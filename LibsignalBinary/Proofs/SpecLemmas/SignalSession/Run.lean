/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Proofs.SpecLemmas.FsFold
import all Init.Data.Repr
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RecordCodecs.Proto
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.SignalSession.SmDir
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Path Loadability, Non-Vacuity, and `fsView` Lemmas for CLI Runs

**Checked by Lean.**

- Proves that all file and directory paths constructed by `smInputs`, `pqInitInputs`,
  `pqSendInputs`, and `pqRecvInputs` satisfy `LoadablePath` (no leading `/` or `..`
  segments).
- Establishes satisfiability of `CliRejectsMalformedCommandLine`'s premises across general,
  SM, and PQ directory layouts, and proves that `fsView (initFsState ...)` depends only on
  the input file list.
-/

namespace CryptoVerification.SignalSession

open Arm64 CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

private theorem digitChar_ne_dot : ∀ d : Nat, Nat.digitChar d ≠ '.'
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => by decide
  | _ + 16 => by simp [Nat.digitChar]

private theorem count_dot_toDigitsCore (base : Nat) :
    ∀ (fuel n : Nat) (ds : List Char),
      (Nat.toDigitsCore base fuel n ds).count '.' = ds.count '.'
  | 0, _, ds => rfl
  | fuel + 1, n, ds => by
    unfold Nat.toDigitsCore
    dsimp only
    by_cases h0 : n / base = 0
    · simp [h0, digitChar_ne_dot]
    · simp only [h0, ↓reduceIte]
      rw [count_dot_toDigitsCore base fuel]
      simp [digitChar_ne_dot]

/-- Decimal representations `toString n` contain no `'.'` characters. -/
theorem count_dot_toString (n : Nat) : (toString n).toList.count '.' = 0 := by
  change (Nat.repr n).toList.count '.' = 0
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList, count_dot_toDigitsCore]
  rfl

private theorem splitSlash_go_cons_ne {c : Char} (cur cs : List Char) (hc : c ≠ '/') :
    Arm64.splitSlash.go cur (c :: cs) = Arm64.splitSlash.go (c :: cur) cs := by
  conv_lhs => unfold Arm64.splitSlash.go
  split
  · contradiction
  · rename_i cs' heq
    injection heq with hc' _
    exact absurd hc' hc
  · rename_i c' cs' _ heq
    injection heq with h1 h2
    subst h1 h2
    rfl

private theorem splitSlash_go_dot_le :
    ∀ (cs cur : List Char) {seg : String},
      seg ∈ Arm64.splitSlash.go cur cs →
        seg.toList.count '.' ≤ cur.count '.' + cs.count '.'
  | [], cur, seg, hmem => by
    have hgo : Arm64.splitSlash.go cur [] = [String.ofList cur.reverse] := rfl
    rw [hgo, List.mem_singleton] at hmem
    subst hmem
    rw [String.toList_ofList, List.count_reverse]
    omega
  | c :: cs, cur, seg, hmem => by
    by_cases hc : c = '/'
    · subst hc
      have hgo : Arm64.splitSlash.go cur ('/' :: cs) =
          String.ofList cur.reverse :: Arm64.splitSlash.go [] cs := rfl
      rw [hgo, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rw [String.toList_ofList, List.count_reverse]
        simp
      · have ih := splitSlash_go_dot_le cs [] hmem
        simp only [List.count_nil, Nat.zero_add] at ih
        have hslash : ('/' :: cs).count '.' = cs.count '.' := by simp
        omega
    · rw [splitSlash_go_cons_ne cur cs hc] at hmem
      have ih := splitSlash_go_dot_le cs (c :: cur) hmem
      by_cases hdot : c = '.'
      · subst hdot
        simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at ih ⊢
        omega
      · have hbeq : (c == '.') = false := beq_eq_false_iff_ne.mpr hdot
        simp only [List.count_cons, hbeq, Bool.false_eq_true, ↓reduceIte] at ih ⊢
        omega

private theorem hasDotDot_false_of_count {p : String} (h : p.toList.count '.' ≤ 1) :
    Arm64.hasDotDot p = false := by
  unfold Arm64.hasDotDot
  by_contra htrue
  simp only [Bool.not_eq_false, List.contains_iff_mem] at htrue
  have hle := splitSlash_go_dot_le p.toList [] htrue
  have htwo : "..".toList.count '.' = 2 := by decide
  simp only [List.count_nil, Nat.zero_add, htwo] at hle
  omega

private theorem loadablePath_of_bool {p : String}
    (h : (Arm64.hasLeadingSlash p || Arm64.hasDotDot p) = false) : LoadablePath p := by
  simp only [Bool.or_eq_false_iff] at h
  exact h

private theorem loadablePath_prefix_nat_suffix (pref suf : String) (n : Nat)
    (hlead : Arm64.hasLeadingSlash pref = false)
    (hne : pref.isEmpty = false)
    (hdots : decide (pref.toList.count '.' + suf.toList.count '.' ≤ 1) = true) :
    LoadablePath (pref ++ toString n ++ suf) := by
  have hd : pref.toList.count '.' + suf.toList.count '.' ≤ 1 := of_decide_eq_true hdots
  refine ⟨?_, hasDotDot_false_of_count ?_⟩
  · unfold Arm64.hasLeadingSlash at hlead ⊢
    rw [String.toList_append, String.toList_append]
    cases hp : pref.toList with
    | nil =>
      have : pref.isEmpty = true := String.isEmpty_iff.mpr (String.ext_iff.mpr hp)
      rw [this] at hne
      contradiction
    | cons c cs =>
      simp only [hp, List.head?_cons] at hlead
      simpa [List.cons_append] using hlead
  · rw [String.toList_append, String.toList_append, List.count_append, List.count_append,
      count_dot_toString]
    omega

private theorem loadablePath_prefix_nat (pref : String) (n : Nat)
    (hlead : Arm64.hasLeadingSlash pref = false)
    (hne : pref.isEmpty = false)
    (hdots : decide (pref.toList.count '.' ≤ 1) = true) :
    LoadablePath (pref ++ toString n) := by
  have h := loadablePath_prefix_nat_suffix pref "" n hlead hne (by
    simpa [List.count_nil] using hdots)
  simpa [String.append_empty] using h

private theorem loadable_partyDirs : ∀ d ∈ partyDirs, LoadablePath d := by
  intro d hd
  simp only [partyDirs, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact loadablePath_of_bool (by decide)

private theorem loadable_bundleDir : LoadablePath bundleDir :=
  loadablePath_of_bool (by decide)

private theorem loadable_publicBundle_files (b : PreKeyBundleFields) :
    ∀ f ∈ (publicBundleOf b).files bundleDir, LoadablePath f.1 := by
  intro f hf
  have hp : f.1 ∈ ((publicBundleOf b).files bundleDir).map Prod.fst := List.mem_map_of_mem hf
  generalize f.1 = p at hp ⊢
  clear f hf
  simp only [PublicBundle.files, publicBundleOf, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl) | hp
  · exact loadablePath_of_bool (by decide)
  · exact loadablePath_of_bool (by decide)
  · exact loadablePath_of_bool (by decide)
  · exact loadablePath_of_bool (by decide)
  · cases hopk : b.opk
    · simp only [hopk, Option.map, List.map_nil, List.not_mem_nil] at hp
    · simp only [hopk, Option.map, List.map_cons, List.map_nil, List.mem_singleton] at hp
      subst hp
      exact loadablePath_of_bool (by decide)

private theorem loadable_encodeDir (W : PEParams) (st : PqParty) :
    ∀ f ∈ encodeDir W st, LoadablePath f.1 := by
  intro f hf
  have hp : f.1 ∈ (encodeDir W st).map Prod.fst := List.mem_map_of_mem hf
  generalize f.1 = p at hp ⊢
  clear f hf
  simp only [encodeDir, List.map_append, List.map_cons, List.map_nil, List.map_flatten,
    List.map_map, Function.comp_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_flatten] at hp
  rcases hp with (((((((rfl | rfl | rfl) | hpeer) | hsess) | hspk) | hopk) | hkpk) | hlr)
  · exact loadablePath_of_bool (by decide)
  · exact loadablePath_of_bool (by decide)
  · exact loadablePath_of_bool (by decide)
  · cases hpeer' : st.peerId
    · simp only [hpeer', List.not_mem_nil] at hpeer
      rcases hpeer with ⟨_, ⟨⟨⟩, _⟩⟩
    · simp only [hpeer', List.mem_singleton] at hpeer
      rcases hpeer with ⟨a, ha, rfl⟩
      rw [congrArg Prod.fst ha]
      dsimp only
      cases st.party.other <;> exact loadablePath_of_bool (by decide)
  · cases hsess' : st.session
    · simp only [hsess', List.not_mem_nil] at hsess
      rcases hsess with ⟨_, ⟨⟨⟩, _⟩⟩
    · simp only [hsess', List.mem_singleton] at hsess
      rcases hsess with ⟨a, ha, rfl⟩
      rw [congrArg Prod.fst ha]
      dsimp only
      cases st.party.other <;> exact loadablePath_of_bool (by decide)
  · rcases hspk with ⟨x, _, rfl⟩
    exact loadablePath_prefix_nat "signed-pre-keys/" x.1.toNat
      (by decide) (by decide) (by decide)
  · rcases hopk with ⟨x, _, rfl⟩
    exact loadablePath_prefix_nat "one-time-pre-keys/" x.1.toNat
      (by decide) (by decide) (by decide)
  · rcases hkpk with ⟨x, _, rfl⟩
    exact loadablePath_prefix_nat "one-time-kyber-pre-keys/" x.1.toNat
      (by decide) (by decide) (by decide)
  · rcases hlr with ⟨l, ⟨x, _, rfl⟩, hfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfl
    rcases hfl with rfl | rfl
    · exact loadablePath_prefix_nat "last-resort-kyber-pre-keys/" x.1.toNat
        (by decide) (by decide) (by decide)
    · exact loadablePath_prefix_nat_suffix "last-resort-kyber-pre-keys/" ".base-keys" x.1.toNat
        (by decide) (by decide) (by decide)

/-- All directory and file paths of `pqInitInputs` satisfy `LoadablePath`. -/
theorem loadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    (∀ d ∈ (pqInitInputs W st b t).dirs, LoadablePath d) ∧
    (∀ f ∈ (pqInitInputs W st b t).files, LoadablePath f.1) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact loadable_partyDirs d hd
    · exact loadable_bundleDir
  · intro f hf
    simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hf
    rcases hf with (hf | hf) | rfl
    · exact loadable_encodeDir W st f hf
    · exact loadable_publicBundle_files b f hf
    · change LoadablePath coinsFile
      exact loadablePath_of_bool (by decide)

/-- All directory and file paths of `pqSendInputs` satisfy `LoadablePath`. -/
theorem loadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    (∀ d ∈ (pqSendInputs W st m r).dirs, LoadablePath d) ∧
    (∀ f ∈ (pqSendInputs W st m r).files, LoadablePath f.1) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [pqSendInputs, pqInputs, List.append_nil] at hd
    exact loadable_partyDirs d hd
  · intro f hf
    simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact loadable_encodeDir W st f hf
    · change LoadablePath coinsFile
      exact loadablePath_of_bool (by decide)

/-- All directory and file paths of `pqRecvInputs` satisfy `LoadablePath`. -/
theorem loadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    (∀ d ∈ (pqRecvInputs W st c rc).dirs, LoadablePath d) ∧
    (∀ f ∈ (pqRecvInputs W st c rc).files, LoadablePath f.1) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [pqRecvInputs, pqInputs, List.append_nil] at hd
    exact loadable_partyDirs d hd
  · intro f hf
    simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact loadable_encodeDir W st f hf
    · change LoadablePath coinsFile
      exact loadablePath_of_bool (by decide)

/-! ## Additional Path Loadability Witnesses -/

section MoveCompat
private theorem loadable_addressFile : LoadablePath addressFile :=
  loadablePath_of_bool (by decide)

private theorem loadable_identityFile (P : Party) : LoadablePath (identityFile (partyAddressName P)) := by
  cases P <;> exact loadablePath_of_bool (by decide)

private theorem loadable_sessionFile (P : Party) : LoadablePath (sessionFile (partyAddress P)) := by
  cases P <;> exact loadablePath_of_bool (by decide)

theorem loadable_coinsFile : LoadablePath coinsFile :=
  loadablePath_of_bool (by decide)

theorem loadable_dirOfE (P : Party) (rec : List (BitVec 8)) :
    ∀ f ∈ dirOfE P rec, LoadablePath f.1 := by
  intro f hf
  simp only [dirOfE, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h <;> subst h
  · exact loadable_addressFile
  · exact loadable_identityFile _
  · exact loadable_sessionFile _

theorem loadable_smInputs (g : GhostState Bytes) (cmd : Cmd) (coins stdin : List (BitVec 8)) :
    (∀ d ∈ (smInputs g cmd coins stdin).dirs, LoadablePath d) ∧
    (∀ f ∈ (smInputs g cmd coins stdin).files, LoadablePath f.1) := by
  refine ⟨loadable_partyDirs, ?_⟩
  intro f hf
  simp only [smInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h
  · exact loadable_dirOfE _ _ f h
  · subst h; exact loadable_coinsFile

theorem NoFiles.sameFiles {a b : FsState} (ha : NoFiles a) (hb : NoFiles b) : SameFiles a b :=
  fun q => by rw [ha q, hb q]

private theorem NoFiles.foldl_dir {a : FsState} (h : NoFiles a) (l : List FsPath) :
    NoFiles (l.foldl (fun acc pref => acc.setEntry pref (some .dir)) a) := by
  induction l generalizing a with
  | nil => exact h
  | cons x xs ih =>
    apply ih
    intro q
    simp only [FsState.setEntry]
    split
    · rfl
    · exact h q

theorem NoFiles.dirsFold_none (dirs : List String) : NoFiles (dirsFold dirs {}) := by
  suffices ∀ a : FsState, NoFiles a → NoFiles (dirsFold dirs a) from
    this _ NoFiles.base
  induction dirs with
  | nil => intro a h; exact h
  | cons d ds ih => intro a h; exact ih _ (h.foldl_dir _)

theorem fsView_initFsState (i : Process.ProcessInputs) :
    fsView (Process.initFsState i) = filesOf i.files := by
  funext p
  unfold filesOf fsView
  split
  · rfl
  · rename_i hp
    show fileOfEntry ((Process.initFsState i).files p) =
      fileOfEntry ((Process.initFsState { files := i.files }).files p)
    simp only [FsState.files, FsState.getEntry]
    split
    · rfl
    · rw [initFsState_entries i _ hp, initFsState_entries { files := i.files } _ hp]
      exact (SameFiles.filesFold_same
        (NoFiles.sameFiles (NoFiles.dirsFold_none i.dirs) (NoFiles.dirsFold_none [])) i.files) _

end MoveCompat

end CryptoVerification.SignalSession
