/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.BundleGeneralParse
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.FilesExtParity
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.InitPaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Two-Placement Bundle-Initialization ELF Parity Bridges

Relocatable two-placement (`mpl`, `mmpl : Obj.MultiPlacement`) parity bridges for flat-bundle `init`
over `cliRunPlacedSig mpl mmpl elf W` and `CliReachesOOMPlaced mpl mmpl elf W`, covering valid
bundle initialization, malformed-bundle rejection, and `read_file` cap overflow.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3

open Arm64 (
  FsEntry FsPath FsState GhostName MAX_LFS_FILESIZE Memory hasDotDot hasLeadingSlash normalizePath
  subroutine_ok
)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage ProcessInputs bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.E2E (
  PEParams PreKeyBundleFields UnreachedPqxdhPrimitives djbKey encodeRecordUnderExtras
  initiateState initiateTapeLen kyberKey partyAddressName partyIdentityKey seedRecordExtras
  spqrOffSessionParams
)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession (
  Address ArgvFitsInitialStack CliHooks CliReachesOOMPlaced Cmd Inputs Outcome OutcomeOrExcusedAbort
  PqParty PqxdhPartyInSpecDomain PrintableAsciiArg PublicBundle ancestors baseKeysFile bundleDir
  cliExternsPlaced cliProcessInputs coinsFile dirsFold encodeDir fileCapBytes filesFold filesOf
  files_eq_entries fsView identityFile initFsState_entries le32 observe partyAddress pathComps
  pqInitInputs pqInitModel pqInputs pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes
  stdioPaths
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli (
  CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainResult
  RunAnswer StoresGhost WriteOk addressText cliInputs decimalText ofLe32 pathOf splitId splitSigned
  utf8 writeOk_pqInitInputs
)
open CryptoVerification.SignalSession.Cli.MainHops (
  DirWrOk StoresWrOk blockingAncestorF cliIo cliRd coinsOf namedWrites_ascii pathStr readViewF
  saveUpd_own
)
open CryptoVerification.SignalSession.Cli.RunCompose (
  BundleV RunBounds RunFilesOk RunHsOk RunSem bundleNames finish readBundleV readU32LE runAns
  runFiles runRel
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  InitOk₀ bundleEOf? initDef
)
open CryptoVerification.SignalSession.Cli.RunProofs.InitS0 (
  pqInitiateAgrees_initDef_proof utf8_eq_flatMap
)
open CryptoVerification.SignalSession.Cli.RunRefine (
  addrParse_textBytes addrValE bundleVE ownAddr_pqInit parseArgs_init runAns_pqInit runAns_pqInit_eq
  runBounds_pqInit
)
open CryptoVerification.SignalSession.Cli.Slots (
  distinctSid_party filesOk₀ filesOkPeer_pqInit partyAddr pqSessBytes runFilesOk_of_peer
)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  BundleFilesFlatRaw pqInitInputsFRaw
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions b2MainSpecTightNeedLocksFineAt cliBudgetLimits
  cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs cliRunPlacedSig_eq_on_input_of_progEq2
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (
  outcomeOrExcusedAbort_of_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (
  BundleReadWithinCap InputsEquivRaw NonBundleCoinsStdio bundleVE_injective fileStep_entries
  filesFold_entries_eq_or filesFold_eq_foldl_fileStep filesOf_append_writes_eq_of_nonBundleCoins
  filesOf_publicBundle_files initDef_eq_of_nonBundleCoins initFsState_entries_eq_of_filesOf_eq
  initOk₀_and_initDef_of_nonBundleCoins mem_dropLast_nonEmptyPrefixes_iff nonBundleCoinsStdio_upward
  normDjbKey normKyberKey normalizePath_head_slash parseBundleDir publicBundleOf_injective
  readBundleV_runFiles_eq_none_of_not_withinCap readBundleV_runFiles_eq_none_of_parseBundleDir_eq_none
  readBundleV_runFiles_eq_some_iff_bundleE runFiles_eq_of_nonBundleCoins segCanon_of_mem_normalizePath
)

private theorem ite_pos_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_f3 {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

theorem inputsEquivRaw_refl (i : Inputs) : InputsEquivRaw i i :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-! ## `PublicBundle` Round-Trip and Path-Head Partitioning -/

private theorem ofLe32_extract_raw (v : BitVec 32) :
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
    congr 1
    omega
  · have hb : decide (i - 8 - 8 < 8) = true := decide_eq_true h3
    rw [hb, Bool.true_and]
    congr 1
    omega
  · have h4 : i - 8 - 8 - 8 < 8 := by omega
    have hb : decide (i - 8 - 8 - 8 < 8) = true := decide_eq_true h4
    rw [hb, Bool.true_and]
    congr 1
    omega

private theorem readU32LE_le32_raw (v : BitVec 32) :
    readU32LE (le32 v) = some v := by
  simp only [le32, readU32LE, ofLe32_extract_raw]

private theorem splitId_le32_raw (id : BitVec 32) (key : List (BitVec 8)) :
    splitId (le32 id ++ key) = some (id, key) := by
  simp only [le32, List.cons_append, List.nil_append, splitId, ofLe32_extract_raw]

private theorem splitSigned_le32_raw (id : BitVec 32) (key sig : List (BitVec 8))
    (hs : sig.length = 64) :
    splitSigned (le32 id ++ key ++ sig) = some (id, key, sig) := by
  rw [List.append_assoc, splitSigned, splitId_le32_raw]
  simp only [List.length_append, hs, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
    List.take_left', List.drop_left']

private theorem normDjbKey_djbKey (k : List.Vector (BitVec 8) 32) :
    normDjbKey (djbKey k) = some (djbKey k) := by
  rcases k with ⟨l, hl⟩
  simp [djbKey, normDjbKey, hl, List.take_of_length_le (Nat.le_of_eq hl)]

private theorem normKyberKey_kyberKey (k : List.Vector (BitVec 8) 1568) :
    normKyberKey (kyberKey k) = some (kyberKey k) := by
  rcases k with ⟨l, hl⟩
  simp [kyberKey, normKyberKey, hl]

theorem bundleFilesFlatRaw_publicBundleOf (b : PreKeyBundleFields) :
    BundleFilesFlatRaw ((publicBundleOf b).files bundleDir) := by
  intro f hf
  simp only [publicBundleOf, PublicBundle.files, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | hot_mem
  · refine ⟨⟨"identity-key", by dsimp only; decide⟩, ?_⟩
    dsimp only [djbKey]
    simp only [List.length_cons, List.Vector.toList_length]
    decide
  · refine ⟨⟨"registration-id", by dsimp only; decide⟩, ?_⟩
    dsimp only [le32]
    simp only [List.length_cons, List.length_nil]
    decide
  · refine ⟨⟨"signed-pre-key", by dsimp only; decide⟩, ?_⟩
    dsimp only [le32, djbKey]
    simp only [List.length_append, List.length_cons, List.length_nil, List.Vector.toList_length]
    decide
  · refine ⟨⟨"kyber-pre-key", by dsimp only; decide⟩, ?_⟩
    dsimp only [le32, kyberKey]
    simp only [List.length_append, List.length_cons, List.length_nil, List.Vector.toList_length]
    decide
  · rcases hopk : b.opk with _ | ⟨oid, okey⟩
    · simp [hopk] at hot_mem
    · simp only [hopk, Option.map_some, List.mem_singleton] at hot_mem
      subst hot_mem
      refine ⟨⟨"one-time-pre-key", by dsimp only; decide⟩, ?_⟩
      dsimp only [le32, djbKey]
      simp only [List.length_append, List.length_cons, List.length_nil, List.Vector.toList_length]
      decide

theorem parseBundleDir_publicBundleOf (b : PreKeyBundleFields) :
    parseBundleDir (filesOf ((publicBundleOf b).files bundleDir)) bundleDir =
      some (publicBundleOf b) := by
  obtain ⟨f_ik, f_reg, f_spk, f_kpk, f_opk⟩ := filesOf_publicBundle_files (publicBundleOf b)
  unfold parseBundleDir
  dsimp only [bind, Option.bind]
  simp only [f_ik, f_reg, f_spk, f_kpk, f_opk, Option.getD_some]
  clear f_ik f_reg f_spk f_kpk f_opk
  dsimp only [publicBundleOf]
  simp only [normDjbKey_djbKey, readU32LE_le32_raw,
    splitSigned_le32_raw _ _ _ b.spkSig.toList_length,
    splitSigned_le32_raw _ _ _ b.kpkSig.toList_length, normKyberKey_kyberKey]
  rcases b with ⟨_, _ | ⟨oid, okey⟩, _, _, _, _, _, _, _⟩
  · rfl
  · dsimp only [Option.map, Option.getD]
    have hne : (le32 oid ++ djbKey okey).isEmpty = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, splitId_le32_raw, normDjbKey_djbKey]

private theorem head_ne_bc_of_prefix (seg rest : String) (hns : '/' ∉ seg.toList)
    (hok : (!seg.isEmpty && seg != ".") = true)
    (h1 : some seg ≠ some bundleDir) (h2 : some seg ≠ some coinsFile) :
    (normalizePath ((seg ++ "/") ++ rest)).head? ≠ some bundleDir ∧
      (normalizePath ((seg ++ "/") ++ rest)).head? ≠ some coinsFile := by
  rw [normalizePath_head_slash seg rest hns hok]
  exact ⟨h1, h2⟩

private theorem encodeDir_head_ne_bundle_coins (P : PEParams) (st : PqParty)
    {x : String × List (BitVec 8)} (hx : x ∈ encodeDir P st) :
    (normalizePath x.1).head? ≠ some bundleDir ∧ (normalizePath x.1).head? ≠ some coinsFile := by
  unfold encodeDir at hx
  simp only [List.mem_append] at hx
  rcases hx with ((((((hpre | hpeer) | hsess) | hsigned) | hot) | hkot) | hklr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpre
    rcases hpre with rfl | rfl | rfl <;> (dsimp only; exact ⟨by decide, by decide⟩)
  · cases hp : st.peerId <;> simp only [hp, List.not_mem_nil, List.mem_singleton] at hpeer
    subst hpeer
    exact head_ne_bc_of_prefix "identities" _ (by decide) (by decide) (by decide) (by decide)
  · rcases hs : st.session with _ | ⟨_, _⟩ <;> simp only [hs, List.not_mem_nil, List.mem_singleton] at hsess
    subst hsess
    exact head_ne_bc_of_prefix "sessions" _ (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hsigned
    exact head_ne_bc_of_prefix "signed-pre-keys" _ (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hot
    exact head_ne_bc_of_prefix "one-time-pre-keys" _ (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨⟨_, _⟩, _, rfl⟩ := List.mem_map.mp hkot
    exact head_ne_bc_of_prefix "one-time-kyber-pre-keys" _ (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨_, hl, hp⟩ := List.mem_flatten.mp hklr
    obtain ⟨⟨_, _, _⟩, _, rfl⟩ := List.mem_map.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact head_ne_bc_of_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide) (by decide) (by decide)
    · dsimp only
      unfold baseKeysFile
      rw [String.append_assoc]
      exact head_ne_bc_of_prefix "last-resort-kyber-pre-keys" _ (by decide) (by decide) (by decide) (by decide)

private theorem bundleFilesFlat_directChild {files : List (String × List (BitVec 8))}
    (hb : BundleFilesFlatRaw files) :
    ∀ e ∈ files, ∃ name, name ≠ "" ∧ normalizePath e.1 = ["bundle", name] := by
  intro e he
  obtain ⟨⟨name, hnorm⟩, _⟩ := hb e he
  have hcan := segCanon_of_mem_normalizePath
    (hnorm ▸ List.mem_cons_of_mem _ (List.mem_singleton_self name))
  exact ⟨name, fun h => by subst h; exact absurd hcan.1 (by decide), hnorm⟩

private theorem filesFold_entries_of_head_ne (l : List (String × List (BitVec 8))) (fs : FsState)
    {q : FsPath} (h : ∀ x ∈ l, (normalizePath x.1).head? ≠ q.head?) :
    (filesFold l fs).entries q = fs.entries q := by
  rw [filesFold_eq_foldl_fileStep]
  induction l generalizing fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩
    rw [List.foldl_cons, ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy)), fileStep_entries]
    have hp := h (p, bs) (List.mem_cons_self ..)
    have hneq : q ≠ normalizePath p := fun heq => hp (heq ▸ rfl)
    have hnanc : q ∉ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast := by
      intro hm
      obtain ⟨hqne, ⟨tl, htl⟩, _⟩ := mem_dropLast_nonEmptyPrefixes_iff.mp hm
      cases q with
      | nil => exact hqne rfl
      | cons c qs => exact hp (by rw [← htl, List.cons_append, List.head?_cons, List.head?_cons])
    simp [hneq, hnanc]

private theorem emptyFsState_entries_ne_nil {q : FsPath} (hq : q ≠ []) :
    ({} : FsState).entries q = none := by
  show (if q.isEmpty then some FsEntry.dir else none) = none
  rw [List.isEmpty_eq_false_iff.mpr hq]
  rfl

private theorem filesOf_eq_none_of_nil_or_stdio (f : List (String × List (BitVec 8))) {p : String}
    (h : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath) :
    filesOf f p = none := by
  unfold filesOf fsView
  by_cases hns : normalizePath p ∈ stdioPaths.map normalizePath
  · rw [ite_pos_f3 hns]
  · rw [ite_neg_f3 hns]
    rcases h with hnil | hst <;> [rw [files_eq_entries, hnil]; exact absurd hst hns]
    rfl

private theorem filesOf_eq_match_filesFold_f3 (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_f3 hns, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_eq_none_of_head_ne (f : List (String × List (BitVec 8))) {p : String}
    (h : ∀ x ∈ f, (normalizePath x.1).head? ≠ (normalizePath p).head?) :
    filesOf f p = none := by
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · exact filesOf_eq_none_of_nil_or_stdio f hbad
  · push Not at hbad
    rw [filesOf_eq_match_filesFold_f3 f hbad.1 hbad.2, filesFold_entries_of_head_ne f {} h,
      emptyFsState_entries_ne_nil hbad.1]

private theorem filesOf_append_of_head_ne (f₁ f₂ : List (String × List (BitVec 8))) {p : String}
    (h : ∀ x ∈ f₂, (normalizePath x.1).head? ≠ (normalizePath p).head?) :
    filesOf (f₁ ++ f₂) p = filesOf f₁ p := by
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · rw [filesOf_eq_none_of_nil_or_stdio _ hbad, filesOf_eq_none_of_nil_or_stdio _ hbad]
  · push Not at hbad
    rw [filesOf_eq_match_filesFold_f3 _ hbad.1 hbad.2, filesOf_eq_match_filesFold_f3 _ hbad.1 hbad.2,
      show filesFold (f₁ ++ f₂) {} = filesFold f₂ (filesFold f₁ {}) from List.foldl_append,
      filesFold_entries_of_head_ne f₂ _ h]

private theorem filesOf_prepend_of_head_ne (f₁ f₂ : List (String × List (BitVec 8))) {p : String}
    (h : ∀ x ∈ f₁, (normalizePath x.1).head? ≠ (normalizePath p).head?) :
    filesOf (f₁ ++ f₂) p = filesOf f₂ p := by
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · rw [filesOf_eq_none_of_nil_or_stdio _ hbad, filesOf_eq_none_of_nil_or_stdio _ hbad]
  · push Not at hbad
    rw [filesOf_eq_match_filesFold_f3 _ hbad.1 hbad.2, filesOf_eq_match_filesFold_f3 _ hbad.1 hbad.2,
      show filesFold (f₁ ++ f₂) {} = filesFold f₂ (filesFold f₁ {}) from List.foldl_append,
      filesFold_entries_eq_or f₂ _ hbad.1, filesFold_entries_of_head_ne f₁ {} h,
      emptyFsState_entries_ne_nil hbad.1, Option.or_none]

private theorem tail_head_bundle_or_coins {files : List (String × List (BitVec 8))}
    {coins : List (BitVec 8)} (hb : BundleFilesFlatRaw files)
    {x : String × List (BitVec 8)} (hx : x ∈ files ++ [(coinsFile, coins)]) :
    (normalizePath x.1).head? = some bundleDir ∨ (normalizePath x.1).head? = some coinsFile := by
  rcases List.mem_append.mp hx with hf | hc
  · obtain ⟨⟨_, hnorm⟩, _⟩ := hb x hf
    rw [hnorm, List.head?_cons]
    exact .inl rfl
  · rw [List.mem_singleton] at hc
    subst hc
    dsimp only
    exact .inr (by decide)

private theorem filesOf_pqInitInputsF_nonBundleCoins {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) {p : String} (hp : NonBundleCoinsStdio (normalizePath p)) :
    filesOf i.files p = filesOf (encodeDir P st) p := by
  rw [heq.2.2.2 p, show (pqInitInputsFRaw P st files t).files =
      encodeDir P st ++ (files ++ [(coinsFile, t.toList)]) by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc]]
  refine filesOf_append_of_head_ne _ _ fun x hx hhead => ?_
  rcases tail_head_bundle_or_coins hb hx with h1 | h2
  exacts [hp.2.1 (hhead.symm.trans h1), hp.2.2.1 (hhead.symm.trans h2)]

private theorem filesOf_pqInitInputsF_or {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) (p : String) :
    filesOf i.files p = (filesOf (files ++ [("coins", t.toList)]) p).or (filesOf (encodeDir P st) p) := by
  rw [heq.2.2.2 p, show (pqInitInputsFRaw P st files t).files =
      encodeDir P st ++ (files ++ [("coins", t.toList)]) by
        simp [pqInitInputsFRaw, pqInputs, coinsFile, List.append_assoc]]
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · rw [filesOf_eq_none_of_nil_or_stdio _ hbad, filesOf_eq_none_of_nil_or_stdio _ hbad,
      filesOf_eq_none_of_nil_or_stdio _ hbad]
    rfl
  · push Not at hbad
    by_cases hbc : (normalizePath p).head? = some bundleDir ∨ (normalizePath p).head? = some coinsFile
    · have hne : ∀ x ∈ encodeDir P st, (normalizePath x.1).head? ≠ (normalizePath p).head? :=
        fun x hx he => hbc.elim (fun h1 => (encodeDir_head_ne_bundle_coins P st hx).1 (he.trans h1))
          (fun h2 => (encodeDir_head_ne_bundle_coins P st hx).2 (he.trans h2))
      rw [filesOf_prepend_of_head_ne _ _ hne, filesOf_eq_none_of_head_ne _ hne, Option.or_none]
    · push Not at hbc
      have hne : ∀ x ∈ files ++ [("coins", t.toList)],
          (normalizePath x.1).head? ≠ (normalizePath p).head? :=
        fun x hx he => (tail_head_bundle_or_coins hb hx).elim (fun h1 => hbc.1 (he.symm.trans h1))
          (fun h2 => hbc.2 (he.symm.trans h2))
      rw [filesOf_append_of_head_ne _ _ hne, filesOf_eq_none_of_head_ne _ hne, Option.none_or]

theorem bundleReadWithinCap_publicBundleOf (b : PreKeyBundleFields) :
    BundleReadWithinCap (filesOf ((publicBundleOf b).files bundleDir)) bundleDir := by
  obtain ⟨hik, hreg, hspk, hkpk, hopk⟩ := filesOf_publicBundle_files (publicBundleOf b)
  intro name hname
  simp only [bundleNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · rw [hik]
    dsimp only [Option.getD, publicBundleOf, djbKey]
    simp [List.Vector.toList_length, fileCapBytes]
  · rw [hreg]
    dsimp only [Option.getD, publicBundleOf, le32]
    simp [fileCapBytes]
  · rw [hspk]
    dsimp only [Option.getD, publicBundleOf, djbKey, le32]
    simp [List.Vector.toList_length, fileCapBytes]
  · rw [hkpk]
    dsimp only [Option.getD, publicBundleOf, kyberKey, le32]
    simp [List.Vector.toList_length, fileCapBytes]
  · rw [hopk]
    dsimp only [publicBundleOf]
    cases b.opk with
    | none => decide
    | some p =>
      rcases p with ⟨_, _⟩
      dsimp only [Option.map, Option.getD, djbKey, le32]
      simp [List.Vector.toList_length, fileCapBytes]

theorem readBundleV_iff_parseBundleDir_of_inputsEquivRaw {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (_hwf : PqxdhPartyInSpecDomain P st) (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir) :
    (readBundleV (runFiles i) (bytesOfString bundleDir) 1#8 = none ↔
      parseBundleDir (filesOf files) bundleDir = none) ∧
    (∀ b : PreKeyBundleFields, readBundleV (runFiles i) (bytesOfString bundleDir) 1#8 =
      some (bundleVE b) ↔ parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) := by
  have hd_scrub : ∀ p, (normalizePath p).head? = some "bundle" → filesOf (encodeDir P st) p = none :=
    fun _ hp => filesOf_eq_none_of_head_ne _ fun _ hx he =>
      (encodeDir_head_ne_bundle_coins P st hx).1 (he.trans hp)
  have ⟨hnone, hsome1, hsome2⟩ := readBundleV_runFiles_eq_some_iff_bundleE heq.2.1
    (bundleFilesFlat_directChild hb) hd_scrub (fun p _ => filesOf_pqInitInputsF_or heq hb p) hcap
  refine ⟨hnone, fun b => ⟨fun hr => ?_, fun hp => ?_⟩⟩
  · obtain ⟨_, ⟨hbv, _, hpb⟩, _⟩ := hsome1 _ hr
    exact bundleVE_injective hbv ▸ hpb
  · obtain ⟨_, hpb, hr, _, _⟩ := hsome2 _ hp
    exact publicBundleOf_injective hpb ▸ hr

theorem readBundleV_eq_none_of_parseBundleDir_of_inputsEquivRaw {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (_hwf : PqxdhPartyInSpecDomain P st) (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    readBundleV (runFiles i) (bytesOfString bundleDir) 1#8 = none := by
  have hd_scrub : ∀ p, (normalizePath p).head? = some "bundle" → filesOf (encodeDir P st) p = none :=
    fun _ hp => filesOf_eq_none_of_head_ne _ fun _ hx he =>
      (encodeDir_head_ne_bundle_coins P st hx).1 (he.trans hp)
  exact readBundleV_runFiles_eq_none_of_parseBundleDir_eq_none heq.2.1
    (bundleFilesFlat_directChild hb) hd_scrub (fun p _ => filesOf_pqInitInputsF_or heq hb p) hparse

theorem readBundleV_eq_none_of_not_withinCap_of_inputsEquivRaw {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (_hwf : PqxdhPartyInSpecDomain P st) (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    readBundleV (runFiles i) (bytesOfString bundleDir) 1#8 = none := by
  have hd_scrub : ∀ p, (normalizePath p).head? = some "bundle" → filesOf (encodeDir P st) p = none :=
    fun _ hp => filesOf_eq_none_of_head_ne _ fun _ hx he =>
      (encodeDir_head_ne_bundle_coins P st hx).1 (he.trans hp)
  exact readBundleV_runFiles_eq_none_of_not_withinCap heq.2.1
    (bundleFilesFlat_directChild hb) hd_scrub (fun p _ => filesOf_pqInitInputsF_or heq hb p) hover

theorem readBundleV_iff_parseBundleDir_pqInitInputsFRaw (P : PEParams) (st : PqParty)
    (files : List (String × List (BitVec 8))) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hwf : PqxdhPartyInSpecDomain P st) (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir) :
    (readBundleV (runFiles (pqInitInputsFRaw P st files t))
        (bytesOfString bundleDir) 1#8 = none ↔ parseBundleDir (filesOf files) bundleDir = none) ∧
    (∀ b : PreKeyBundleFields, readBundleV (runFiles (pqInitInputsFRaw P st files t))
        (bytesOfString bundleDir) 1#8 = some (bundleVE b) ↔
        parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :=
  readBundleV_iff_parseBundleDir_of_inputsEquivRaw (inputsEquivRaw_refl _) hwf hb hcap

private theorem toString_one_eq : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private theorem partyAddress_text_toList_f3 (P : Party) :
    (partyAddress P).text.toList = (partyAddressName P).toList ++ ".".toList ++ ['1'] := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [partyAddress, Address.text, ht1, hd1, String.toList_append]

private theorem partyAddress_text_printable_f3 (P : Party) :
    PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro h
    have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · intro c hc
    rw [partyAddress_text_toList_f3] at hc
    cases P <;> revert c hc <;> decide

private theorem partyAddress_text_length_f3 (P : Party) :
    (partyAddress P).text.length = 38 := by
  rw [← String.length_toList, partyAddress_text_toList_f3]
  cases P <;> decide

theorem cliInputsOk_pqInitInputsFRaw (P : PEParams) (st : PqParty)
    (files : List (String × List (BitVec 8))) (t : List.Vector (BitVec 8) initiateTapeLen) :
    CliInputsOk (pqInitInputsFRaw P st files t) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqInitInputsFRaw, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable_f3 st.party.other
    · unfold PrintableAsciiArg bundleDir; decide
  · unfold ArgvFitsInitialStack pqInitInputsFRaw pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length_f3, bundleDir]
    decide

theorem cliInputsOk_of_inputsEquivRaw {i i' : Inputs} (heq : InputsEquivRaw i i')
    (hok : CliInputsOk i') : CliInputsOk i := by
  unfold CliInputsOk at hok ⊢
  rwa [heq.1]

/-! ## `InitRunSemOk` and Run-Level `observe` Bridges -/

def InitRunSemOk (S : RunSem) (X : UnreachedPqxdhPrimitives) (WP : PEParams) : Prop :=
  S.initiate = initDef X WP ∧ S.initOk = InitOk₀ WP ∧
  ∃ (Scope : SessionRecord (List (BitVec 8)) → Prop) (extra : FsFiles → Prop),
    S.filesOk = filesOk₀ Scope extra ∧
    (∀ (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
      PqxdhPartyInSpecDomain WP st → st.session = none → extra (runFiles (pqInitInputs WP st b t))) ∧
    (∀ F₁ F₂ : FsFiles, (∀ p : String, NonBundleCoinsStdio (normalizePath p) → F₁ p = F₂ p) →
      extra F₁ → extra F₂)

theorem initRunSemOk_of_filesOk₀ {S : RunSem} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} (hinit : S.initiate = initDef X WP)
    (hfiles : S.filesOk = filesOk₀ Scope (fun _ => True)) (hinitOk : S.initOk = InitOk₀ WP) :
    InitRunSemOk S X WP :=
  ⟨hinit, hinitOk, Scope, fun _ => True, hfiles, fun _ _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩

private def zeroBundleE : PreKeyBundleFields :=
  ⟨0#32, none, 0#32, List.Vector.replicate 32 0#8, List.Vector.replicate 64 0#8,
   0#32, List.Vector.replicate 1568 0#8, List.Vector.replicate 64 0#8, List.Vector.replicate 32 0#8⟩

private theorem filesOf_append_eq_of_filesOf_eq_not_bc {f₁ f₂ ws : List (String × List (BitVec 8))}
    (hf : ∀ p, filesOf f₁ p = filesOf f₂ p)
    (hws : ∀ w ∈ ws, (normalizePath w.1).head? ≠ some bundleDir ∧
      (normalizePath w.1).head? ≠ some coinsFile) : filesOf (f₁ ++ ws) = filesOf (f₂ ++ ws) := by
  funext p
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · rw [filesOf_eq_none_of_nil_or_stdio _ hbad, filesOf_eq_none_of_nil_or_stdio _ hbad]
  · push Not at hbad
    by_cases hbc : (normalizePath p).head? = some bundleDir ∨ (normalizePath p).head? = some coinsFile
    · have hne : ∀ w ∈ ws, (normalizePath w.1).head? ≠ (normalizePath p).head? :=
        fun w hw he => hbc.elim (fun hb' => (hws w hw).1 (he.trans hb'))
          (fun hc' => (hws w hw).2 (he.trans hc'))
      rw [filesOf_append_of_head_ne _ _ hne, filesOf_append_of_head_ne _ _ hne, hf p]
    · push Not at hbc
      exact filesOf_append_writes_eq_of_nonBundleCoins (fun q _ => hf q) p
        ⟨hbad.1, hbc.1, hbc.2, hbad.2⟩

private theorem filesOf_pqInitInputsF_coins_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    filesOf i.files coinsFile = some t.toList := by
  rw [heq.2.2.2 coinsFile]
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns,
    show (pqInitInputsFRaw P st files t).files =
      (encodeDir P st ++ files) ++ [(coinsFile, t.toList)] by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc],
    filesFold_eq_foldl_fileStep, List.foldl_append, List.foldl_cons, List.foldl_nil,
    fileStep_entries, ite_pos_f3 rfl]

private theorem coinsOf_of_inputsEquiv_pqInitInputsF {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    coinsOf i = t.toList := by
  unfold coinsOf
  rw [show "coins" = coinsFile from rfl, filesOf_pqInitInputsF_coins_f3 heq]
  rfl

private theorem coinsReadable_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    CoinsReadable i := by
  have hc := filesOf_pqInitInputsF_coins_f3 heq
  have hne : normalizePath coinsFile ≠ [] := by decide
  have hns : normalizePath coinsFile ∉ stdioPaths.map normalizePath := by decide
  rw [filesOf_eq_match_filesFold_f3 _ hne hns] at hc
  have hfold : (filesFold i.files {}).entries (normalizePath coinsFile) =
      some (.file t.toList) := by
    rcases hf : (filesFold i.files {}).entries (normalizePath coinsFile) with _ | bs | _ <;>
      rw [hf] at hc <;>
      [cases hc;
       (dsimp only at hc
        exact congrArg (fun x => some (FsEntry.file x)) (Option.some.inj hc));
       cases hc]
  unfold CoinsReadable
  rw [show "coins" = coinsFile from rfl, files_eq_entries,
    ite_neg_f3 (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries (cliInputs i) (normalizePath coinsFile) hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) ≠
      some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath coinsFile) =
      some (.file bs) → bs.length ≤ fileCapBytes
  rw [filesFold_entries_eq_or i.files _ hne, hfold, Option.some_or]
  refine ⟨fun h => FsEntry.noConfusion (Option.some.inj h), fun bs h => ?_⟩
  injection h with h
  injection h with h
  subst h
  simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes]

private theorem runFiles_and_entries_agree_pqInit {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) (b : PreKeyBundleFields) :
    (∀ p : String, NonBundleCoinsStdio (normalizePath p) →
      runFiles i p = runFiles (pqInitInputs P st b t) p) ∧
    (∀ q : FsPath, NonBundleCoinsStdio q →
      (initFsState (cliInputs i)).entries q = (initFsState (cliInputs (pqInitInputs P st b t))).entries q) := by
  have hag : ∀ p : String, NonBundleCoinsStdio (normalizePath p) →
      filesOf i.files p = filesOf (pqInitInputs P st b t).files p := fun p hp =>
    (filesOf_pqInitInputsF_nonBundleCoins heq hb hp).trans
      (filesOf_pqInitInputsF_nonBundleCoins (inputsEquivRaw_refl _)
        (bundleFilesFlatRaw_publicBundleOf b) hp).symm
  refine ⟨runFiles_eq_of_nonBundleCoins heq.2.1 hag, fun q hq => ?_⟩
  rw [initFsState_entries (cliInputs i) q hq.2.2.2,
    initFsState_entries (cliInputs (pqInitInputs P st b t)) q hq.2.2.2]
  change (filesFold i.files (dirsFold i.dirs {})).entries q =
    (filesFold (pqInitInputs P st b t).files (dirsFold (pqInitInputs P st b t).dirs {})).entries q
  have hent := initFsState_entries_eq_of_filesOf_eq
    (P := NonBundleCoinsStdio) (fun _ h => h.1) (fun _ h => h.2.2.2)
    (fun _ _ h hpre => nonBundleCoinsStdio_upward h hpre) hag q hq
  rw [filesFold_entries_eq_or i.files _ hq.1,
    filesFold_entries_eq_or (pqInitInputs P st b t).files _ hq.1, hent, heq.2.1]
  rfl

private theorem identityFile_eq_f3 (P : Party) :
    identityFile (partyAddressName P) =
      match P with
      | .A => "identities/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"
      | .B => "identities/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6" := by
  cases P <;> exact String.toList_inj.mp (by
    unfold identityFile partyAddressName
    simp only [String.toList_append]
    decide)

private theorem sessionFile_eq_f3 (P : Party) :
    sessionFile (partyAddress P) =
      match P with
      | .A => "sessions/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"
      | .B => "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1" := by
  cases P <;> exact String.toList_inj.mp (by
    unfold sessionFile partyAddress Address.text partyAddressName
    rw [toString_one_eq]
    simp only [String.toList_append]
    decide)

private theorem splitOn_slash_pair (s1 s2 : String)
    (h1 : '/' ∉ s1.toList) (h2 : '/' ∉ s2.toList) :
    (s1 ++ "/" ++ s2).toList.splitOn '/' = [s1.toList, s2.toList] := by
  have heq : (s1 ++ "/" ++ s2).toList = ['/'].intercalate [s1.toList, s2.toList] := by
    simp [String.toList_append, List.intercalate]
  rw [heq, List.splitOn_intercalate]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact h1
    · exact h2
  · exact List.cons_ne_nil _ _

private theorem ancestors_slash_pair (s1 s2 : String)
    (h1 : '/' ∉ s1.toList) (h2 : '/' ∉ s2.toList) :
    ancestors (s1 ++ "/" ++ s2) = [s1] := by
  unfold ancestors pathComps
  rw [splitOn_slash_pair s1 s2 h1 h2]
  simp [List.range_succ]

private theorem peerStorePaths_nonBundleCoins (P : Party) :
    NonBundleCoinsStdio (normalizePath (identityFile (partyAddressName P))) ∧
    (∀ q ∈ ancestors (identityFile (partyAddressName P)), NonBundleCoinsStdio (normalizePath q)) ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath (identityFile (partyAddressName P)))).dropLast,
      NonBundleCoinsStdio pref) ∧
    NonBundleCoinsStdio (normalizePath (sessionFile (partyAddress P))) ∧
    (∀ q ∈ ancestors (sessionFile (partyAddress P)), NonBundleCoinsStdio (normalizePath q)) ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath (sessionFile (partyAddress P)))).dropLast,
      NonBundleCoinsStdio pref) := by
  cases P
  · have ha1 : ancestors "identities/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b" = ["identities"] :=
      ancestors_slash_pair "identities" "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b" (by decide) (by decide)
    have ha2 : ancestors "sessions/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1" = ["sessions"] :=
      ancestors_slash_pair "sessions" "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1" (by decide) (by decide)
    rw [identityFile_eq_f3, sessionFile_eq_f3]
    dsimp only
    rw [ha1, ha2]
    unfold NonBundleCoinsStdio
    decide
  · have ha1 : ancestors "identities/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6" = ["identities"] :=
      ancestors_slash_pair "identities" "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6" (by decide) (by decide)
    have ha2 : ancestors "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1" = ["sessions"] :=
      ancestors_slash_pair "sessions" "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1" (by decide) (by decide)
    rw [identityFile_eq_f3, sessionFile_eq_f3]
    dsimp only
    rw [ha1, ha2]
    unfold NonBundleCoinsStdio
    decide

private theorem writeOk_peer_of_inputsEquiv_pqInitInputsF {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) :
    WriteOk i (identityFile (partyAddressName st.party.other)) ∧
    WriteOk i (sessionFile (partyAddress st.party.other)) := by
  obtain ⟨hrf, hent⟩ := runFiles_and_entries_agree_pqInit heq hb zeroBundleE
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := peerStorePaths_nonBundleCoins st.party.other
  let st' : PqParty :=
    { st with peerId := some (partyIdentityKey .A)
              session := some (seedRecordExtras .A,
                (spqrOffSessionParams P.C).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩) }
  have hw := writeOk_pqInitInputs P st st' zeroBundleE t
  have hw_id := hw (identityFile (partyAddressName st.party.other), (partyIdentityKey .A).serialize)
    (by simp [encodeDir, st'])
  have hw_sess := hw (sessionFile (partyAddress st.party.other), encodeRecordUnderExtras
    (fun _ => seedRecordExtras .A)
    ((spqrOffSessionParams P.C).initA ⟨0#256, 0#256, 0#256, 0#256, 0#256⟩)) (by simp [encodeDir, st'])
  exact ⟨⟨hw_id.1, by change runFiles i _ ≠ some .dir; rw [hrf _ h1]; exact hw_id.2.1,
      fun q hq => by change runFiles i q = some .dir; rw [hrf q (h2 q hq)]; exact hw_id.2.2.1 q hq,
      fun pref hp => by rw [hent pref (h3 pref hp)]; exact hw_id.2.2.2 pref hp⟩,
    ⟨hw_sess.1, by change runFiles i _ ≠ some .dir; rw [hrf _ h4]; exact hw_sess.2.1,
      fun q hq => by change runFiles i q = some .dir; rw [hrf q (h5 q hq)]; exact hw_sess.2.2.1 q hq,
      fun pref hp => by rw [hent pref (h6 pref hp)]; exact hw_sess.2.2.2 pref hp⟩⟩

private theorem peer_id_pathStr (P : Party) :
    pathStr (pathOf (utf8 "identities") (addrValE P).name) = identityFile (partyAddressName P) := by
  rw [identityFile_eq_f3]
  cases P <;> exact String.toList_inj.mp (by
    unfold pathStr pathOf addrValE partyAddressName
    simp only [String.toList_ofList, utf8_eq_flatMap]
    decide)

private theorem peer_sess_pathStr (P : Party) :
    pathStr (pathOf (utf8 "sessions") (addressText (addrValE P))) = sessionFile (partyAddress P) := by
  rw [sessionFile_eq_f3]
  cases P <;> exact String.toList_inj.mp (by
    unfold pathStr pathOf addressText decimalText addrValE partyAddressName
    dsimp only
    rw [show (1#8).toNat = 1 from rfl, toString_one_eq]
    simp only [String.toList_ofList, utf8_eq_flatMap]
    decide)

private theorem cliRd_store_eq_of_runFiles_agree {F₁ F₂ : FsFiles} (P : Party)
    (hF : ∀ p : String, NonBundleCoinsStdio (normalizePath p) → F₁ p = F₂ p) :
    StoresGhost.opened.sessions.get cliIo.rd F₁ (addressText (partyAddr P)) =
      StoresGhost.opened.sessions.get cliIo.rd F₂ (addressText (partyAddr P)) ∧
    StoresGhost.opened.identity.peers.get cliIo.rd F₁ (partyAddr P).name =
      StoresGhost.opened.identity.peers.get cliIo.rd F₂ (partyAddr P).name := by
  obtain ⟨h1, h2, _, h4, h5, _⟩ := peerStorePaths_nonBundleCoins P
  have hrd_eq : ∀ (bs : List (BitVec 8)) (s : String), pathStr bs = s →
      NonBundleCoinsStdio (normalizePath s) →
      (∀ q ∈ ancestors s, NonBundleCoinsStdio (normalizePath q)) →
      cliIo.rd F₁ bs = cliIo.rd F₂ bs := fun bs s hs hp0 hanc => by
    have hblk : blockingAncestorF F₁ (pathStr bs) = blockingAncestorF F₂ (pathStr bs) := by
      rw [hs]
      unfold blockingAncestorF
      rw [List.find?_congr (fun q hq => by rw [hF q (hanc q hq)])]
      rcases hf : List.find? _ (ancestors s) with _ | q
      exacts [rfl, congrArg some (hF q (hanc q (List.mem_of_find?_eq_some hf)))]
    show cliRd F₁ bs = cliRd F₂ bs
    unfold cliRd readViewF
    rw [hblk, hs, hF s hp0]
  exact ⟨hrd_eq _ _ (peer_sess_pathStr P) h4 h5, hrd_eq _ _ (peer_id_pathStr P) h1 h2⟩

private theorem runRel_and_runAns_pqInitInputsF {S : RunSem} {X : UnreachedPqxdhPrimitives}
    {WP : PEParams} (hS : InitRunSemOk S X WP) {st : PqParty}
    {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw WP st files t))
    (hwf : PqxdhPartyInSpecDomain WP st) (hs : st.session = none) (hb : BundleFilesFlatRaw files) :
    runRel S i (runAns S i) ∧
    runAns S i =
      match readBundleV (runFiles i) (bytesOfString bundleDir) 1#8 with
      | none => some none
      | some bv => finish (initDef X WP (runFiles i)
          (addrValE st.party.other) (addrValE st.party) bv t.toList) (fun _ => []) := by
  obtain ⟨hS_init, hS_initOk, Scope, extra, hS_files, hextra_ref, hextra_ext⟩ := hS
  have hargv : i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := heq.1
  have hcoins : coinsOf i = t.toList := coinsOf_of_inputsEquiv_pqInitInputsF heq
  obtain ⟨hrf, _⟩ := runFiles_and_entries_agree_pqInit heq hb zeroBundleE
  have hown_eq := (initDef_eq_of_nonBundleCoins X WP st.party.other
    (addrValE st.party) (bundleVE zeroBundleE) t.toList hrf).1
  have hown := hown_eq.trans (ownAddr_pqInit WP st zeroBundleE t)
  have hbnds_ref := runBounds_pqInit WP st zeroBundleE t
  have hbnds : RunBounds i := by
    refine ⟨by rw [hcoins, List.Vector.toList_length]; decide, ?_, ?_,
      fun bs hbs => hbnds_ref.2.2.2.1 bs (hown_eq ▸ hbs),
      fun peer dir hp => hbnds_ref.2.2.2.2 peer dir (heq.1 ▸ hp)⟩
    · intro _ hp; rw [hargv, parseArgs_init] at hp; cases hp
    · intro _ hp; rw [hargv, parseArgs_init] at hp; cases hp
  have hfok_ref := filesOkPeer_pqInit (Scope := Scope) WP st zeroBundleE t
    (fun _ _ hs' => nomatch hs.symm.trans hs')
    (by simp [pqSessBytes, hs, fileCapBytes])
  obtain ⟨hsess_eq, hid_eq⟩ := cliRd_store_eq_of_runFiles_agree st.party.other hrf
  have hextra_i : extra (runFiles i) :=
    hextra_ext _ _ (fun p hp => (hrf p hp).symm) (hextra_ref st zeroBundleE t hwf hs)
  have hfilesOk : RunFilesOk S i :=
    runFilesOk_of_peer (.init (partyAddress st.party.other) bundleDir) rfl hargv hown
      (hS_files ▸ ⟨⟨hfok_ref.nameLt, hfok_ref.textLt, hfok_ref.sessPathOk, hfok_ref.idPathOk,
        hfok_ref.sessPathLt, hfok_ref.idPathLt, hsess_eq.symm ▸ hfok_ref.sessGet,
        hid_eq.symm ▸ hfok_ref.idGet⟩,
        distinctSid_party st.party, hextra_i⟩)
  have hinitOk_i := (initOk₀_and_initDef_of_nonBundleCoins X WP st zeroBundleE t
    heq.2.1 (fun p hp => filesOf_pqInitInputsF_nonBundleCoins heq hb hp) hwf hs).1
  have hhsOk : RunHsOk S i :=
    ⟨fun peer _ _ _ hp hget hme => by
       rw [hargv, parseArgs_init] at hp
       injection hp with hc
       injection hc with hpeer _
       rw [hown] at hget
       injection hget with hget'
       subst hget'
       rw [addrParse_textBytes] at hme
       injection hme with hme'
       rwa [← hpeer, ← hme', hS_initOk],
     fun _ _ _ _ _ hp _ _ _ _ => (by rw [hargv, parseArgs_init] at hp; cases hp)⟩
  refine ⟨⟨⟨st.party.other, .init (partyAddress st.party.other) bundleDir, rfl, hargv⟩, hbnds,
    hfilesOk, fun _ _ _ hp => (by rw [hargv, parseArgs_init] at hp; cases hp), hhsOk, rfl⟩, ?_⟩
  unfold runAns
  rw [hargv, parseArgs_init]
  dsimp only
  rw [hown]
  dsimp only
  rw [addrParse_textBytes, hcoins, hS_init]
  rfl

private def okPeerPathLocal (P : Party) (p : List (BitVec 8)) : Prop :=
  (∀ b ∈ p, b.toNat < 128) ∧
    (pathStr p = identityFile (partyAddressName P) ∨ pathStr p = sessionFile (partyAddress P))

private theorem initDef_writes_peer {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    {F : FsFiles} {P : Party} {me : AddrVal} {bv : BundleV} {coins ws_out : List (BitVec 8)}
    {ws : List (String × List (BitVec 8))}
    (h : finish (initDef X WP F (addrValE P) me bv coins) (fun _ => []) =
      some (some (ws, ws_out))) :
    ∀ pw ∈ ws, pw.1 = identityFile (partyAddressName P) ∨ pw.1 = sessionFile (partyAddress P) := by
  rcases ha : initDef X WP F (addrValE P) me bv coins with _ | (_ | ⟨g', _⟩) <;>
    rw [ha] at h <;> [cases h; cases h; skip]
  simp only [finish, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hws, _⟩ := h
  subst hws
  have hid_ok : okPeerPathLocal P (pathOf (utf8 "identities") (addrValE P).name) :=
    ⟨by cases P <;>
      { unfold pathOf addrValE partyAddressName
        simp only [utf8_eq_flatMap]
        decide },
      .inl (peer_id_pathStr P)⟩
  have hsess_ok : okPeerPathLocal P (pathOf (utf8 "sessions") (addressText (addrValE P))) :=
    ⟨by cases P <;>
      { unfold pathOf addressText decimalText addrValE partyAddressName
        dsimp only
        rw [show (1#8).toNat = 1 from rfl, toString_one_eq]
        simp only [utf8_eq_flatMap]
        decide },
      .inr (peer_sess_pathStr P)⟩
  have hok : StoresWrOk (okPeerPathLocal P) g' := by
    revert ha
    unfold initDef
    dsimp only
    rcases bundleEOf? bv with _ | _ <;> [exact fun ha => nomatch ha; dsimp only]
    rcases StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) bv.idKey with _ | btr
    · exact fun ha => nomatch ha
    · cases btr
      · exact fun ha => nomatch ha
      · dsimp only
        rcases StoresGhost.opened.identity.keyPair cliIo.rd F with _ | _ <;>
          rcases StoresGhost.opened.identity.regId cliIo.rd F with _ | _ <;>
          dsimp only <;> try (intro ha; cases ha)
        rcases initiateState _ _ _ _ _ _ with _ | ⟨_, _⟩
        · exact fun ha => nomatch ha
        · intro ha
          injection ha with h1
          injection h1 with h2
          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
          have h0 := StoresWrOk.opened (okPeerPathLocal P)
          exact { h0 with own := by rw [saveUpd_own]; exact h0.own
                          peers := DirWrOk.saveUpd h0.peers hid_ok
                          sessions := h0.sessions.put hsess_ok _ }
  intro pw hpw
  rw [namedWrites_ascii g'.writes (fun w hw => (hok.writes w hw).1)] at hpw
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hpw
  exact (hok.writes w hw).2

theorem observe_accept_pqInitInputsFRaw_eq (X : UnreachedPqxdhPrimitives) (WP : PEParams)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw WP st files t))
    (hwf : PqxdhPartyInSpecDomain WP st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files) (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b))
    {S : RunSem} (hS : InitRunSemOk S X WP) :
    runRel S i (runAns S i) ∧
    CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
    observe i.files (runAns S i) =
      pqxdhExpectedOutcome WP (pqInitInputsFRaw WP st files t) (pqInitModel X WP st b t) := by
  let ref := pqInitInputs WP st b t
  obtain ⟨hrel, hans_i0⟩ := runRel_and_runAns_pqInitInputsF hS heq hwf hs hb
  have hrb_i := ((readBundleV_iff_parseBundleDir_of_inputsEquivRaw heq hwf hb hcap).2 b).mpr hparse
  have hflat_b := bundleFilesFlatRaw_publicBundleOf b
  have hrb_ref : readBundleV (runFiles (pqInitInputs WP st b t))
      (bytesOfString bundleDir) 1#8 = some (bundleVE b) :=
    ((readBundleV_iff_parseBundleDir_pqInitInputsFRaw WP st ((publicBundleOf b).files bundleDir) t
      hwf hflat_b (bundleReadWithinCap_publicBundleOf b)).2 b).mpr (parseBundleDir_publicBundleOf b)
  have hinit_eq := (initOk₀_and_initDef_of_nonBundleCoins X WP st b t heq.2.1
    (fun p hp => filesOf_pqInitInputsF_nonBundleCoins heq hb hp) hwf hs).2.1
  have hans_i : runAns S i = finish (initDef X WP (runFiles i)
      (addrValE st.party.other) (addrValE st.party) (bundleVE b) t.toList)
      (fun _ => []) := by rw [hans_i0, hrb_i]
  have hans_ref : runAns S ref = finish (initDef X WP (runFiles ref)
      (addrValE st.party.other) (addrValE st.party) (bundleVE b) t.toList)
      (fun _ => []) := by dsimp only [ref]; rw [runAns_pqInit_eq, hrb_ref, hS.1]
  have hans_eq : runAns S i = runAns S ref := by rw [hans_i, hans_ref, hinit_eq]
  have hwr := writeOk_peer_of_inputsEquiv_pqInitInputsF heq hb
  have hcommit : CommitOk i (MainResult.ofAnswer (runAns S i)) := by
    rw [hans_i]
    rcases hf : finish (initDef X WP (runFiles i)
        (addrValE st.party.other) (addrValE st.party) (bundleVE b) t.toList)
        (fun _ => []) with _ | (_ | _)
    · trivial
    · intro _ hp; cases hp
    · intro pw hpw
      rcases initDef_writes_peer hf pw hpw with hp | hp <;> rw [hp] <;> [exact hwr.1; exact hwr.2]
  have hobs_ref := runAns_pqInit S X WP (pqInitiateAgrees_initDef_proof S X WP hS.1)
    st b t hwf hs
  refine ⟨hrel, hcommit, ?_⟩
  rw [hans_eq]
  rcases hm : pqInitModel X WP st b t with _ | (_ | ⟨st', _⟩) <;>
    rcases ha : runAns S ref with _ | (_ | ⟨ws, _⟩) <;>
    rw [hm, ha] at hobs_ref <;> dsimp only [observe, pqxdhExpectedOutcome, Option.map] at hobs_ref ⊢
  · nomatch hobs_ref
  · nomatch hobs_ref
  · nomatch hobs_ref
  · rw [funext heq.2.2.2]
  · injection hobs_ref with hc _ _; cases hc
  · nomatch hobs_ref
  · injection hobs_ref with hc _ _; cases hc
  · injection hobs_ref with _ hout hfs_ref
    subst hout
    congr 1
    have hws_not_bc : ∀ w ∈ ws, (normalizePath w.1).head? ≠ some bundleDir ∧
        (normalizePath w.1).head? ≠ some coinsFile := fun w hw => by
      rcases initDef_writes_peer (hans_ref.symm.trans ha) w hw with hp | hp <;> rw [hp]
      exacts [head_ne_bc_of_prefix "identities" _ (by decide) (by decide) (by decide) (by decide),
              head_ne_bc_of_prefix "sessions" _ (by decide) (by decide) (by decide) (by decide)]
    rw [filesOf_append_eq_of_filesOf_eq_not_bc heq.2.2.2 hws_not_bc]
    funext p
    by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
    · rw [filesOf_eq_none_of_nil_or_stdio _ hbad, filesOf_eq_none_of_nil_or_stdio _ hbad]
    · push Not at hbad
      by_cases hbc : (normalizePath p).head? = some bundleDir ∨ (normalizePath p).head? = some coinsFile
      · have hne_ws : ∀ w ∈ ws, (normalizePath w.1).head? ≠ (normalizePath p).head? :=
          fun w hw he => hbc.elim (fun h1 => (hws_not_bc w hw).1 (he.trans h1))
            (fun h2 => (hws_not_bc w hw).2 (he.trans h2))
        have hne_enc : ∀ w ∈ encodeDir WP st', (normalizePath w.1).head? ≠ (normalizePath p).head? :=
          fun w hw he => hbc.elim
            (fun h1 => (encodeDir_head_ne_bundle_coins WP st' hw).1 (he.trans h1))
            (fun h2 => (encodeDir_head_ne_bundle_coins WP st' hw).2 (he.trans h2))
        rw [filesOf_append_of_head_ne _ _ hne_ws, filesOf_append_of_head_ne _ _ hne_enc]
      · push Not at hbc
        have hag_inp_ref : ∀ q : String, NonBundleCoinsStdio (normalizePath q) →
            filesOf (pqInitInputsFRaw WP st files t).files q = filesOf ref.files q := fun q hq =>
          (filesOf_pqInitInputsF_nonBundleCoins (inputsEquivRaw_refl _) hb hq).trans
            (filesOf_pqInitInputsF_nonBundleCoins (inputsEquivRaw_refl _) hflat_b hq).symm
        have hp_nbc : NonBundleCoinsStdio (normalizePath p) := ⟨hbad.1, hbc.1, hbc.2, hbad.2⟩
        rw [filesOf_append_writes_eq_of_nonBundleCoins hag_inp_ref p hp_nbc,
          filesOf_append_writes_eq_of_nonBundleCoins hag_inp_ref p hp_nbc]
        exact congrFun hfs_ref p

theorem observe_reject_pqInitInputsFRaw_eq (X : UnreachedPqxdhPrimitives) (WP : PEParams)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw WP st files t))
    (hwf : PqxdhPartyInSpecDomain WP st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files) (hparse : parseBundleDir (filesOf files) bundleDir = none)
    {S : RunSem} (hS : InitRunSemOk S X WP) :
    runRel S i (runAns S i) ∧ CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
    observe i.files (runAns S i) = .exited 1 [] (filesOf (pqInitInputsFRaw WP st files t).files) := by
  obtain ⟨hrel, hans⟩ := runRel_and_runAns_pqInitInputsF hS heq hwf hs hb
  rw [readBundleV_eq_none_of_parseBundleDir_of_inputsEquivRaw heq hwf hb hparse] at hans
  dsimp only at hans
  refine ⟨hrel, ?_, ?_⟩
  · rw [hans]; intro _ hp; cases hp
  · rw [hans]; dsimp only [observe]; rw [funext heq.2.2.2]

theorem observe_overCap_pqInitInputsFRaw_eq (X : UnreachedPqxdhPrimitives) (WP : PEParams)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw WP st files t))
    (hwf : PqxdhPartyInSpecDomain WP st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files) (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir)
    {S : RunSem} (hS : InitRunSemOk S X WP) :
    runRel S i (runAns S i) ∧ CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
    observe i.files (runAns S i) = .exited 1 [] (filesOf (pqInitInputsFRaw WP st files t).files) := by
  obtain ⟨hrel, hans⟩ := runRel_and_runAns_pqInitInputsF hS heq hwf hs hb
  rw [readBundleV_eq_none_of_not_withinCap_of_inputsEquivRaw heq hwf hb hover] at hans
  dsimp only at hans
  refine ⟨hrel, ?_, ?_⟩
  · rw [hans]; intro _ hp; cases hp
  · rw [hans]; dsimp only [observe]; rw [funext heq.2.2.2]

/-! ## Whole-Process `MainInitRunSemOkF3` and `OutcomeOrExcusedAbort` Lifts -/

theorem cliRunPlacedSig_eq_none_of_not_inputsLoadable {mpl mmpl : MultiPlacement}
    (elf : ElfImage) (W : CliHooks) {i : Inputs}
    (hnot : ¬ InputsLoadable i) : cliRunPlacedSig mpl mmpl elf W i = none := by
  have herr : ∃ msg, elf.loadState (cliProcessInputs i) = .error msg := by
    unfold ElfImage.loadState
    by_cases hwf : (!elf.WellFormed) = true
    · simp [hwf, Bind.bind, Except.bind]
    · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Bind.bind, pure, Except.pure, Except.bind]
      by_cases hd : ((cliProcessInputs i).dirs.any fun d => hasLeadingSlash d || hasDotDot d) = true
      · simp [hd]
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        by_cases hf : ((cliProcessInputs i).files.any
            fun (p, bs) => hasLeadingSlash p || hasDotDot p ||
              !decide (bs.length ≤ MAX_LFS_FILESIZE)) = true
        · simp [hf]
        · exfalso
          apply hnot
          simp only [Bool.not_eq_true, List.any_eq_false, Bool.or_eq_false_iff,
            Bool.not_eq_false', decide_eq_true_eq] at hd hf
          exact ⟨fun d hm => hd d hm, fun f hm => ⟨⟨(hf f hm).1.1, (hf f hm).1.2⟩, (hf f hm).2⟩⟩
  unfold cliRunPlacedSig
  split
  · rename_i hex
    obtain ⟨_, _, hload, _⟩ := hex
    obtain ⟨_, hmsg⟩ := herr
    rw [hmsg] at hload
    cases hload
  · rfl

private theorem not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsSendOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs] at hgt

private theorem not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t)) :
    ¬ IsStdinOverCap i := by
  rintro ⟨-, hgt⟩
  rw [heq.2.2.1] at hgt
  simp [pqInitInputsFRaw, pqInputs, stdinCapBytes] at hgt

/-- Flat-bundle `init` input domain (`InputsEquivRaw i (pqInitInputsFRaw WP st files t)` with `st.session = none` and `BundleFilesFlatRaw files`). -/
def CliInitD3Inputs (WP : PEParams) (i : Inputs) : Prop :=
  ∃ (st : PqParty) (files : List (String × List (BitVec 8)))
    (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain WP st ∧ st.session = none ∧
    BundleFilesFlatRaw files ∧ InputsEquivRaw i (pqInitInputsFRaw WP st files t)

/-- Restricts `Run₀` to `CliInitD3Inputs WP`. -/
def initD3ScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop)
    (i : Inputs) (a : RunAnswer) : Prop :=
  CliInitD3Inputs WP i ∧ Run₀ i a

/-- Two-placement `NeedLocks` and `cliBudgetLimits` `main` specification for flat-bundle `init`, scoped to `initD3ScopedRun`. -/
def MainInitRunSemOkF3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∃ S : RunSem,
      InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
      ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
            (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)

abbrev MainInitSemF3 := MainInitRunSemOkF3

section OfF3

variable {mpl mmpl : MultiPlacement}
  {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
  {elf : ElfImage}
  (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
  (hinitSem : MainInitRunSemOkF3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
include H hinitSem

private theorem outcomeUpTo_of_f3_sem (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {i : Inputs} {o : Outcome}
    (hdom : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (hi : CliInputsOk i) (hload : InputsLoadable i)
    (hnoc : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i)
    (hstep : ∀ S : RunSem, InitRunSemOk S X ⟨W.C, W.Q⟩ →
      runRel S i (runAns S i) ∧
      CommitOk i (MainResult.ofAnswer (runAns S i)) ∧
      observe i.files (runAns S i) = o) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i (· = o) := by
  obtain ⟨S, hS, hmainW⟩ := hinitSem H.base547NeZero X W
  obtain ⟨hrel, hcommit, hobs⟩ := hstep S hS
  have hextSig :
      cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W |> fun _ =>
        cliRunPlacedSig mpl mmpl elf W i = some o := by
    have hrunExt :=
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
        (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
        H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW
        H.stkLo H.stkHi hi hload ⟨hdom, hrel⟩ hnoc hnstin hobs hcoins hcommit
    have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
    exact (cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl).trans hrunExt
  exact outcomeOrExcusedAbort_of_eq hextSig

theorem outcomeUpTo_pqInitFiles_exact_of_f3 (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  outcomeUpTo_of_f3_sem H hinitSem W X ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_accept_pqInitInputsFRaw_eq X ⟨W.C, W.Q⟩ heq hwf hs hb hcap hparse hS)

theorem outcomeUpTo_pqInitFiles_exact_or_none_of_f3 (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {st : PqParty} {files : List (String × List (BitVec 8))} {b : PreKeyBundleFields}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hcap : BundleReadWithinCap (filesOf files) bundleDir)
    (hparse : parseBundleDir (filesOf files) bundleDir = some (publicBundleOf b)) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t)
          (pqInitModel X ⟨W.C, W.Q⟩ st b t)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitFiles_exact_of_f3 H hinitSem W X heq hload hwf hs hb hcap hparse)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

private def dummyUnreached : UnreachedPqxdhPrimitives where
  sigPkGen := fun _ => []
  sigSign := fun _ _ _ => []
  scalarMul := fun _ _ => []
  scalarAdd := fun _ _ => []
  kemKeyGen := fun _ => ([], [])
  pow8 := fun _ => []
  isValidDhTriple := fun _ _ _ => false

theorem outcomeUpTo_pqInitReject_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  outcomeUpTo_of_f3_sem H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_reject_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hparse hS)

theorem outcomeUpTo_pqInitReject_or_none_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hparse : parseBundleDir (filesOf files) bundleDir = none) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitReject_of_f3 H hinitSem W heq hload hwf hs hb hparse)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

theorem outcomeUpTo_pqInitOverCap_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hload : InputsLoadable i)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) i
      (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) :=
  outcomeUpTo_of_f3_sem H hinitSem W dummyUnreached ⟨st, files, t, hwf, hs, hb, heq⟩
    (cliInputsOk_of_inputsEquivRaw heq (cliInputsOk_pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    hload (not_isSendOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (not_isStdinOverCap_of_inputsEquiv_pqInitInputsF_f3 heq)
    (coinsReadable_of_inputsEquiv_pqInitInputsF_f3 heq)
    (fun _ hS => observe_overCap_pqInitInputsFRaw_eq dummyUnreached ⟨W.C, W.Q⟩ heq hwf hs hb hover hS)

theorem outcomeUpTo_pqInitOverCap_or_none_of_f3 (W : CliHooks)
    {st : PqParty} {files : List (String × List (BitVec 8))}
    {t : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (heq : InputsEquivRaw i (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t))
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hs : st.session = none)
    (hb : BundleFilesFlatRaw files)
    (hover : ¬ BundleReadWithinCap (filesOf files) bundleDir) :
    cliRunPlacedSig mpl mmpl elf W i = none ∨
      OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
        (cliRunPlacedSig mpl mmpl elf W) i
        (· = .exited 1 [] (filesOf (pqInitInputsFRaw ⟨W.C, W.Q⟩ st files t).files)) := by
  by_cases hload : InputsLoadable i
  · exact .inr (outcomeUpTo_pqInitOverCap_of_f3 H hinitSem W heq hload hwf hs hb hover)
  · exact .inl (cliRunPlacedSig_eq_none_of_not_inputsLoadable elf W hload)

end OfF3

end LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
