/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Whole-`main` `RealCliMainEnvOf` Domain Adapter

Proves `∀ i, CliPqxdhInputs W i → FitsEnv fineCostModel lim fineCostModel.init (RealCliMainEnvOf E i)`
both parametrically in `(SE, hSlots)` and unconditionally at `mkExistentialRealCalleeEnvs img S W`
(with `< 90%` of `1 GiB` physical RAM footprint `962,211,497 ≤ 966,367,641` B), plus unconditional
`argvLen ≤ 1820` setup/early-exit `FitsEnv` bounds and `recv-prekey` non-vacuity witnesses.
-/

@[expose] public section
set_option autoImplicit false
namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter

open Arm64 (FsEntry FsPath FsState normalizePath splitSlash)
open Arm64.Process (ProcessInputs bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams initiateTapeLen partyAddressName)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain baseKeysFile bundleDir coinsFile
   encodeDir fileCapBytes partyAddress publicBundleOf textBytes)
open CryptoVerification.SignalSession.Cli (StoresGhost cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV RunCall addrParse cliIo cliRd parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem addrValOf callPeer runFiles)
open CryptoVerification.SignalSession.CliExt (pathStr readFileResult)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride reserveMinCap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs SeqEnv rustAllocEvents
   rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (ReadFileEnv ReadStdinEnv allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (SessionRecordCapInDomain argv_length_le_of_cliPqInputs encodeDir_files_le_of_caps
   publicBundleOf_files_le_1637)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds fitsTrace_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (cliIoReadFileEnv_nonFreeBound cliIoReadStdinEnv_nonFreeBound cliMainSetupFineGrpS
   fine_rustAlloc_le_44 m1PhaseEnv_groupSpec m1PhaseEnv_le_3_fine_groupSpec m2CollectEnv_groupSpec
   m2CollectStepEnv_groupSpec m5PhaseEnv_groupSpec m6Env_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (CliIoReadFileEnv CliIoReadStdinEnv addrParse_name_bounds phaseCreditSpec_cliIoReadFile_anyR_tight
   phaseCreditSpec_cliIoReadStdin_anyR_tight phaseCredit_allocBytes1_tight phaseCredit_m1Phase_small64
   phaseCredit_m2Collect_small64 phaseCredit_rustRealloc_small_any specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainCliIoEnv CliMainEnv CliMainSetupCliIoEnv CliMainSetupEnv M1PhaseEnv M2CollectEnv
   M2CollectStepEnv M3PhaseCliIoEnv M3PhaseEnv M5DirStepEnv M5PhaseEnv M6Env cliMainDeltaCum_tight
   cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq m3PhaseDeltaCum_tight
   m3PhaseDeltaLive m3PhaseDeltaPeak m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq
   m5DirStep_phaseCredit m6DeltaCum m6_phaseCredit_small1024 readFileDeltaCum_tight
   readStdinDeltaCum_tight readStdinDeltaLive readStdinDeltaPeak readStdinMaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes existentialRealCalleeFineSpecs
   existentialRealCalleeFineSpecs_direct_run_bounds mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOpenedEnv cliRunOpened_tight_phaseCredit fineCostModel_cliRunTightHyps)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (CliRunTightSpqrCaps cliRunSpqrAndInitCaps_of_cliPqInputs)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs CliRealR2CalleeCaps cliPqRealCallDomain_recvPrekey_nonvacuous
   cliRealMainStepReserve cliRealNinetyPctOneGiB cliRealR2_fits_90pct_and_oneGiB
   cliRealRunCumCap cliRealRunGrpSCap cliRealRunLiveCap cliRealRunPeakCap cliRealRunReqCap
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS cliRunOpened_real_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightCumOf cliMainTightGrpCountOf cliMainTightGrpSOf cliMainTightLiveOf
   cliMainTightPeakOf cliMainTightReqOf cliMainTightStepReserveOf)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers (cliIoCapEvents cliIoReadCaps)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound PhaseGroupSpec fineStepReserveOfGroups)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (cliRealDirect1MiB_i_fits_90pct_and_oneGiB cliRealDirectRunCum_i cliRealDirectRunGrpS_i
   cliRealDirectRunLive_i cliRealDirectRunMaxReq_i cliRealDirectRunPeak_i)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec (fineCostModel_wireLowInterceptHyps)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (AddressEnv addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

private abbrev seqEnv_mono := @SeqCreditKit.SeqEnv.mono

/-! ## 1. Path-Indexed `initFsState` Provenance & `CliPqxdhInputs` Read Bounds -/

private def EntriesFromAt (files : List (String × List (BitVec 8))) (fs : FsState) : Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, (p, bs) ∈ files ∧ normalizePath p = k

private theorem entriesFromAt_empty (files : List (String × List (BitVec 8))) :
    EntriesFromAt files ({} : FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem entriesFromAt_setDir {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFromAt files fs) (pref : FsPath) :
    EntriesFromAt files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromAt_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List FsPath) {fs : FsState} (h : EntriesFromAt files fs) :
    EntriesFromAt files (prefs.foldl (fun a pref => a.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with | nil => exact h | cons hd _ ih => exact ih (entriesFromAt_setDir h hd)

private theorem entriesFromAt_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : FsState} (h : EntriesFromAt files fs) :
    EntriesFromAt files (dirs.foldl (fun acc d =>
      (FsPath.nonEmptyPrefixes (normalizePath d)).foldl (fun a p => a.setEntry p (some .dir)) acc) fs) := by
  induction dirs generalizing fs with | nil => exact h | cons _ _ ih => exact ih (entriesFromAt_foldl_dirs _ h)

private theorem entriesFromAt_setFile {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFromAt files fs) {p : String} {bs : List (BitVec 8)} (hmem : (p, bs) ∈ files) :
    EntriesFromAt files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold FsState.setFile FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i hbeq; have hk_eq : k = normalizePath p := LawfulBEq.eq_of_beq hbeq
    injection hk with hfile; injection hfile with hbs; subst hbs hk_eq; exact ⟨p, hmem, rfl⟩
  · exact h k bs' hk

private theorem entriesFromAt_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8))) (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : FsState} (h : EntriesFromAt allFiles fs) :
    EntriesFromAt allFiles (rem.foldl (fun acc (p, bs) =>
      let w := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun a pref => a.setEntry pref (some .dir)) acc
      w.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd _ ih =>
    rcases hd with ⟨p, bs⟩; exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      (entriesFromAt_setFile (entriesFromAt_foldl_dirs _ h) (hsub _ (List.mem_cons_self ..)))

/-- Every regular file in `(initFsState inputs).files q` comes from `(p, bs) ∈ inputs.files`
with `normalizePath p = normalizePath q`. -/
theorem initFsState_files_mem_norm {inputs : ProcessInputs} {q : String} {bs : List (BitVec 8)}
    (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, (p, bs) ∈ inputs.files ∧ normalizePath p = normalizePath q := by
  unfold FsState.files FsState.getEntry at h; split at h
  · cases h
  · exact entriesFromAt_foldl_files inputs.files (fun _ hx => hx)
      (entriesFromAt_foldl_outer_dirs inputs.dirs (entriesFromAt_empty inputs.files)) (normalizePath q) bs h

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r; fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList; simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]
private theorem repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem splitSlash_go_cons_ne {cur : List Char} {c : Char} (hc : c ≠ '/') (cs : List Char) :
    splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
  rw [splitSlash.go.eq_def]; split
  · simp_all
  · simp_all
  · rename_i _ _ _ _ heq; injection heq with h1 h2; subst h1 h2; rfl

private theorem splitSlash_go_head : ∀ (cs cur : List Char),
    ∃ post, (splitSlash.go cur cs).head? = some (String.ofList (cur.reverse ++ post))
  | [], cur => ⟨[], by simp [splitSlash.go]⟩
  | c :: cs, cur => by
    by_cases hc : c = '/'
    · subst hc; exact ⟨[], by simp [splitSlash.go]⟩
    · rw [splitSlash_go_cons_ne hc]; obtain ⟨post, hpost⟩ := splitSlash_go_head cs (c :: cur)
      exact ⟨c :: post, by simpa [List.reverse_cons, List.append_assoc] using hpost⟩

private theorem normalizePath_head_first_char {s : String} {c : Char}
    (hs : s.toList.head? = some c) (hc_slash : c ≠ '/') (hc_dot : c ≠ '.') :
    ∃ tl : List Char, (normalizePath s).head? = some (String.ofList (c :: tl)) := by
  cases hcs : s.toList with
  | nil => rw [hcs] at hs; cases hs
  | cons c' cs =>
    rw [hcs, List.head?_cons, Option.some.injEq] at hs; subst hs
    unfold normalizePath splitSlash; rw [hcs, splitSlash_go_cons_ne hc_slash]
    obtain ⟨post, hhead⟩ := splitSlash_go_head cs [c']
    cases hgo : splitSlash.go [c'] cs with
    | nil => rw [hgo] at hhead; cases hhead
    | cons seg rest =>
      rw [hgo, List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hrev : [c'].reverse ++ post = c' :: post := rfl; rw [hrev]
      have hlist : (String.ofList (c' :: post)).toList = c' :: post := String.toList_ofList
      have hne : (String.ofList (c' :: post)).isEmpty = false := by
        rw [Bool.eq_false_iff]; intro he
        have h0 := congrArg String.toList (String.isEmpty_iff.mp he); rw [hlist] at h0; cases h0
      have hndot : (String.ofList (c' :: post) != ".") = true := by
        rw [bne_iff_ne]; intro he; have h0 := congrArg String.toList he
        have hdot : ".".toList = ['.'] := by decide
        rw [hlist, hdot] at h0; injection h0 with hc_eq _; exact hc_dot hc_eq
      have hpred : (!(String.ofList (c' :: post)).isEmpty && String.ofList (c' :: post) != ".") = true := by
        rw [hne, hndot]; rfl
      rw [List.filter_cons_of_pos (p := fun seg => !seg.isEmpty && seg != ".") hpred, List.head?_cons]
      exact ⟨post, rfl⟩

private theorem append_toList_head {pref : String} {c : Char}
    (hp : pref.toList.head? = some c) (s : String) : (pref ++ s).toList.head? = some c := by
  rw [String.toList_append]; cases hl : pref.toList with
  | nil => rw [hl] at hp; cases hp
  | cons _ _ => rw [hl, List.head?_cons] at hp; rw [List.cons_append, List.head?_cons]; exact hp

private theorem head_ne_of_first_char {s : String} {c d : Char} {seg : String}
    (hs : s.toList.head? = some c) (hc_slash : c ≠ '/') (hc_dot : c ≠ '.')
    (hseg : seg.toList.head? = some d) (hcd : c ≠ d) : (normalizePath s).head? ≠ some seg := by
  obtain ⟨tl, hhead⟩ := normalizePath_head_first_char hs hc_slash hc_dot
  rw [hhead]; intro heq; injection heq with heq'; have h0 := congrArg (fun x => x.toList.head?) heq'
  rw [String.toList_ofList, List.head?_cons, hseg] at h0; injection h0 with h1; exact hcd h1

private theorem partyAddress_textBytes_length_le_40 (p : Party) :
    (textBytes (partyAddress p).text).length ≤ 40 := by
  unfold textBytes partyAddress CryptoVerification.SignalSession.Address.text; dsimp only
  rw [repr_utf8_eq_kutf8]
  have hk_app (a b : String) : kutf8 (a ++ b) = kutf8 a ++ kutf8 b := by
    simp [kutf8, String.toList_append, List.flatMap_append]
  rw [hk_app, hk_app, List.length_append, List.length_append]
  have hd : (kutf8 (toString (1 : Nat))).length ≤ 1 := by
    rw [← utf8_eq_kutf8]; exact decimalText_length_le 1 1 (by omega) (by omega)
  have hdot : (kutf8 ".").length = 1 := rfl
  have hp : (kutf8 (partyAddressName p)).length = 36 := by cases p <;> rfl
  omega

private theorem encodeDir_entry_head_or_lr {W : PEParams} {st : PqParty}
    {p : String} {bs : List (BitVec 8)} (hmem : (p, bs) ∈ encodeDir W st) :
    ((∃ c ∈ (['a', 'i', 'r', 's', 'o'] : List Char), p.toList.head? = some c) ∧
      (p, bs) ∈ encodeDir W { st with kyberLastResort := [] }) ∨
    p.toList.head? = some 'l' := by
  unfold encodeDir at hmem; rw [List.mem_append] at hmem
  rcases hmem with hpre | hf_klr
  · refine Or.inl ⟨?_, by
      unfold encodeDir; simp only [List.map_nil, List.flatten_nil, List.append_nil]; exact hpre⟩
    simp only [List.mem_append] at hpre
    rcases hpre with ((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
      rcases hf_hdr with h | h | h <;> (injection h with hp _; subst hp)
      · exact ⟨'a', by decide, by decide⟩
      · exact ⟨'i', by decide, by decide⟩
      · exact ⟨'r', by decide, by decide⟩
    · cases hp : st.peerId with
      | none => simp [hp] at hf_peer
      | some k =>
        simp only [hp, List.mem_singleton] at hf_peer; injection hf_peer with hp_eq _; subst hp_eq
        exact ⟨'i', by decide, append_toList_head (pref := "identities/") (by decide) _⟩
    · cases hs : st.session with
      | none => simp [hs] at hf_sess
      | some xg =>
        rcases xg with ⟨_, _⟩
        simp only [hs, List.mem_singleton] at hf_sess; injection hf_sess with hp_eq _; subst hp_eq
        exact ⟨'s', by decide, append_toList_head (pref := "sessions/") (by decide) _⟩
    · rw [List.mem_map] at hf_sig; rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      dsimp only at h; injection h with hp_eq _; subst hp_eq
      exact ⟨'s', by decide, append_toList_head (pref := "signed-pre-keys/") (by decide) _⟩
    · rw [List.mem_map] at hf_ot; rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      dsimp only at h; injection h with hp_eq _; subst hp_eq
      exact ⟨'o', by decide, append_toList_head (pref := "one-time-pre-keys/") (by decide) _⟩
    · rw [List.mem_map] at hf_kot; rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      dsimp only at h; injection h with hp_eq _; subst hp_eq
      exact ⟨'o', by decide, append_toList_head (pref := "one-time-kyber-pre-keys/") (by decide) _⟩
  · rw [List.mem_flatten] at hf_klr; rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub; rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq _; subst hp_eq
      exact Or.inr (append_toList_head (pref := "last-resort-kyber-pre-keys/") (by decide) _)
    · injection h2 with hp_eq _; subst hp_eq; unfold baseKeysFile; rw [String.append_assoc]
      exact Or.inr (append_toList_head (pref := "last-resort-kyber-pre-keys/") (by decide) _)

private theorem encodeDir_entry_nonBaseKeys_le {W : PEParams} {st : PqParty}
    (hwf : PqxdhPartyInSpecDomain W st) (hSess : SessionRecordCapInDomain W sessionCapBytes)
    {p : String} {bs : List (BitVec 8)} (hmem : (p, bs) ∈ encodeDir W st)
    (hnot_lr : ∀ tl : List Char, (normalizePath p).head? ≠ some (String.ofList ('l' :: tl))) :
    bs.length ≤ sessionCapBytes := by
  rcases encodeDir_entry_head_or_lr hmem with ⟨_, hmem'⟩ | hl
  · have hwf' : PqxdhPartyInSpecDomain W { st with kyberLastResort := [] } :=
      ⟨hwf.1, fun f hf => hwf.2.1 f (by
        unfold encodeDir at hf ⊢
        simp only [List.map_nil, List.flatten_nil, List.append_nil] at hf
        exact List.mem_append_left _ hf),
       hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, List.nodup_nil⟩
    have hle := encodeDir_files_le_of_caps hwf' hSess (bkCap := 0)
      (fun _ _ _ hm => nomatch hm) (p, bs) hmem'
    dsimp only at hle; unfold sessionCapBytes at *; omega
  · obtain ⟨tl, hhead⟩ := normalizePath_head_first_char hl (by decide) (by decide)
    exact False.elim (hnot_lr tl hhead)

private theorem encodeDir_head_ne_bc {W : PEParams} {st : PqParty}
    {p : String} {bs : List (BitVec 8)} (hmem : (p, bs) ∈ encodeDir W st)
    {seg : String} {d : Char} (hd : d = 'b' ∨ d = 'c') (hseg : seg.toList.head? = some d) :
    (normalizePath p).head? ≠ some seg := by
  rcases encodeDir_entry_head_or_lr hmem with ⟨⟨c, hc_mem, hp_c⟩, _⟩ | hp_l
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_mem
    rcases hd with rfl | rfl <;> rcases hc_mem with rfl | rfl | rfl | rfl | rfl <;>
      exact head_ne_of_first_char hp_c (by decide) (by decide) hseg (by decide)
  · rcases hd with rfl | rfl <;>
      exact head_ne_of_first_char hp_l (by decide) (by decide) hseg (by decide)

private theorem cliPqInputs_files_cases {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ (cliInputs i).files) :
    (∃ st, PqxdhPartyInSpecDomain W st ∧ (p, bs) ∈ encodeDir W st) ∨
    (∃ b, (p, bs) ∈ (publicBundleOf b).files bundleDir) ∨ (p = coinsFile ∧ bs.length ≤ 192) := by
  have hno_bun {coins : List (BitVec 8)} (hc : coins.length ≤ 192) {st : PqParty}
      (hwf : PqxdhPartyInSpecDomain W st)
      (hm : (p, bs) ∈ (encodeDir W st ++ []) ++ [(coinsFile, coins)]) :
      (∃ st, PqxdhPartyInSpecDomain W st ∧ (p, bs) ∈ encodeDir W st) ∨
      (∃ b, (p, bs) ∈ (publicBundleOf b).files bundleDir) ∨ (p = coinsFile ∧ bs.length ≤ 192) := by
    rw [List.append_nil, List.mem_append, List.mem_singleton] at hm
    rcases hm with hed | hcoins
    · exact Or.inl ⟨st, hwf, hed⟩
    · injection hcoins with hp hbs; subst hp hbs; exact Or.inr (Or.inr ⟨rfl, hc⟩)
  rcases hi with ⟨st, hwf, hcase⟩
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, _, rfl⟩
  · change (p, bs) ∈ encodeDir W st ++ (publicBundleOf b).files bundleDir ++
        [(coinsFile, t.toList)] at hmem
    rw [List.mem_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hed | hbun) | hcoins
    · exact Or.inl ⟨st, hwf, hed⟩
    · exact Or.inr (Or.inl ⟨b, hbun⟩)
    · injection hcoins with hp hbs; subst hp hbs
      have ht : t.toList.length = initiateTapeLen := t.toList_length
      unfold initiateTapeLen at ht; exact Or.inr (Or.inr ⟨rfl, by omega⟩)
  · exact hno_bun (by have := r.toList_length; omega) hwf hmem
  · exact hno_bun (by simp [keyToBytes32]) hwf hmem
  · exact hno_bun (by simp [keyToBytes32]) hwf hmem
  · exact hno_bun (by simp [keyToBytes32]) hwf hmem

/-- On `CliPqxdhInputs W i`, the `"coins"` file in `(initFsState (cliInputs i)).files` has length
`≤ 192 ≤ sessionCapBytes`. -/
theorem coins_file_length_le_of_cliPqInputs {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) {bs : List (BitVec 8)}
    (hfile : (initFsState (cliInputs i)).files (pathStr (utf8 "coins")) = some (.file bs)) :
    bs.length ≤ sessionCapBytes := by
  have hpc : pathStr (utf8 "coins") = "coins" := by unfold pathStr; rw [utf8_eq_kutf8]; rfl
  have hnorm_coins : normalizePath (pathStr (utf8 "coins")) = ["coins"] := by rw [hpc]; decide
  obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
  rw [hnorm_coins] at hp_norm
  rcases cliPqInputs_files_cases hi hmem with ⟨_, _, hed⟩ | ⟨b, hbun⟩ | ⟨_, hle⟩
  · exact False.elim (encodeDir_head_ne_bc hed (seg := "coins") (Or.inr rfl)
      (by decide) (by rw [hp_norm]; rfl))
  · have hb := publicBundleOf_files_le_1637 b bundleDir (p, bs) hbun
    dsimp only at hb; unfold sessionCapBytes; omega
  · unfold sessionCapBytes; omega

/-- Own-address lookup on `CliPqxdhInputs W i` returns `≤ 40` bytes. -/
theorem cliIo_rd_ownAddress_le_40_of_cliPqInputs {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) {bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok bs) : bs.length ≤ 40 := by
  change StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") = .ok bs at hrd
  rcases hi with ⟨st, _, hcase⟩
  have hget : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") =
      .ok (textBytes (partyAddress st.party).text) := by
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
        ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
    · exact CryptoVerification.SignalSession.Cli.RunRefine.ownAddr_pqInit W st b t
    · exact CryptoVerification.SignalSession.Cli.RunRefine.ownAddr_pqSend W st m r
    · exact CryptoVerification.SignalSession.Cli.RunRefine.ownAddr_pqRecv W st _ rc
    · exact CryptoVerification.SignalSession.Cli.RunRefine.ownAddr_pqRecv W st _ rc
    · exact CryptoVerification.SignalSession.Cli.RunRefine.ownAddr_pqRecv W st _ rc
  rw [hget] at hrd; injection hrd with hbs; subst hbs
  exact partyAddress_textBytes_length_le_40 st.party

private theorem cliIo_rd_eq_ok_nil_or_files_some {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨ (initFsState (cliInputs i)).files (pathStr path) = some (.file bs) := by
  change cliRd (initFsState (cliInputs i)).files path = .ok bs at hrd
  unfold cliRd at hrd; split at hrd
  · cases hrd
  · rename_i rbs hrv; injection hrd with h; subst h
    unfold CryptoVerification.SignalSession.Cli.MainHops.readViewF at hrv; split at hrv
    · cases hrv
    · injection hrv with h; subst h; exact Or.inl rfl
    · split at hrv
      · rename_i fbs hfp
        split at hrv
        · injection hrv with h; subst h; exact Or.inr hfp
        · cases hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl

private theorem pathStr_cons_head (b : BitVec 8) (bs : List (BitVec 8)) :
    (pathStr (b :: bs)).toList.head? = some (Char.ofNat b.toNat) := by
  unfold pathStr; rw [List.map_cons, String.toList_ofList, List.head?_cons]

private theorem pathStr_pathOf_bundle_first_char (name : List (BitVec 8)) :
    (pathStr (pathOf (bytesOfString bundleDir) name)).toList.head? = some 'b' := by
  have hb : bytesOfString bundleDir = [0x62#8, 0x75#8, 0x6e#8, 0x64#8, 0x6c#8, 0x65#8] := rfl
  have hp : pathOf (bytesOfString bundleDir) name =
      0x62#8 :: ([0x75#8, 0x6e#8, 0x64#8, 0x6c#8, 0x65#8] ++ utf8 "/" ++ name) := by
    unfold pathOf; rw [hb]; rfl
  rw [hp, pathStr_cons_head]; rfl

/-- On `CliPqxdhInputs W g.i` with `parseArgs = some g.c`, every `.init peer dir` command has
`dir.length ≤ 26` and bundle file reads `≤ 1637` B. -/
theorem cliIo_rd_initBundle_caps_of_cliPqInputs {W : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    ∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637) := by
  intro peer dir hcmd; rcases hi with ⟨st, _, hcase⟩
  have hrecv (harg : g.i.argv = (Cmd.recv (partyAddress st.party.other)).argv) : False := by
    rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv, hcmd] at hparse
    cases hparse
  rcases hcase with ⟨_, b, t, hi_eq⟩ | ⟨_, _, _, hi_eq⟩ | ⟨_, _, _, hi_eq⟩ |
      ⟨_, _, _, hi_eq⟩ | ⟨_, _, _, _, _, hi_eq⟩
  · have harg : g.i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := by
      rw [hi_eq]; rfl
    rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_init, hcmd] at hparse
    injection hparse with hcmd_eq; injection hcmd_eq with _ hdir_eq; subst hdir_eq
    refine ⟨by decide, fun name bs hrd => ?_⟩
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 1637
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      rw [hi_eq] at hmem
      change (p, bs) ∈ encodeDir W st ++ (publicBundleOf b).files bundleDir ++
          [(coinsFile, t.toList)] at hmem
      rw [List.mem_append, List.mem_append, List.mem_singleton] at hmem
      obtain ⟨tl_b, hhead_b⟩ := normalizePath_head_first_char
        (pathStr_pathOf_bundle_first_char name) (by decide) (by decide)
      have hb_seg : (String.ofList ('b' :: tl_b)).toList.head? = some 'b' := by
        rw [String.toList_ofList, List.head?_cons]
      rcases hmem with (hed | hbun) | hcoins
      · exact False.elim (encodeDir_head_ne_bc hed (Or.inl rfl) hb_seg (hp_norm ▸ hhead_b))
      · exact publicBundleOf_files_le_1637 b bundleDir (p, bs) hbun
      · injection hcoins with hp_coins _; subst hp_coins
        have hc_head : (normalizePath coinsFile).head? = some "coins" := by decide
        rw [hp_norm, hhead_b] at hc_head; injection hc_head with hc_eq
        have h0 := congrArg (fun s => s.toList.head?) hc_eq
        have hc_list : "coins".toList.head? = some 'c' := by decide
        rw [hb_seg, hc_list] at h0; injection h0 with hcb; exact absurd hcb (by decide)
  · have harg : g.i.argv = (Cmd.send (partyAddress st.party.other)).argv := by rw [hi_eq]; rfl
    rw [harg, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_send, hcmd] at hparse
    cases hparse
  · exact False.elim (hrecv (by rw [hi_eq]; rfl))
  · exact False.elim (hrecv (by rw [hi_eq]; rfl))
  · exact False.elim (hrecv (by rw [hi_eq]; rfl))

private theorem pathStr_pathOf_sessions_first_char (name : List (BitVec 8)) :
    (pathStr (pathOf StoresGhost.opened.sessions.path name)).toList.head? = some 's' := by
  have hs : StoresGhost.opened.sessions.path =
      [0x73#8, 0x65#8, 0x73#8, 0x73#8, 0x69#8, 0x6f#8, 0x6e#8, 0x73#8] := by
    change utf8 "sessions" = _; rw [utf8_eq_kutf8]; rfl
  have hp : pathOf StoresGhost.opened.sessions.path name =
      0x73#8 :: ([0x65#8, 0x73#8, 0x73#8, 0x69#8, 0x6f#8, 0x6e#8, 0x73#8] ++ utf8 "/" ++ name) := by
    unfold pathOf; rw [hs]; rfl
  rw [hp, pathStr_cons_head]; rfl

/-- Under `SessionRecordCapInDomain W sessionCapBytes`, every `sessions/<name>` lookup in
`runFiles i` on `CliPqxdhInputs W i` returns `≤ sessionCapBytes` B. -/
theorem cliIo_rd_sessions_le_of_cliPqInputs {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) (hSessCap : SessionRecordCapInDomain W sessionCapBytes)
    {name bs : List (BitVec 8)}
    (hrd : StoresGhost.opened.sessions.get cliIo.rd (runFiles i) name = .ok bs) :
    bs.length ≤ sessionCapBytes := by
  change cliIo.rd (runFiles i) (pathOf StoresGhost.opened.sessions.path name) = .ok bs at hrd
  rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le sessionCapBytes
  · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
    obtain ⟨tl_s, hhead_s⟩ := normalizePath_head_first_char
      (pathStr_pathOf_sessions_first_char name) (by decide) (by decide)
    have hnot_lr : ∀ tl : List Char, (normalizePath p).head? ≠ some (String.ofList ('l' :: tl)) := by
      intro tl hlr; rw [hp_norm, hhead_s] at hlr; injection hlr with h_eq
      have h0 := congrArg (fun s => s.toList.head?) h_eq
      rw [String.toList_ofList, String.toList_ofList, List.head?_cons, List.head?_cons] at h0
      injection h0 with hsl; exact absurd hsl (by decide)
    rcases cliPqInputs_files_cases hi hmem with ⟨st, hwf, hed⟩ | ⟨b, hbun⟩ | ⟨_, hle⟩
    · exact encodeDir_entry_nonBaseKeys_le hwf hSessCap hed hnot_lr
    · have hb := publicBundleOf_files_le_1637 b bundleDir (p, bs) hbun
      dsimp only at hb; unfold sessionCapBytes; omega
    · unfold sessionCapBytes; omega

/-! ## 2. Reachable `M4` Call Domain -/

/-- Reachable `M4` (`run`) call-domain witness. -/
structure CliPqRunDomain (W : PEParams) (g : RunCall) : Prop where
  inputs : CliPqxdhInputs W g.i
  sess_cap : SessionRecordCapInDomain W sessionCapBytes
  stdin_le : g.i.stdin.length ≤ msgCapBytes
  parse_eq : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c

theorem CliPqRunDomain.toSpqrCaps {W : PEParams} {g : RunCall} (hd : CliPqRunDomain W g) :
    CliRunTightSpqrCaps g :=
  cliRunSpqrAndInitCaps_of_cliPqInputs hd.inputs hd.parse_eq
    (cliIo_rd_initBundle_caps_of_cliPqInputs hd.inputs hd.parse_eq)

theorem CliPqRunDomain.ownAddr_le_sessionCap {W : PEParams} {g : RunCall}
    (hd : CliPqRunDomain W g) {bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
      .ok bs) : bs.length ≤ sessionCapBytes :=
  Nat.le_trans (cliIo_rd_ownAddress_le_40_of_cliPqInputs hd.inputs hrd)
    (by unfold sessionCapBytes; decide)

theorem CliPqRunDomain.sessions_le_sessionCap {W : PEParams} {g : RunCall}
    (hd : CliPqRunDomain W g) {name bs : List (BitVec 8)}
    (hrd : StoresGhost.opened.sessions.get cliIo.rd (runFiles g.i) name = .ok bs) :
    bs.length ≤ sessionCapBytes :=
  cliIo_rd_sessions_le_of_cliPqInputs hd.inputs hd.sess_cap hrd

theorem CliPqRunDomain.filesOkPeer_scopeKit {W : PEParams} {g : RunCall} {peer : AddrV}
    (hd : CliPqRunDomain W g) (hpeer : callPeer g.c = some peer) :
    CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer
      CryptoVerification.SignalSession.Cli.Slots.scopeKit (runFiles g.i) (addrValOf peer) :=
  LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile.filesOkPeer_scopeKit_of_cliPqxdhInputs
    hd.inputs hd.parse_eq hpeer

/-- Whole-`run` `PhaseCreditSpec fineCostModel` under `CliPqRunDomain W g`. -/
theorem cliRunOpened_real_1MiB_fine_phaseCredit_of_runDomain
    {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g)) (hd : CliPqRunDomain W g) :
    PhaseCreditSpec fineCostModel (CliRunOpenedEnv cliIo.rd (E g) sessionCapBytes g)
      (cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum)
      (cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive)
      (cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak)
      (cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq) :=
  cliRunOpened_tight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
    fineCostModel_wireLowInterceptHyps SE.toSlotCalleeSpecs sessionCapBytes
    hd.stdin_le (fun _ hrd => hd.ownAddr_le_sessionCap hrd) hd.toSpqrCaps.init_caps

/-- Whole-`run` `PhaseCreditSpec fineCostModel` from `CliPqxdhInputs W g.i`,
`g.i.stdin.length ≤ msgCapBytes`, and `parseArgs = some g.c`. -/
theorem cliRunOpened_real_1MiB_fine_phaseCredit_of_cliPqInputs
    {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (SE : CliRealCalleeFineSpecs (E g))
    (hi : CliPqxdhInputs W g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (CliRunOpenedEnv cliIo.rd (E g) sessionCapBytes g)
      (cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum)
      (cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive)
      (cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
        SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak)
      (cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
        SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq) :=
  cliRunOpened_tight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
    fineCostModel_wireLowInterceptHyps SE.toSlotCalleeSpecs sessionCapBytes
    hstdin
    (fun _ hrd => Nat.le_trans (cliIo_rd_ownAddress_le_40_of_cliPqInputs hi hrd)
      (by unfold sessionCapBytes; decide))
    (cliRunSpqrAndInitCaps_of_cliPqInputs hi hparse
      (cliIo_rd_initBundle_caps_of_cliPqInputs hi hparse)).init_caps

/-! ## 3. Pre-`M4` Setup, Over-Cap Early Exit, and `RealCliMainEnvOf` Envelopes -/

def M2CollectFullEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  M2CollectEnv argvLen evs ∨
  SeqEnv (· = rustAllocEvents 64 8) (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1))) evs

def AddrOptBoundedEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1

def BundleOptBoundedEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1

def BoundedReadStdinEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ (∃ bs : List (BitVec 8), bs.length ≤ msgCapBytes ∧ evs = allocBytes1Events bs) ∨
  SeqEnv (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 8 r)) FreeOnlyEvs evs

def BoundedReadFileEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ (∃ bs : List (BitVec 8), bs.length ≤ sessionCapBytes ∧ evs = allocBytes1Events bs) ∨
  SeqEnv (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) FreeOnlyEvs evs

def M3BoundedSetupEnv (evs : List AllocEvent) : Prop :=
  SeqEnv BoundedReadStdinEnv (SeqEnv BoundedReadFileEnv FreeOnlyEvs) evs

def CliMainBoundedSetupEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (M1PhaseEnv argvLen)
    (SeqEnv (M2CollectFullEnv argvLen)
      (SeqEnv AddrOptBoundedEnv
        (SeqEnv BundleOptBoundedEnv
          (SeqEnv FreeOnlyEvs M3BoundedSetupEnv)))) evs

/-- Post-setup witness when `main` enters `M4` (`run`). -/
structure ValidPostSetupWitness (i : Inputs) where
  g : RunCall
  g_i : g.i = i
  parse_ok : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c
  stdin_le : g.i.stdin.length ≤ msgCapBytes
  dirs : List (List (BitVec 8) × List (List (BitVec 8)))
  dirs_sum_le : (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries
  dirs_bounds : ∀ dn ∈ dirs,
    dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes
  ok : Bool

/-- Unfolded whole-`main` allocator trace predicate on `i : Inputs` over callee slot family `E`. -/
def RealCliMainEnvOf (E : RunCall → CliRunCalleeEnvs) (i : Inputs) (evs : List AllocEvent) : Prop :=
  SeqEnv (CliMainBoundedSetupEnv i.argv.length) (fun evs' =>
    FreeOnlyEvs evs' ∨ ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
      SeqEnv (CliRunOpenedEnv cliIo.rd (E w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs') evs

private theorem seqEnv_of_left_nil {E₁ E₂ : List AllocEvent → Prop} (h1 : E₁ [])
    {evs : List AllocEvent} (h2 : E₂ evs) : SeqEnv E₁ E₂ evs :=
  Or.inr ⟨[], evs, rfl, h1, h2⟩

/-- Unconditional `args.length ≤ 3` whenever `parseArgs` succeeds. -/
theorem args_length_le_3_of_parseArgs_some (uuidParse : UuidParser)
    {args : List (List (BitVec 8))} {c : CallV}
    (h : parseArgs uuidParse args = some c) :
    args.length ≤ 3 := by
  match args with
  | [] => simp [parseArgs] at h
  | [_] => simp [parseArgs] at h
  | [_, _] => simp
  | [_, _, _] => simp
  | _ :: _ :: _ :: _ :: _ => simp [parseArgs] at h

/-- Unconditional `argv.length ≤ 3` whenever `parseArgs` succeeds. -/
theorem argv_length_le_3_of_parseArgs_some (uuidParse : UuidParser) {argv : List String} {c : CallV}
    (h : parseArgs uuidParse (argv.map bytesOfString) = some c) :
    argv.length ≤ 3 := by
  simpa [List.length_map] using args_length_le_3_of_parseArgs_some uuidParse h

theorem addrOptBoundedEnv_nil : AddrOptBoundedEnv [] := Or.inl rfl

theorem addrOptBoundedEnv_of_alloc_le {n : Nat} (hn : n ≤ 16384) :
    AddrOptBoundedEnv (rustAllocEvents n 1) :=
  Or.inr ⟨n, hn, rfl⟩

theorem bundleOptBoundedEnv_nil : BundleOptBoundedEnv [] := Or.inl rfl

theorem bundleOptBoundedEnv_of_alloc_le {n : Nat} (hn : n ≤ 16384) :
    BundleOptBoundedEnv (rustAllocEvents n 1) :=
  Or.inr ⟨n, hn, rfl⟩

theorem addrOptBoundedEnv_of_opt (uuidParse : UuidParser) (addrOpt : Option AddressCall)
    {evs : List AllocEvent}
    (h : (match addrOpt with | none => (· = []) | some ag => AddressEnv uuidParse ag) evs) :
    AddrOptBoundedEnv evs := by
  cases addrOpt with
  | none => exact Or.inl h
  | some ag =>
    dsimp only at h; unfold AddressEnv addressEvents at h
    cases hparse : addrParse uuidParse ag.bs with
    | none => rw [hparse] at h; exact Or.inl h
    | some a =>
      rw [hparse] at h
      exact Or.inr ⟨a.name.length,
        Nat.le_trans (addrParse_name_bounds uuidParse ag.bs hparse).1 (by decide), h⟩

theorem boundedReadStdinEnv_of_readStdinEnv {stdin : List (BitVec 8)}
    (hstdin : stdin.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : ReadStdinEnv stdin evs) : BoundedReadStdinEnv evs := by
  unfold ReadStdinEnv at h; rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨stdin, hstdin, rfl⟩)
  · rw [specCliIoReadSchedule_events_eq 8 stdin.length]; exact Or.inr (Or.inr (Or.inl ⟨stdin.length, rfl⟩))
  · rw [specCliIoReadSchedule_events_eq 8 1048576]
    exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨1048576, rfl⟩, FreeOnlyEvs.singleton 1 1048576⟩))

theorem boundedReadStdinEnv_of_cliIo (r : Nat) {evs : List AllocEvent}
    (h : CliIoReadStdinEnv r evs) : BoundedReadStdinEnv evs := Or.inr (Or.inr (Or.inl ⟨r, h⟩))

theorem boundedReadStdinEnv_of_cliIo_seq_free (r : Nat) {evs : List AllocEvent}
    (h : SeqEnv (CliIoReadStdinEnv r) FreeOnlyEvs evs) : BoundedReadStdinEnv evs :=
  Or.inr (Or.inr (seqEnv_mono (fun _ h1 => ⟨r, h1⟩) (fun _ h2 => h2) h))

/-- Unconditional `BoundedReadFileEnv` from `SpecBudget.ReadFileEnv files path`
(`readViewF` enforces `bs.length ≤ fileCapBytes = sessionCapBytes`). -/
theorem boundedReadFileEnv_of_readFileEnv_any (files : String → Option FsEntry)
    (path : List (BitVec 8)) {evs : List AllocEvent}
    (h : ReadFileEnv files path evs) : BoundedReadFileEnv evs := by
  unfold ReadFileEnv at h; split at h
  · rename_i bs hres
    have hbs_le : bs.length ≤ sessionCapBytes := by
      unfold readFileResult at hres; split at hres
      · cases hres
      · rename_i rbs hrv; injection hres with hbs; subst hbs
        unfold CryptoVerification.SignalSession.CliExt.readViewF at hrv; split at hrv
        · cases hrv
        · injection hrv with hbs; subst hbs; exact Nat.zero_le _
        · split at hrv
          · split at hrv
            · rename_i hle; injection hrv with hbs; subst hbs
              exact Nat.le_trans hle (by unfold fileCapBytes sessionCapBytes; decide)
            · cases hrv
          · cases hrv
          · injection hrv with hbs; subst hbs; exact Nat.zero_le _
    rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr (Or.inl ⟨bs, hbs_le, rfl⟩)
    · exact Or.inl rfl
    · rw [specCliIoReadSchedule_events_eq 9 bs.length]; exact Or.inr (Or.inr (Or.inl ⟨bs.length, rfl⟩))
    · rw [specCliIoReadSchedule_events_eq 9 2097152]
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨2097152, rfl⟩, FreeOnlyEvs.singleton 1 2097152⟩))
  · exact Or.inl h

theorem boundedReadFileEnv_of_readFileEnv_coins {W : PEParams} {i : Inputs}
    (_hi : CliPqxdhInputs W i) {evs : List AllocEvent}
    (h : ReadFileEnv (initFsState (cliInputs i)).files (utf8 "coins") evs) : BoundedReadFileEnv evs :=
  boundedReadFileEnv_of_readFileEnv_any (initFsState (cliInputs i)).files (utf8 "coins") h

/-- Unconditional `BoundedReadFileEnv` from `ReadFileRuleEnv cliIo.rd files path`
(`cliIo_rd_ok_length_le_sessionCapBytes` caps every `.ok bs` at `2 MiB`). -/
theorem boundedReadFileEnv_of_readFileRuleEnv_cliIo (files : FsFiles) (path : List (BitVec 8))
    {evs : List AllocEvent} (h : ReadFileRuleEnv cliIo.rd files path evs) :
    BoundedReadFileEnv evs := by
  unfold ReadFileRuleEnv at h; split at h
  · rename_i bs hrd
    have hbs_le : bs.length ≤ sessionCapBytes :=
      cliIo_rd_ok_length_le_sessionCapBytes files path bs hrd
    rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inr (Or.inl ⟨bs, hbs_le, rfl⟩)
    · exact Or.inl rfl
    · rw [specCliIoReadSchedule_events_eq 9 bs.length]; exact Or.inr (Or.inr (Or.inl ⟨bs.length, rfl⟩))
    · rw [specCliIoReadSchedule_events_eq 9 2097152]
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨2097152, rfl⟩, FreeOnlyEvs.singleton 1 2097152⟩))
  · exact Or.inl h

theorem boundedReadFileEnv_of_cliIo (r : Nat) {evs : List AllocEvent}
    (h : CliIoReadFileEnv r evs) : BoundedReadFileEnv evs := Or.inr (Or.inr (Or.inl ⟨r, h⟩))

theorem m3BoundedSetupEnv_of_m3PhaseEnv_any (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8))
    (hstdin : needStdin = true → stdin.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : M3PhaseEnv needStdin stdin files coinsPath evs) :
    M3BoundedSetupEnv evs :=
  seqEnv_mono (fun _ h1 => by cases needStdin
                              · exact Or.inl h1
                              · exact boundedReadStdinEnv_of_readStdinEnv (hstdin rfl) h1)
    (fun _ h2 => seqEnv_mono (fun _ hrf => boundedReadFileEnv_of_readFileEnv_any files coinsPath hrf)
      (fun _ hf => hf) h2) h

theorem m3BoundedSetupEnv_of_m3PhaseEnv {W : PEParams} {i : Inputs} (_hi : CliPqxdhInputs W i)
    (needStdin : Bool) (hstdin : needStdin = true → i.stdin.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : M3PhaseEnv needStdin i.stdin (initFsState (cliInputs i)).files (utf8 "coins") evs) :
    M3BoundedSetupEnv evs :=
  m3BoundedSetupEnv_of_m3PhaseEnv_any needStdin i.stdin
    (initFsState (cliInputs i)).files (utf8 "coins") hstdin h

theorem m3BoundedSetupEnv_of_m3PhaseCliIoEnv (needStdin : Bool) (stdinLen fileLen : Nat)
    {evs : List AllocEvent} (h : M3PhaseCliIoEnv needStdin stdinLen fileLen evs) : M3BoundedSetupEnv evs :=
  seqEnv_mono (fun _ h1 => by cases needStdin
                              · exact Or.inl h1
                              · exact boundedReadStdinEnv_of_cliIo stdinLen h1)
    (fun _ h2 => seqEnv_mono (fun _ hrf => boundedReadFileEnv_of_cliIo fileLen hrf) (fun _ hf => hf) h2) h

theorem cliMainBoundedSetupEnv_of_setup_any (uuidParse : UuidParser) (i : Inputs)
    (addrOpt : Option AddressCall) (needStdin : Bool)
    (hstdin : needStdin = true → i.stdin.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : CliMainSetupEnv uuidParse i addrOpt needStdin evs) :
    CliMainBoundedSetupEnv i.argv.length evs :=
  Or.inr <| seqEnv_mono (fun _ hm1 => hm1)
    (fun _ hr1 => seqEnv_mono (fun _ hm2 => Or.inl hm2)
      (fun _ hr2 => seqEnv_mono (fun _ had => addrOptBoundedEnv_of_opt uuidParse addrOpt had)
        (fun _ hm3 => seqEnv_of_left_nil bundleOptBoundedEnv_nil
          (seqEnv_of_left_nil (fun _ h => nomatch h)
            (m3BoundedSetupEnv_of_m3PhaseEnv_any needStdin i.stdin
              (initFsState (cliInputs i)).files (utf8 "coins") hstdin hm3))) hr2) hr1) h

theorem cliMainBoundedSetupEnv_of_setup {W : PEParams} {i : Inputs} (_hi : CliPqxdhInputs W i)
    (uuidParse : UuidParser) (addrOpt : Option AddressCall) (needStdin : Bool)
    (hstdin : needStdin = true → i.stdin.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : CliMainSetupEnv uuidParse i addrOpt needStdin evs) :
    CliMainBoundedSetupEnv i.argv.length evs :=
  cliMainBoundedSetupEnv_of_setup_any uuidParse i addrOpt needStdin hstdin h

theorem cliMainBoundedSetupEnv_of_cliIoSetup (uuidParse : UuidParser) (argvLen : Nat)
    (addrOpt : Option AddressCall) (needStdin : Bool) (stdinLen fileLen : Nat)
    {evs : List AllocEvent}
    (h : CliMainSetupCliIoEnv uuidParse argvLen addrOpt needStdin stdinLen fileLen evs) :
    CliMainBoundedSetupEnv argvLen evs :=
  Or.inr <| seqEnv_mono (fun _ hm1 => hm1)
    (fun _ hr1 => seqEnv_mono (fun _ hm2 => Or.inl hm2)
      (fun _ hr2 => seqEnv_mono (fun _ had => addrOptBoundedEnv_of_opt uuidParse addrOpt had)
        (fun _ hm3 => seqEnv_of_left_nil bundleOptBoundedEnv_nil
          (seqEnv_of_left_nil (fun _ h => nomatch h)
            (m3BoundedSetupEnv_of_m3PhaseCliIoEnv needStdin stdinLen fileLen hm3))) hr2) hr1) h

/-- Early-exit lift (`argv = []`, `parseArgs = none`, `M3` `stdin > 1 MiB` → exit `2`, `"coins"`
error, `IsSendOverCap` → exit `1`) with zero `run`-entry preconditions. -/
theorem realCliMainEnvOf_of_setup_earlyExit (E : RunCall → CliRunCalleeEnvs) (i : Inputs)
    {evs : List AllocEvent} (h : SeqEnv (CliMainBoundedSetupEnv i.argv.length) FreeOnlyEvs evs) :
    RealCliMainEnvOf E i evs :=
  seqEnv_mono (fun _ hs => hs) (fun _ hf => Or.inl hf) h

/-- Standard `CliMainEnv` lift into `RealCliMainEnvOf E g.i`. -/
theorem realCliMainEnvOf_of_cliMainEnv {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (hi : CliPqxdhInputs W g.i) (uuidParse : UuidParser) (addrOpt : Option AddressCall)
    (needStdin : Bool) (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) (ok : Bool)
    (hrun_guard : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
      g.i.stdin.length ≤ msgCapBytes ∧ (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {evs : List AllocEvent}
    (h : CliMainEnv uuidParse (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
      g addrOpt needStdin dirs ok evs) :
    RealCliMainEnvOf E g.i evs :=
  seqEnv_mono
    (fun _ hs => cliMainBoundedSetupEnv_of_setup hi uuidParse addrOpt needStdin
      (fun _ => hrun_guard.2.1) hs)
    (fun _ htail => match htail with
      | Or.inl hf => Or.inl hf
      | Or.inr hrun => Or.inr ⟨⟨g, rfl, hrun_guard.1, hrun_guard.2.1, dirs,
          hrun_guard.2.2.1, hrun_guard.2.2.2, ok⟩, rfl, hrun⟩) h

/-- Standard `CliMainCliIoEnv` lift into `RealCliMainEnvOf E g.i`. -/
theorem realCliMainEnvOf_of_cliMainCliIoEnv {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    (uuidParse : UuidParser) (addrOpt : Option AddressCall) (needStdin : Bool) (stdinLen fileLen : Nat)
    (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) (ok : Bool)
    (hrun_guard : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c ∧
      g.i.stdin.length ≤ msgCapBytes ∧ (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {evs : List AllocEvent}
    (h : CliMainCliIoEnv uuidParse (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
      g addrOpt needStdin stdinLen fileLen dirs ok evs) :
    RealCliMainEnvOf E g.i evs :=
  seqEnv_mono
    (fun _ hs => cliMainBoundedSetupEnv_of_cliIoSetup uuidParse g.i.argv.length
      addrOpt needStdin stdinLen fileLen hs)
    (fun _ htail => match htail with
      | Or.inl hf => Or.inl hf
      | Or.inr hrun => Or.inr ⟨⟨g, rfl, hrun_guard.1, hrun_guard.2.1, dirs,
          hrun_guard.2.2.1, hrun_guard.2.2.2, ok⟩, rfl, hrun⟩) h

/-! ## 4. `PhaseCreditSpec`, `PhaseGroupSpec`, and Whole-`main` `FitsTrace` / `FitsEnv` -/

private theorem m2CollectFull_phaseCredit_fine {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec fineCostModel (M2CollectFullEnv argvLen) 29001 0 0 64 := by
  have hM := fineCostModel_modelHyps
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have halloc64 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 8) (2 * 64 + 9539) 0 0 64 :=
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 64) (al := 8) (by decide) hsm64).mono
      (hM.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  have hstep : ∀ k ∈ List.range' 1 (argvLen - 1),
      PhaseCreditSpec fineCostModel (M2CollectStepEnv k) 9667 0 0 64 := by
    intro k hk; rw [List.mem_range'] at hk; obtain ⟨i, _, rfl⟩ := hk
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have hcap : reserveCapStride 16 1 1 1 = 4 := by decide
      unfold M2CollectStepEnv; rw [hcap]
      exact ((PhaseCreditSpec.nil fineCostModel).or
        (phaseCredit_rustRealloc_small_any hM (old := 16 * 1) (new := 16 * 4) (al := 8)
          (by decide) (by decide) (by omega) (by omega))).mono
        (by decide) (by decide) (by decide) (by decide)
    · have hcap : reserveCapStride 16 2 2 1 = 4 := by decide
      unfold M2CollectStepEnv; rw [hcap]
      exact ((PhaseCreditSpec.nil fineCostModel).or
        (phaseCredit_rustRealloc_small_any hM (old := 16 * 2) (new := 16 * 4) (al := 8)
          (by decide) (by decide) (by omega) (by omega))).mono
        (by decide) (by decide) (by decide) (by decide)
  have hiter : PhaseCreditSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1))) ((argvLen - 1) * 9667) 0 0 64 := by
    simpa only [List.length_range'] using PhaseCreditSpec.iter_zero_live (M := fineCostModel)
      (Step := M2CollectStepEnv) (c := 9667) (p := 0) (r := 64) (List.range' 1 (argvLen - 1)) hstep
  exact ((phaseCredit_m2Collect_small64 hM hsm64 hargv).or (halloc64.seq hiter)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem m2CollectFull_fine_groupSpec {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseGroupSpec fineCostModel (M2CollectFullEnv argvLen) (3 * (3 * FineScale)) := by
  have h1 := (m2CollectEnv_groupSpec fineCostModel argvLen).mono
    (Nat.mul_le_mul_right (3 * FineScale) hargv)
  have hiter : PhaseGroupSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1)))
      ((argvLen - 1) * (3 * FineScale)) := by
    simpa only [List.length_range'] using PhaseGroupSpec.iterSeq_const (M := fineCostModel)
      (Step := M2CollectStepEnv) (3 * FineScale) (List.range' 1 (argvLen - 1))
      (fun k _ => m2CollectStepEnv_groupSpec fineCostModel k)
  refine (h1.or ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 8).seq hiter)).mono ?_
  have hc : (argvLen - 1) * (3 * FineScale) ≤ 2 * (3 * FineScale) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold FineScale at hc ⊢; omega

private theorem optAlloc16384_phaseCredit_fine :
    PhaseCreditSpec fineCostModel
      (fun evs => evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1)
      42307 0 0 16384 := by
  have halloc (n : Nat) (hn : n ≤ 16384) :
      PhaseCreditSpec fineCostModel (· = rustAllocEvents n 1) 42307 0 0 16384 := by
    have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (Nat.le_trans (fineCostModel_modelHyps.smallAlloc_le hsm) (by omega))
      (Nat.le_refl 0) (Nat.le_refl 0) hn
  have h1 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1) 42307 0 0 16384 :=
    { req_align := fun evs ⟨n, hn, he⟩ ev hev => (halloc n hn).req_align evs he ev hev
      credit_le := fun st0 {_} ⟨n, hn, he⟩ => (halloc n hn).credit_le st0 he }
  exact ((PhaseCreditSpec.nil fineCostModel).or h1).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem addrOptBounded_phaseCredit_fine :
    PhaseCreditSpec fineCostModel AddrOptBoundedEnv 42307 0 0 16384 :=
  optAlloc16384_phaseCredit_fine

private theorem bundleOptBounded_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BundleOptBoundedEnv 42307 0 0 16384 :=
  optAlloc16384_phaseCredit_fine

private theorem optAlloc16384_fine_groupSpec :
    PhaseGroupSpec fineCostModel
      (fun evs => evs = [] ∨ ∃ n : Nat, n ≤ 16384 ∧ evs = rustAllocEvents n 1)
      (3 * FineScale) where
  groups_le st0 {_} h := by
    rcases h with rfl | ⟨n, _, rfl⟩
    · simp [AllocCostModel.stepEvents_nil]
    · exact (PhaseGroupSpec.rustAlloc_any fineCostModel n 1).groups_le st0 rfl

private theorem addrOptBounded_fine_groupSpec :
    PhaseGroupSpec fineCostModel AddrOptBoundedEnv (3 * FineScale) :=
  optAlloc16384_fine_groupSpec

private theorem bundleOptBounded_fine_groupSpec :
    PhaseGroupSpec fineCostModel BundleOptBoundedEnv (3 * FineScale) :=
  optAlloc16384_fine_groupSpec

private theorem fine_sm_bounds :
    131072 ≤ HasFineReallocCredit.smallMaxReq fineCostModel ∧
    HasFineReallocCredit.smallMaxReq fineCostModel < 262144 := by
  rw [fineCostModel_smallMaxReq_eq]; decide

private theorem allocBytes1_bounded_phaseCredit_fine (cap cum live peak req : Nat)
    (hc : 533825 ≤ cum) (hl : cap + 8195 ≤ live) (hp : cap + 8195 ≤ peak) (hr : cap ≤ req) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ cap ∧ evs = allocBytes1Events bs)
      cum live peak req where
  req_align evs := fun ⟨bs, hbs, he⟩ ev hev =>
    ((phaseCredit_allocBytes1_tight fineCostModel_modelHyps fine_sm_bounds.2 bs hbs).mono
      hc hl hp hr).req_align evs he ev hev
  credit_le st0 {_} := fun ⟨bs, hbs, he⟩ =>
    ((phaseCredit_allocBytes1_tight fineCostModel_modelHyps fine_sm_bounds.2 bs hbs).mono
      hc hl hp hr).credit_le st0 he

private theorem boundedReadStdin_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BoundedReadStdinEnv readStdinDeltaCum_tight
      (readStdinDeltaLive msgCapBytes) (readStdinDeltaPeak msgCapBytes)
      (readStdinMaxReq msgCapBytes) := by
  have hM := fineCostModel_modelHyps
  have h1 := allocBytes1_bounded_phaseCredit_fine msgCapBytes readStdinDeltaCum_tight
    (readStdinDeltaLive msgCapBytes) (readStdinDeltaPeak msgCapBytes) (readStdinMaxReq msgCapBytes)
    (by unfold readStdinDeltaCum_tight; decide) (by unfold readStdinDeltaLive msgCapBytes; decide)
    (by unfold readStdinDeltaPeak msgCapBytes; decide) (by unfold readStdinMaxReq msgCapBytes; decide)
  have hcap_raw : PhaseCreditSpec fineCostModel
      (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 8 r)) 573696 1056771 1589254 1048576 :=
    PhaseCreditSpec.of_imp (fun _ ⟨r, he⟩ => ⟨r, he⟩)
      (phaseCreditSpec_cliIoReadStdin_anyR_tight hM fine_sm_bounds.1 fine_sm_bounds.2)
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (h1.or (hcap_raw.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)))).mono
    (by unfold readStdinDeltaCum_tight; decide) (by unfold readStdinDeltaLive msgCapBytes; decide)
    (by unfold readStdinDeltaPeak msgCapBytes; decide) (by unfold readStdinMaxReq msgCapBytes; decide)

private theorem boundedReadFile_phaseCredit_fine :
    PhaseCreditSpec fineCostModel BoundedReadFileEnv readFileDeltaCum_tight
      (max (sessionCapBytes + 8195) (2097152 + 8195))
      (max (sessionCapBytes + 8195) 3162118) (max sessionCapBytes 2097152) := by
  have hM := fineCostModel_modelHyps
  have h1 := allocBytes1_bounded_phaseCredit_fine sessionCapBytes readFileDeltaCum_tight
    (max (sessionCapBytes + 8195) (2097152 + 8195))
    (max (sessionCapBytes + 8195) 3162118) (max sessionCapBytes 2097152)
    (by unfold readFileDeltaCum_tight; decide)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hcap_raw : PhaseCreditSpec fineCostModel
      (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 573818 2105347 3162118 2097152 :=
    PhaseCreditSpec.of_imp (fun _ ⟨r, he⟩ => ⟨r, he⟩)
      (phaseCreditSpec_cliIoReadFile_anyR_tight hM fine_sm_bounds.1 fine_sm_bounds.2)
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (h1.or (hcap_raw.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)))).mono
    (by unfold readFileDeltaCum_tight; decide) (by unfold sessionCapBytes; decide)
    (by unfold sessionCapBytes; decide) (by unfold sessionCapBytes; decide)

private theorem m3BoundedSetup_phaseCredit_fine :
    PhaseCreditSpec fineCostModel M3BoundedSetupEnv m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) :=
  (boundedReadStdin_phaseCredit_fine.seq
    (boundedReadFile_phaseCredit_fine.seq
      (PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc))).mono
    (by unfold m3PhaseDeltaCum_tight readStdinDeltaCum_tight readFileDeltaCum_tight; decide)
    (by unfold m3PhaseDeltaLive readStdinDeltaLive msgCapBytes sessionCapBytes; decide)
    (by unfold m3PhaseDeltaPeak readStdinDeltaPeak readStdinDeltaLive msgCapBytes sessionCapBytes
        decide)
    (by unfold m3PhaseMaxReq readStdinMaxReq msgCapBytes sessionCapBytes; decide)

private theorem allocBytes1_bounded_fine_groupSpec (cap grp : Nat) (hgrp : 3 * FineScale ≤ grp) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ cap ∧ evs = allocBytes1Events bs) grp where
  groups_le st0 {_} := fun ⟨bs, _, hevs⟩ => by
    subst hevs; unfold allocBytes1Events; split
    · simp [AllocCostModel.stepEvents_nil]
    · exact Nat.le_trans
        ((PhaseGroupSpec.rustAlloc_any fineCostModel bs.length 1).groups_le st0 rfl)
        (Nat.add_le_add_left hgrp _)

private theorem boundedReadStdin_fine_groupSpec :
    PhaseGroupSpec fineCostModel BoundedReadStdinEnv (27 * FineScale) := by
  have h1 := allocBytes1_bounded_fine_groupSpec msgCapBytes (27 * FineScale)
    (by unfold FineScale; decide)
  have hnf : NonFreeBound (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 8 r)) 9 :=
    fun _ ⟨r, hr⟩ => hr ▸ cliIoReadStdinEnv_nonFreeBound r _ rfl
  exact ((PhaseGroupSpec.nil fineCostModel).or
    (h1.or ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by unfold FineScale; decide)

private theorem boundedReadFile_fine_groupSpec :
    PhaseGroupSpec fineCostModel BoundedReadFileEnv (30 * FineScale) := by
  have h1 := allocBytes1_bounded_fine_groupSpec sessionCapBytes (30 * FineScale)
    (by unfold FineScale; decide)
  have hnf : NonFreeBound (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 10 :=
    fun _ ⟨r, hr⟩ => hr ▸ cliIoReadFileEnv_nonFreeBound r _ rfl
  exact ((PhaseGroupSpec.nil fineCostModel).or
    (h1.or ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by unfold FineScale; decide)

/-- Tight `fineCostModel` widened setup group bound (`argvLen ≤ 3`, `AddrOpt` + `BundleOpt` `≤ 16384`). -/
def cliMainWidenedSetupFineGrpS : Nat :=
  24623 + 72 * FineScale

/-- Closed-form whole-`main` `Δcum` with widened `16384`-B `AddrOpt`/`BundleOpt` setup (`123,250` B pre-`M3`). -/
def cliMainWidenedCumOf (runCumCap : Nat) : Nat :=
  123250 + m3PhaseDeltaCum_tight + runCumCap +
    cliMaxDirtyEntries * (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

/-- Closed-form whole-`main` scaled group count `grpS` with widened setup. -/
def cliMainWidenedGrpSOf (runGrpSCap : Nat) : Nat :=
  cliMainWidenedSetupFineGrpS + runGrpSCap + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

/-- Closed-form whole-`main` integer group ceiling `(grpS + FineScale - 1) / FineScale` with widened setup. -/
def cliMainWidenedGrpCountOf (runGrpSCap : Nat) : Nat :=
  (cliMainWidenedGrpSOf runGrpSCap + FineScale - 1) / FineScale

/-- Closed-form whole-`main` `stepReserve` with widened setup. -/
def cliMainWidenedStepReserveOf (runReqCap runGrpSCap : Nat) : Nat :=
  fineStepReserveOfGroups (cliMainTightReqOf runReqCap) 16 (cliMainWidenedGrpCountOf runGrpSCap)

/-- Set-A (`cliRealRunReqCap`, `cliRealRunGrpSCap`) whole-`main` `stepReserve` with widened setup. -/
def cliRealWidenedMainStepReserve : Nat :=
  cliMainWidenedStepReserveOf cliRealRunReqCap cliRealRunGrpSCap

private theorem cliMainBoundedSetup_phaseCredit_fine {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec fineCostModel (CliMainBoundedSetupEnv argvLen)
      (123250 + m3PhaseDeltaCum_tight) (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes)) := by
  have hM := fineCostModel_modelHyps
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  exact ((PhaseCreditSpec.freeOnly hM.freeNonInc).or
    ((phaseCredit_m1Phase_small64 hM hsm64 hargv).seq
      ((m2CollectFull_phaseCredit_fine hargv).seq
        (addrOptBounded_phaseCredit_fine.seq
          (bundleOptBounded_phaseCredit_fine.seq
            ((PhaseCreditSpec.freeOnly hM.freeNonInc).seq m3BoundedSetup_phaseCredit_fine)))))).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem cliMainBoundedSetup_fine_groupSpec {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseGroupSpec fineCostModel (CliMainBoundedSetupEnv argvLen) cliMainWidenedSetupFineGrpS := by
  have hm3 : PhaseGroupSpec fineCostModel M3BoundedSetupEnv (57 * FineScale) :=
    (boundedReadStdin_fine_groupSpec.seq
      (boundedReadFile_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
      (by unfold FineScale; decide)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((m1PhaseEnv_le_3_fine_groupSpec hargv).seq
      ((m2CollectFull_fine_groupSpec hargv).seq
        (addrOptBounded_fine_groupSpec.seq
          (bundleOptBounded_fine_groupSpec.seq
            ((PhaseGroupSpec.freeOnly fineCostModel).seq hm3)))))).mono
    (by unfold cliMainWidenedSetupFineGrpS FineScale; decide)

/-! ### `argvLen ≤ 1820` Unconditional Setup and Early-Exit Bounds -/

private theorem reserveCapStride_16_bounds_lt_1820 {k : Nat} (hk : k < 1820) :
    4 ≤ reserveCapStride 16 k k 1 ∧ reserveCapStride 16 k k 1 ≤ 3638 := by
  have hm : reserveMinCap 16 = 4 := rfl
  unfold reserveCapStride
  rw [hm]
  omega

theorem m1Phase_phaseCredit_le1820 {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    PhaseCreditSpec fineCostModel (M1PhaseEnv argvLen) 67779 0 0 29120 := by
  have hM := fineCostModel_modelHyps
  have hle : 16 * argvLen ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have hsa := hM.smallAlloc_le hle
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 16 * argvLen) (al := 8)
      (by decide) hle)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem m2CollectFull_phaseCredit_le1820 {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    PhaseCreditSpec fineCostModel (M2CollectFullEnv argvLen) 229238100 0 0 58208 := by
  have hM := fineCostModel_modelHyps
  have hsm_eq := fineCostModel_smallMaxReq_eq
  have hstep_lt : ∀ k : Nat, k < 1820 →
      PhaseCreditSpec fineCostModel (M2CollectStepEnv k) 125955 0 0 58208 := by
    intro k hk
    obtain ⟨hc4, hc_hi⟩ := reserveCapStride_16_bounds_lt_1820 hk
    have hold : 16 * k ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by omega
    have hnew : 16 * reserveCapStride 16 k k 1 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by omega
    exact ((PhaseCreditSpec.nil fineCostModel).or
      (phaseCredit_rustRealloc_small_any hM (old := 16 * k)
        (new := 16 * reserveCapStride 16 k k 1) (al := 8)
        (by decide) (by omega) hold hnew)).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  have hit1 : PhaseCreditSpec fineCostModel (M2CollectEnv argvLen)
      (argvLen * 125955) 0 0 58208 := by
    unfold M2CollectEnv
    simpa only [List.length_range] using PhaseCreditSpec.iter_zero_live (M := fineCostModel)
      (Step := M2CollectStepEnv) (c := 125955) (p := 0) (r := 58208) (List.range argvLen)
      (fun k hk => hstep_lt k (Nat.lt_of_lt_of_le (List.mem_range.mp hk) hargv))
  have halloc64 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 8) 9667 0 0 64 := by
    have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by omega
    exact (PhaseCreditSpec.rustAlloc_small_any hM (req := 64) (al := 8) (by decide) hsm64).mono
      (Nat.le_trans (hM.smallAlloc_le hsm64) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  have hit2 : PhaseCreditSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1)))
      ((argvLen - 1) * 125955) 0 0 58208 := by
    simpa only [List.length_range'] using PhaseCreditSpec.iter_zero_live (M := fineCostModel)
      (Step := M2CollectStepEnv) (c := 125955) (p := 0) (r := 58208)
      (List.range' 1 (argvLen - 1))
      (fun k hk => by
        rw [List.mem_range'] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        simpa only [Nat.one_mul] using hstep_lt (1 + j) (by omega))
  exact (hit1.or (halloc64.seq hit2)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem m2CollectFull_fine_groupSpec_le1820 {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    PhaseGroupSpec fineCostModel (M2CollectFullEnv argvLen) (5463 * FineScale) := by
  have h1 := (m2CollectEnv_groupSpec fineCostModel argvLen).mono
    (Nat.mul_le_mul_right (3 * FineScale) hargv)
  have hiter : PhaseGroupSpec fineCostModel
      (IterSeqEnv M2CollectStepEnv (List.range' 1 (argvLen - 1)))
      ((argvLen - 1) * (3 * FineScale)) := by
    simpa only [List.length_range'] using PhaseGroupSpec.iterSeq_const (M := fineCostModel)
      (Step := M2CollectStepEnv) (3 * FineScale) (List.range' 1 (argvLen - 1))
      (fun k _ => m2CollectStepEnv_groupSpec fineCostModel k)
  refine (h1.or ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 8).seq hiter)).mono ?_
  have hc1 : argvLen * (3 * FineScale) ≤ 1820 * (3 * FineScale) :=
    Nat.mul_le_mul_right _ hargv
  have hc2 : (argvLen - 1) * (3 * FineScale) ≤ 1820 * (3 * FineScale) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold FineScale at hc1 hc2 ⊢; omega

/-- Unconditional `PhaseCreditSpec fineCostModel` for `CliMainBoundedSetupEnv argvLen` across all
`argvLen ≤ 1820` (`STACK_ARG_MAX` / `CliInputsOk`). -/
theorem cliMainBoundedSetup_phaseCredit_le1820 {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    PhaseCreditSpec fineCostModel (CliMainBoundedSetupEnv argvLen)
      (229390493 + m3PhaseDeltaCum_tight)
      (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) := by
  have hM := fineCostModel_modelHyps
  have h58 : max 58208 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
      m3PhaseMaxReq msgCapBytes sessionCapBytes := by
    unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
  exact ((PhaseCreditSpec.freeOnly hM.freeNonInc).or
    ((m1Phase_phaseCredit_le1820 hargv).seq
      ((m2CollectFull_phaseCredit_le1820 hargv).seq
        (addrOptBounded_phaseCredit_fine.seq
          (bundleOptBounded_phaseCredit_fine.seq
            ((PhaseCreditSpec.freeOnly hM.freeNonInc).seq m3BoundedSetup_phaseCredit_fine)))))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Unconditional `PhaseGroupSpec fineCostModel` for `CliMainBoundedSetupEnv argvLen` across all
`argvLen ≤ 1820`. -/
theorem cliMainBoundedSetup_fine_groupSpec_le1820 {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    PhaseGroupSpec fineCostModel (CliMainBoundedSetupEnv argvLen) (5529 * FineScale) := by
  have hm3 : PhaseGroupSpec fineCostModel M3BoundedSetupEnv (57 * FineScale) :=
    (boundedReadStdin_fine_groupSpec.seq
      (boundedReadFile_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
      (by unfold FineScale; decide)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((m1PhaseEnv_groupSpec fineCostModel argvLen).seq
      ((m2CollectFull_fine_groupSpec_le1820 hargv).seq
        (addrOptBounded_fine_groupSpec.seq
          (bundleOptBounded_fine_groupSpec.seq
            ((PhaseGroupSpec.freeOnly fineCostModel).seq hm3)))))).mono
    (by unfold FineScale; decide)

private theorem cliMainSetupEarlyExit_90pct_bounds :
    m3PhaseDeltaLive msgCapBytes sessionCapBytes ≤
      m3PhaseDeltaPeak msgCapBytes sessionCapBytes ∧
    cliDecoupledRamNeed cliDefaultStaticBytes
      (229390493 + m3PhaseDeltaCum_tight)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) 5529 ≤ cliRealNinetyPctOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      (229390493 + m3PhaseDeltaCum_tight)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) 5529 ≤ 2 ^ 48 :=
  ⟨by decide, by decide, by decide⟩

/-- Unconditional `< 90%` (`≤ 966,367,641` B) early-exit `FitsEnv fineCostModel` across all
`argvLen ≤ 1820`. -/
theorem cliMainSetupEarlyExit_90pct_fitsEnv_le1820 {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    FitsEnv fineCostModel lim fineCostModel.init
      (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs) := by
  obtain ⟨hlp, hram0, hva0⟩ := cliMainSetupEarlyExit_90pct_bounds
  have hSpec : PhaseCreditSpec fineCostModel
      (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs)
      (229390493 + m3PhaseDeltaCum_tight)
      (m3PhaseDeltaLive msgCapBytes sessionCapBytes)
      (m3PhaseDeltaPeak msgCapBytes sessionCapBytes)
      (m3PhaseMaxReq msgCapBytes sessionCapBytes) :=
    ((cliMainBoundedSetup_phaseCredit_le1820 hargv).seq
      (PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hGrp := ((cliMainBoundedSetup_fine_groupSpec_le1820 hargv).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact fitsEnv_fineCostModel_of_group_literal_bounds hSpec hGrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _)
    (by unfold FineScale; decide) henf
    (Nat.le_trans (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap90))
    (Nat.le_trans (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0)

/-- Unconditional `≤ 1 GiB` early-exit `FitsEnv fineCostModel` across all `argvLen ≤ 1820`. -/
theorem cliMainSetupEarlyExit_fitsEnv_le1820 {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    {argvLen : Nat} (hargv : argvLen ≤ 1820) :
    FitsEnv fineCostModel lim fineCostModel.init
      (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs) :=
  cliMainSetupEarlyExit_90pct_fitsEnv_le1820 henf hsb hsc
    (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) hargv

/-- Closed `cliBudgetLimits` (`1 GiB`) early-exit `FitsEnv fineCostModel` across all `argvLen ≤ 1820`. -/
theorem cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 :
    ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs) :=
  fun _ hargv =>
    cliMainSetupEarlyExit_90pct_fitsEnv_le1820 rfl (Nat.le_refl _) (Nat.le_refl _)
      (by unfold cliBudgetLimits cliRealNinetyPctOneGiB cliOneGiB; decide) hargv

/-- Closed `cliBudgetLimits` (`1 GiB`) setup `FitsEnv fineCostModel` across all `argvLen ≤ 1820`. -/
theorem cliMainBoundedSetup_fitsEnv_cliBudgetLimits_le1820 :
    ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (CliMainBoundedSetupEnv argvLen) :=
  fun argvLen hargv evs hs =>
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 argvLen hargv evs (Or.inl hs)

private theorem m5Phase_Bounded_phaseCredit_fine
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))}
    (hsum : (dirs.map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries)
    (hdirs : ∀ dn ∈ dirs,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    PhaseCreditSpec fineCostModel (M5PhaseEnv dirs)
      (cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539))
      0 (m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes)
      (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes) := by
  have hM := fineCostModel_modelHyps
  have hit : PhaseCreditSpec fineCostModel (IterSeqEnv (fun dn => M5DirStepEnv dn.1 dn.2) dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539))
      0 (m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes)
      (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes) := by
    clear hsum; induction dirs with
    | nil =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | cons dn dns ih =>
      obtain ⟨hd1, hd2⟩ := hdirs dn List.mem_cons_self
      refine ((m5DirStep_phaseCredit hM hd1 hd2).seq
        (ih (fun d hd => hdirs d (List.mem_cons_of_mem dn hd)))).mono ?_ (Nat.le_refl 0) ?_ ?_
      · simp only [List.map_cons, List.sum_cons, Nat.add_mul]; exact Nat.le_refl _
      · rw [Nat.zero_add]; exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
      · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine (hit.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ (Nat.le_refl 0) ?_ ?_
  · rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hsum
  · rw [Nat.zero_add]; exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

private theorem max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem max4_le {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    max a1 (max b1 (max c1 d1)) ≤ max a2 (max b2 (max c2 d2)) :=
  max_mono ha (max_mono hb (max_mono hc hd))

private theorem cliRealRun_bounds_of_caps {EC : CliRunCalleeEnvs} {SE : CliRealCalleeFineSpecs EC}
    (hCaps : CliRealR2CalleeCaps SE) :
    cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRealRunCumCap ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRealRunLiveCap ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤ cliRealRunPeakCap ∧
    cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
      SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤ cliRealRunReqCap ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ cliRealRunGrpSCap := by
  rcases hCaps with
    ⟨hic, hil, hip, hir, hig, hec, hel, hep, her, heg,
     hsc, hsl, hsp, hsr, hsg, hkc, hkl, hkp, hkr, hkg, hpc, hpl, hpp, hpr, hpg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cliRun1MiBCustomPksmCum, cliRealRunCumCap, CliRunArmsPeak.initArmDeltaCum,
      CliRunArmsPeak.r2TightDeltaCum]
    exact Nat.add_le_add_left (max4_le (by omega) (by omega) (by omega) (by omega)) _
  · simp only [cliRun1MiBCustomPksmLive, cliRealRunLiveCap, CliRunPeakSpec.cliRun1MiBSlotLive,
      CliTopBudgetReal.cliRealPksmLiveCap, CliRunArmsPeak.initArmDeltaLive,
      CliRunArmsPeak.r2DeltaLive] at hkl ⊢
    exact Nat.add_le_add_left (max4_le (by omega) (by omega) (by omega) (by omega)) _
  · unfold cliRun1MiBCustomPksmPeak cliRealRunPeakCap CliRunPeakSpec.cliRun1MiBSlotPeak
      CliRunArmsPeak.initArmDeltaPeak CliRunArmsPeak.r2DeltaPeak
    unfold CliTopBudgetReal.cliRealPksmLiveCap at hkl
    unfold CliTopBudgetReal.cliRealPksmPeakCap at hkp
    exact max_mono (Nat.le_refl _) (Nat.add_le_add_left (max4_le
      (max_mono (Nat.le_refl _) (Nat.add_le_add_left
        (max_mono (Nat.le_refl _) (Nat.add_le_add_left hip _)) _))
      (max_mono hep (Nat.add_le_add_right hel _))
      (max_mono (Nat.le_refl _) (Nat.add_le_add_left hsp _))
      (max_mono hkp (Nat.add_le_add hkl hpp))) _)
  · unfold cliRun1MiBCustomPksmMaxReq cliRealRunReqCap CliRunPeakSpec.cliRun1MiBSlotMaxReq
      CliRunArmsPeak.initArmMaxReq CliRunArmsPeak.r2MaxReq
    unfold CliTopBudgetReal.cliRealPksmReqCap at hkr
    exact max_mono (Nat.le_refl _) (max4_le
      (max_mono (Nat.le_refl _) (max_mono (Nat.le_refl _) hir))
      (max_mono her (Nat.le_refl _)) (max_mono (Nat.le_refl _) hsr) (max_mono hkr hpr))
  · unfold cliRunOpenedCustomPksmGrpS cliRealRunGrpSCap
    exact Nat.add_le_add_left (max4_le
      (Nat.add_le_add_left hig _) (Nat.add_le_add_right heg _)
      (Nat.add_le_add_left hsg _) (Nat.add_le_add hkg hpg)) _

/-- Whole-`main` `PhaseCreditSpec fineCostModel` on `RealCliMainEnvOf E i`. -/
theorem realCliMainEnvOf_phaseCredit_fine {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {i : Inputs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) (hi : CliPqxdhInputs W i) :
    PhaseCreditSpec fineCostModel (RealCliMainEnvOf E i)
      (cliMainWidenedCumOf cliRealRunCumCap) (cliMainTightLiveOf cliRealRunLiveCap)
      (cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap)
      (cliMainTightReqOf cliRealRunReqCap) := by
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunOpenedEnv cliIo.rd (E w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliRealRunCumCap + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealRunLiveCap
      (max cliRealRunPeakCap
        (cliRealRunLiveCap + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealRunReqCap (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hd : CliPqRunDomain W w.g := ⟨w.g_i.symm ▸ hi, hSessCap, w.stdin_le, w.parse_ok⟩
    obtain ⟨h1, h2, h3, h4, _⟩ := cliRealRun_bounds_of_caps (hSlots w.g hd)
    have hrun := (cliRunOpened_real_1MiB_fine_phaseCredit_of_runDomain (SE w.g hd) hd).mono
      h1 h2 h3 h4
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunOpenedEnv cliIo.rd (E w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealRunCumCap + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealRunLiveCap
      (max cliRealRunPeakCap
        (cliRealRunLiveCap + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealRunReqCap (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have htail := ((PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc).or hex).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    ?_ ?_ ?_ ?_
  · unfold cliMainWidenedCumOf; simp only [Nat.add_assoc]; exact Nat.le_refl _
  · unfold cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
  · unfold cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
  · unfold cliMainTightReqOf cliMainMaxReq
    have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
        m3PhaseMaxReq msgCapBytes sessionCapBytes := by
      unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
    rw [h16k]

/-- Whole-`main` `PhaseGroupSpec fineCostModel` on `RealCliMainEnvOf E i`. -/
theorem realCliMainEnvOf_fine_groupSpec {W : PEParams} {E : RunCall → CliRunCalleeEnvs} {i : Inputs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) (hi : CliPqxdhInputs W i) :
    PhaseGroupSpec fineCostModel (RealCliMainEnvOf E i) (cliMainWidenedGrpSOf cliRealRunGrpSCap) := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunOpenedEnv cliIo.rd (E w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealRunGrpSCap + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hd : CliPqRunDomain W w.g := ⟨w.g_i.symm ▸ hi, hSessCap, w.stdin_le, w.parse_ok⟩
        obtain ⟨_, _, _, _, h5⟩ := cliRealRun_bounds_of_caps (hSlots w.g hd)
        have hrun := (cliRunOpened_real_fine_groupSpec (wireOutCap := sessionCapBytes)
          (SE w.g hd) w.stdin_le).mono h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunOpenedEnv cliIo.rd (E w.g) sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliRealRunGrpSCap + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono (by omega)
        exact htot.groups_le st0 hseq }
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or hex).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    (by unfold cliMainWidenedGrpSOf; omega)

private theorem cliRealWidened_90pct_literals :
    cliDecoupledRamNeed cliDefaultStaticBytes (cliMainWidenedCumOf cliRealRunCumCap)
      (cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap) (cliMainTightReqOf cliRealRunReqCap)
      (cliMainWidenedGrpCountOf cliRealRunGrpSCap) ≤ cliRealNinetyPctOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount (cliMainWidenedCumOf cliRealRunCumCap)
      (cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap) (cliMainTightReqOf cliRealRunReqCap)
      (cliMainWidenedGrpCountOf cliRealRunGrpSCap) ≤ 2 ^ 48 :=
  ⟨by decide, by decide⟩

private theorem realCliMainEnvOf_90pct_bounds {lim : BudgetLimits}
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap) :
    cliMainTightLiveOf cliRealRunLiveCap ≤ cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap ∧
    cliDecoupledRamNeed lim.staticBytes (cliMainWidenedCumOf cliRealRunCumCap)
      (cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap) (cliMainTightReqOf cliRealRunReqCap)
      (cliMainWidenedGrpCountOf cliRealRunGrpSCap) ≤ lim.physCap ∧
    cliDecoupledVaNeed lim.staticBytes lim.staticCount (cliMainWidenedCumOf cliRealRunCumCap)
      (cliMainTightPeakOf cliRealRunLiveCap cliRealRunPeakCap) (cliMainTightReqOf cliRealRunReqCap)
      (cliMainWidenedGrpCountOf cliRealRunGrpSCap) ≤ 2 ^ 48 :=
  ⟨by unfold cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   Nat.le_trans (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     (Nat.le_trans cliRealWidened_90pct_literals.1 hcap90),
   Nat.le_trans (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     cliRealWidened_90pct_literals.2⟩

/-- Whole-`main` `< 90%` (`≤ 966,367,641` B) `FitsTrace fineCostModel` on `RealCliMainEnvOf E i`
for every `CliPqxdhInputs W i`. -/
theorem realCliMainEnvOf_90pct_fitsTrace_fineCostModel {lim : BudgetLimits} (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap) {W : PEParams} {E : RunCall → CliRunCalleeEnvs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) {i : Inputs} (hi : CliPqxdhInputs W i)
    {fullLog : List AllocEvent} (hEnv : RealCliMainEnvOf E i fullLog) :
    FitsTrace fineCostModel lim cliRealWidenedMainStepReserve fullLog := by
  obtain ⟨hlp, hram, hva⟩ := realCliMainEnvOf_90pct_bounds hsb hsc hcap90
  exact fitsTrace_fineCostModel_of_group_literal_bounds
    (realCliMainEnvOf_phaseCredit_fine SE hSlots hSessCap hi)
    (realCliMainEnvOf_fine_groupSpec SE hSlots hSessCap hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva hEnv

/-- Whole-`main` `< 90%` (`≤ 966,367,641` B) `FitsEnv fineCostModel` on `RealCliMainEnvOf E i`
for every `CliPqxdhInputs W i`. -/
theorem realCliMainEnvOf_90pct_fitsEnv_fineCostModel {lim : BudgetLimits} (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap) {W : PEParams} {E : RunCall → CliRunCalleeEnvs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) (i : Inputs) (hi : CliPqxdhInputs W i) :
    FitsEnv fineCostModel lim fineCostModel.init (RealCliMainEnvOf E i) := by
  obtain ⟨hlp, hram, hva⟩ := realCliMainEnvOf_90pct_bounds hsb hsc hcap90
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (realCliMainEnvOf_phaseCredit_fine SE hSlots hSessCap hi)
    (realCliMainEnvOf_fine_groupSpec SE hSlots hSessCap hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- Whole-`main` `≤ 1 GiB` `FitsEnv fineCostModel` on `RealCliMainEnvOf E i`. -/
theorem realCliMainEnvOf_fitsEnv_fineCostModel {lim : BudgetLimits} (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap) {W : PEParams} {E : RunCall → CliRunCalleeEnvs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) (i : Inputs) (hi : CliPqxdhInputs W i) :
    FitsEnv fineCostModel lim fineCostModel.init (RealCliMainEnvOf E i) :=
  realCliMainEnvOf_90pct_fitsEnv_fineCostModel henf hsb hsc
    (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) SE hSlots hSessCap i hi

/-- Concrete `cliBudgetLimits` (`1 GiB`) specialization of `realCliMainEnvOf_fitsEnv_fineCostModel`. -/
theorem realCliMainEnvOf_fitsEnv_cliBudgetLimits {W : PEParams} {E : RunCall → CliRunCalleeEnvs}
    (SE : ∀ (g : RunCall), CliPqRunDomain W g → CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ (g : RunCall) (hd : CliPqRunDomain W g), CliRealR2CalleeCaps (SE g hd))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainEnvOf E i) :=
  fun i hi =>
    realCliMainEnvOf_90pct_fitsEnv_fineCostModel rfl (Nat.le_refl _) (Nat.le_refl _)
      (by unfold cliBudgetLimits cliRealNinetyPctOneGiB cliOneGiB; decide) SE hSlots hSessCap i hi

/-- Uniform-slot corollary when `SE` does not inspect `CliPqRunDomain W g`. -/
theorem realCliMainEnvOf_fitsEnv_cliBudgetLimits_uniform
    {W : PEParams} {E : RunCall → CliRunCalleeEnvs}
    (SE : ∀ g : RunCall, CliRealCalleeFineSpecs (E g))
    (hSlots : ∀ g : RunCall, CliRealR2CalleeCaps (SE g))
    (hSessCap : SessionRecordCapInDomain W sessionCapBytes) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainEnvOf E i) :=
  realCliMainEnvOf_fitsEnv_cliBudgetLimits (fun g _ => SE g) (fun g _ => hSlots g) hSessCap

/-! ## 5. Unconditional Concrete `mkExistentialRealCalleeEnvs` Whole-`main` `FitsEnv` -/

/-- Canonical direct-5-slot whole-`main` `stepReserve` under Variant (i)
(`W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes`, widened setup). -/
def cliRealDirectMainStepReserve_i : Nat :=
  cliMainWidenedStepReserveOf cliRealDirectRunMaxReq_i cliRealDirectRunGrpS_i

private theorem cliRealDirectWidened_90pct_literals :
    cliDecoupledRamNeed cliDefaultStaticBytes (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealDirectRunGrpS_i) ≤ cliRealNinetyPctOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealDirectRunGrpS_i) ≤ 2 ^ 48 :=
  ⟨by decide, by decide⟩

private theorem realCliMainEnvOf_90pct_bounds_direct {lim : BudgetLimits}
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes) (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap) :
    cliMainTightLiveOf cliRealDirectRunLive_i ≤
      cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i ∧
    cliDecoupledRamNeed lim.staticBytes (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealDirectRunGrpS_i) ≤ lim.physCap ∧
    cliDecoupledVaNeed lim.staticBytes lim.staticCount (cliMainWidenedCumOf cliRealDirectRunCum_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i)
      (cliMainWidenedGrpCountOf cliRealDirectRunGrpS_i) ≤ 2 ^ 48 :=
  ⟨by unfold cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   Nat.le_trans
     (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     (Nat.le_trans cliRealDirectWidened_90pct_literals.1 hcap90),
   Nat.le_trans
     (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
     cliRealDirectWidened_90pct_literals.2⟩

/-- Unconditional concrete `PhaseCreditSpec fineCostModel` on
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i`. -/
theorem realCliMainEnvOf_phaseCredit_fine_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) :
    PhaseCreditSpec fineCostModel (RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i)
      (cliMainWidenedCumOf cliRealDirectRunCum_i) (cliMainTightLiveOf cliRealDirectRunLive_i)
      (cliMainTightPeakOf cliRealDirectRunLive_i cliRealDirectRunPeak_i)
      (cliMainTightReqOf cliRealDirectRunMaxReq_i) := by
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunOpenedEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (cliRealDirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs W w.g.i := w.g_i.symm ▸ hi
    let SE := existentialRealCalleeFineSpecs img S hi_g w.parse_ok
    obtain ⟨h1, h2, h3, h4, _⟩ :=
      existentialRealCalleeFineSpecs_direct_run_bounds img S hi_g w.parse_ok
    have hrun :=
      (cliRunOpened_real_1MiB_fine_phaseCredit_of_cliPqInputs SE hi_g w.stdin_le w.parse_ok).mono
        h1 h2 h3 h4
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunOpenedEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealDirectRunCum_i + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      cliRealDirectRunLive_i
      (max cliRealDirectRunPeak_i
        (cliRealDirectRunLive_i + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max cliRealDirectRunMaxReq_i (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have htail := ((PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc).or hex).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    ?_ ?_ ?_ ?_
  · unfold cliMainWidenedCumOf; simp only [Nat.add_assoc]; exact Nat.le_refl _
  · unfold cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
  · unfold cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
  · unfold cliMainTightReqOf cliMainMaxReq
    have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
        m3PhaseMaxReq msgCapBytes sessionCapBytes := by
      unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
    rw [h16k]

/-- Unconditional concrete `PhaseGroupSpec fineCostModel` on
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i`. -/
theorem realCliMainEnvOf_fine_groupSpec_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {W : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs W i) :
    PhaseGroupSpec fineCostModel (RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i)
      (cliMainWidenedGrpSOf cliRealDirectRunGrpS_i) := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunOpenedEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (cliRealDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs W w.g.i := w.g_i.symm ▸ hi
        let SE := existentialRealCalleeFineSpecs img S hi_g w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          existentialRealCalleeFineSpecs_direct_run_bounds img S hi_g w.parse_ok
        have hrun := (cliRunOpened_real_fine_groupSpec (wireOutCap := sessionCapBytes)
          SE w.stdin_le).mono h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunOpenedEnv cliIo.rd (mkExistentialRealCalleeEnvs img S W w.g) sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (cliRealDirectRunGrpS_i + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono (by omega)
        exact htot.groups_le st0 hseq }
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or hex).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_of_cliPqInputs hi)).seq htail).mono
    (by unfold cliMainWidenedGrpSOf; omega)

/-- Unconditional `< 90%` (`962,211,497 ≤ 966,367,641` B) concrete whole-`main`
`FitsTrace fineCostModel` at `mkExistentialRealCalleeEnvs img S W`. -/
theorem realCliMainEnvOf_90pct_fitsTrace_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams)
    {i : Inputs} (hi : CliPqxdhInputs W i)
    {fullLog : List AllocEvent}
    (hEnv : RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i fullLog) :
    FitsTrace fineCostModel lim cliRealDirectMainStepReserve_i fullLog := by
  obtain ⟨hlp, hram, hva⟩ := realCliMainEnvOf_90pct_bounds_direct hsb hsc hcap90
  exact fitsTrace_fineCostModel_of_group_literal_bounds
    (realCliMainEnvOf_phaseCredit_fine_concrete img S hi)
    (realCliMainEnvOf_fine_groupSpec_concrete img S hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva hEnv

/-- Unconditional `< 90%` (`962,211,497 ≤ 966,367,641` B) concrete whole-`main`
`FitsEnv fineCostModel` at `mkExistentialRealCalleeEnvs img S W`. -/
theorem realCliMainEnvOf_90pct_fitsEnv_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i) := by
  intro i hi
  obtain ⟨hlp, hram, hva⟩ := realCliMainEnvOf_90pct_bounds_direct hsb hsc hcap90
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    (realCliMainEnvOf_phaseCredit_fine_concrete img S hi)
    (realCliMainEnvOf_fine_groupSpec_concrete img S hi)
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- Unconditional `≤ 1 GiB` concrete whole-`main` `FitsEnv fineCostModel` at `mkExistentialRealCalleeEnvs img S W`. -/
theorem realCliMainEnvOf_fitsEnv_concrete [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i) :=
  realCliMainEnvOf_90pct_fitsEnv_concrete henf hsb hsc
    (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) img S W

/-- Unconditional `cliBudgetLimits` (`1 GiB`) concrete whole-`main` `FitsEnv fineCostModel` at `mkExistentialRealCalleeEnvs img S W`. -/
theorem realCliMainEnvOf_fitsEnv_cliBudgetLimits_concrete [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (W : PEParams) :
    ∀ i : Inputs, CliPqxdhInputs W i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S W) i) :=
  realCliMainEnvOf_90pct_fitsEnv_concrete rfl (Nat.le_refl _) (Nat.le_refl _)
    (by unfold cliBudgetLimits cliRealNinetyPctOneGiB cliOneGiB; decide) img S W

/-! ## 6. Non-Vacuity Theorems (`recv-prekey` `3#8` Allocating Trace) -/

/-- Allocating non-vacuity witness on `RealCliMainEnvOf (E P₀) i₀` (`alloc 72` and `realloc 1 2048 1569`). -/
theorem realCliMainEnvOf_recvPrekey_nonvacuous (E : PEParams → RunCall → CliRunCalleeEnvs)
    (hpksm : ∀ P g, (E P g).pksmEnv = PksmCanonSliceEnv) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧ RealCliMainEnvOf (E P₀) i₀ fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧ AllocEvent.realloc 1 2048 1569 ∈ fullLog := by
  obtain ⟨P₀, g₀, fullLog, hd, hEnv, ha, hr⟩ :=
    cliPqRealCallDomain_recvPrekey_nonvacuous E hpksm
  refine ⟨P₀, g₀.i, fullLog, hd.toCliPqxdhInputs, ?_, ha, hr⟩
  exact realCliMainEnvOf_of_cliMainEnv hd.toCliPqxdhInputs uuidTryParse none false [] false
    ⟨hd.parseArgs_eq, hd.toCliPqDomainCaps.stdin_le, Nat.zero_le _, fun _ hm => nomatch hm⟩ hEnv

/-- Concrete allocating non-vacuity witness on
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀` (`alloc 72` and `realloc 1 2048 1569`). -/
theorem realCliMainEnvOf_concrete_recvPrekey_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧
      RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀ fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧ AllocEvent.realloc 1 2048 1569 ∈ fullLog :=
  realCliMainEnvOf_recvPrekey_nonvacuous (mkExistentialRealCalleeEnvs img S) (fun _ _ => rfl)

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
