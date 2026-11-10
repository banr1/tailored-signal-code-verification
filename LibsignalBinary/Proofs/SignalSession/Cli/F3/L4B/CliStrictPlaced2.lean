/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack
public import ProofLib.StdStartup.Layout
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
import Arm64.Trusted.Spec.Hoare
import ProofLib.ProgramReflection
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs

/-!
# Two-Placement `NeedLocks` Strict Composer and Equality Bridges

Lifts the `NeedLocks` + `argvAtRO` + `inputsOf` strict (`0`-excused-abort) whole-process composer
to two placements `(mpl, mmpl : Obj.MultiPlacement)` over `Placed.CliElfCodeMatchesPlaced mpl mmpl elf`
and `Placed.cliRunPlacedSig mpl mmpl elf W`, with concrete `lim := cliBudgetLimits` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   djbKey initiateTapeLen kyberKey partyAddressName wirePrekey wireWhisper)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (Address ArgvFitsInitialStack CliHooks CliPqxdhBinaryCorrectPlaced CliPqxdhBinaryCorrectPlacedAt
   CliPqxdhElfCorrectPlaced CliPqxdhInputs CliRun CliSpecPqxdh CliSpecPqxdhNoMatch Cmd Inputs
   Outcome OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
   PrintableAsciiArg PublicBundle bundleDir cliExternsPlaced cliProcessInputs coinsFile dirsFold
   encodeDir fileCapBytes filesFold filesOf files_eq_entries initFsState_entries le32
   libsignalSessionLib loadable_pqInitInputs loadable_pqRecvInputs loadable_pqSendInputs
   maxPlaintextBytes observe outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited partyAddress
   pqInitInputs pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel pqSendInputs
   pqSendModel pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes stdioPaths)
open CryptoVerification.SignalSession.Coins (coinsLeftSym coinsNextSym)
open CryptoVerification.SignalSession.Placed
  (CliElfCodeMatchesPlaced CliRunsToPlaced cliProgPlacedSig cliRunPlacedSig)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainGhost MainPost MainResult RunAnswer cliInputs fsView_congr
   fsView_writeAll_initFsState loadState_fs_trace signExtend_ofNat_small)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cmdTag parseArgs parseArgs_cmd)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout FineBudget StartupVmPreserved fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (CliElfTokenCellsPlacedAt CliRunsToExtOnInputsAt CliStackShape b2FineHookPool_of_needLocks
   cliProgExtPlacedAt cliProgExtPlacedSigAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
   cliRunExtOnInputsSigAt cliRunExtOnInputsSigAt_eq_some cliRunExtPlacedSigAt
   cliRunsToExtOnInputsAt_of_outcomeOf_observed cliRunsToExtOnInputsAt_of_outcomeOf_usage
   cliRunsToExtOnInputsAt_unique cliStaticsPlacedAt coinsStaticsPlacedAt
   elfStaticOk_patchElfTokensPlacedAt loadState_patchElfTokensPlacedAt lsLogOffAt
   patchElfTokensPlacedAt tokenInitPlacedAtMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhBinaryCorrectStrictPlaced2 CliPqxdhBinaryCorrectStrictPlacedAt2
   CliPqxdhElfCorrectStrictPlaced2 cliPqxdhBinaryCorrectPlaced_of_strict2
   cliPqxdhElfCorrectPlaced_of_strict2)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced
   externPreservesNoAllocFailed_none steps_preserves_no_allocFailed)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngAuxvAt mallocngAddrsOfPlacement)


/-! ## PQXDH Input Side-Condition Helpers -/

private theorem coinsReadable_of_last (i : Inputs) (prefixFiles : List (String × List (BitVec 8)))
    (coins : List (BitVec 8)) (hfiles : i.files = prefixFiles ++ [(coinsFile, coins)])
    (hcap : coins.length ≤ fileCapBytes) :
    CoinsReadable i := by
  unfold CoinsReadable
  rw [files_eq_entries]
  have hne : (normalizePath "coins").isEmpty = false := by rfl_kernel
  have hnsB : (stdioPaths.map normalizePath).contains (normalizePath "coins") = false := by
    rfl_kernel
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := fun hm => by
    rw [← List.contains_iff_mem] at hm
    exact Bool.noConfusion (hnsB.symm.trans hm)
  rw [hne, initFsState_entries (cliInputs i) (normalizePath "coins") hns]
  change (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") ≠ some .dir ∧
    ∀ bs, (filesFold i.files (dirsFold i.dirs {})).entries (normalizePath "coins") = some (.file bs) →
      bs.length ≤ fileCapBytes
  rw [hfiles]
  unfold filesFold
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, FsState.setFile, FsState.setEntry, coinsFile]
  refine ⟨by simp, fun bs h => ?_⟩
  simp at h
  subst h
  exact hcap

private theorem coinsReadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    CoinsReadable (pqInitInputs W st b t) :=
  coinsReadable_of_last _ (encodeDir W st ++ (publicBundleOf b).files bundleDir) t.toList
    (by simp [pqInitInputs, pqInputs, List.append_assoc])
    (by simp [List.Vector.toList_length, initiateTapeLen, fileCapBytes])

private theorem coinsReadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    CoinsReadable (pqSendInputs W st m r) :=
  coinsReadable_of_last _ (encodeDir W st) r.toList
    (by simp [pqSendInputs, pqInputs])
    (by simp [List.Vector.toList_length, fileCapBytes])

private theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CoinsReadable (pqRecvInputs W st c rc) :=
  coinsReadable_of_last _ (encodeDir W st) (keyToBytes32 rc)
    (by simp [pqRecvInputs, pqInputs])
    (by simp [keyToBytes32, fileCapBytes])

private theorem inputsLoadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqInitInputs W st b t) := by
  refine ⟨(loadable_pqInitInputs W st b t).1, fun f hf =>
    ⟨(loadable_pqInitInputs W st b t).2 f hf, ?_⟩⟩
  simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hf
  rcases hf with h | h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · unfold publicBundleOf PublicBundle.files at h
    cases ho : b.opk with
    | none =>
      simp only [ho, Option.map_none, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
    | some ok =>
      obtain ⟨id, key⟩ := ok
      simp only [ho, Option.map_some, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
  · simp [initiateTapeLen, MAX_LFS_FILESIZE]

private theorem inputsLoadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqSendInputs W st m r) := by
  refine ⟨(loadable_pqSendInputs W st m r).1, fun f hf =>
    ⟨(loadable_pqSendInputs W st m r).2 f hf, ?_⟩⟩
  simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [MAX_LFS_FILESIZE]

private theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [keyToBytes32, MAX_LFS_FILESIZE]

private theorem partyAddress_text_toList (P : Party) :
    (partyAddress P).text.toList = (partyAddressName P).toList ++ ".".toList ++ ['1'] := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  simp [partyAddress, Address.text, ht1, hd1, String.toList_append]

private theorem partyAddress_text_printable (P : Party) :
    PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · intro h
    have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · intro c hc
    rw [partyAddress_text_toList] at hc
    cases P <;> revert c hc <;> decide

private theorem partyAddress_text_length (P : Party) :
    (partyAddress P).text.length = 38 := by
  rw [← String.length_toList, partyAddress_text_toList]
  cases P <;> decide

private theorem cliInputsOk_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    CliInputsOk (pqInitInputs W st b t) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqInitInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
    · unfold PrintableAsciiArg bundleDir; decide
  · unfold ArgvFitsInitialStack pqInitInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    unfold bundleDir
    decide

private theorem cliInputsOk_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    CliInputsOk (pqSendInputs W st m r) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqSendInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · unfold ArgvFitsInitialStack pqSendInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    decide

private theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    CliInputsOk (pqRecvInputs W st c rc) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [pqRecvInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · unfold ArgvFitsInitialStack pqRecvInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      partyAddress_text_length]
    decide

private theorem not_isSendOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ 1_000_000) :
    ¬ IsSendOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

private theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ IsStdinOverCap i :=
  fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

private theorem isSendOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : 1_000_000 < m.length) :
    IsSendOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ := parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  cases c <;> simp [CallV.tag, cmdTag] at htag
  rename_i peer
  exact ⟨peer, hc⟩

private theorem not_isSendOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ IsSendOverCap (pqInitInputs W st b t) := by
  rintro ⟨_, hgt⟩
  simp [pqInitInputs, pqInputs] at hgt

private theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    ¬ IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change parseArgs uuidTryParse
    ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) = some (.send peer) at hp
  rw [hp] at hv
  injection hv with heq
  subst heq
  simp [CallV.tag, cmdTag] at htag

private theorem isStdinOverCap_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (h : stdinCapBytes < m.length) :
    IsStdinOverCap (pqSendInputs W st m r) := by
  refine ⟨?_, h⟩
  obtain ⟨c, hc, htag⟩ := parseArgs_cmd (.send (partyAddress st.party.other)) rfl
  exact ⟨c, hc, by rw [htag]; simp [cmdTag]⟩

private theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) :
    IsStdinOverCap (pqRecvInputs W st c rc) := by
  refine ⟨?_, h⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨v, hv, by rw [htag]; simp [cmdTag]⟩

private theorem not_isStdinOverCap_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ¬ IsStdinOverCap (pqInitInputs W st b t) :=
  not_isStdinOverCap_of_stdin_le (by simp [pqInitInputs, pqInputs])

/-! ## `NeedLocks` + `argvAtRO` + `inputsOf` Per-Input Harness and Strict Outcome -/

/-- Default enforced `1 GiB` `BudgetLimits`. -/
abbrev cliBudgetLimits : BudgetLimits :=
  { staticCount := 64, staticBytes := 16 * 1024 * 1024, physCap := 2 ^ 30, enforced := true }

/-- Read-only NUL-terminated bytes of `s` at `p`. -/
def cStrAtRO (p : BitVec 64) (s : List (BitVec 8)) : SepProp :=
  p ↦ᵣ (s ++ [0#8])

/-- Read-only C `argv` pointer table at `a`. -/
def argvAtRO : BitVec 64 → List (List (BitVec 8)) → SepProp
  | a, [] => a ↦₆₄ᵣ 0#64
  | a, s :: ss => ∃∗ p, (a ↦₆₄ᵣ p) ∗ cStrAtRO p s ∗ argvAtRO (a + 8#64) ss

def B2MainEntryFacts (inputsOf : Inputs → ProcessInputs) (i : Inputs) (s : State) : Prop :=
  (s.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
    s.fs = initFsState (inputsOf i) ∧ s.trace = []

/-- Read-only-`argv` counterpart of `TopBudget.mainFrame`. -/
def b2MainFrameFine {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (stk : Nat) (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  argvAtRO (s.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
    stackAt s.sp stk ∗ A.pool lim st s ∗ Statics

def b2MainEntryPreFine (CodeOk : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (stk : Nat)
    (Statics : SepProp) (i : Inputs) (s : State) : SepProp :=
  ⌜CodeOk s.mem ∧ stk ≤ s.sp.toNat⌝ ∗ b2MainFrameFine A lim st stk Statics i s

/-- Tight `main` `Spec` returning `((libcAddr + 3#64) ↦₈ 0#8)` (`__libc.need_locks = 0`) and
`stackAt s0.sp stk` on normal return (`onExit = onOom = ⌜False⌝`). -/
def b2MainSpecTightNeedLocksFineAt (libcAddr : BitVec 64) (CodeOk : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (stk : Nat) (Statics : SepProp) (Run : Inputs → RunAnswer → Prop)
    (inputsOf : Inputs → ProcessInputs) : Spec MainGhost where
  pre := fun g s =>
    ⌜CodeOk s.mem ∧ MainCaseB2 Run IsSendOverCap IsStdinOverCap g.i g.r ∧ CliInputsOk g.i ∧
      B2MainEntryFacts inputsOf g.i s ∧ stk ≤ s.sp.toNat⌝ ∗
      b2MainFrameFine A lim st stk Statics g.i s
  post := fun g s0 sf =>
    ⌜MainPost g.r s0 sf⌝ ∗ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt s0.sp stk ∗ anyHeap
  onPanic := fun g s0 sf => ⌜g.r = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem exit_frame_needLocks_n {m : Memory} {nl sp : BitVec 64} {n stk : Nat} {Fr : SepProp}
    (hstk : n ≤ stk) (_hstk' : stk ≤ 2 ^ 64)
    (h : m ⊨ ((nl ↦₈ 0#8) ∗ stackAt sp stk ∗ anyHeap) ∗ Fr) :
    m ⊨ (nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗ anyHeap := by
  have hsplit := stackAt_split_bottom sp n (stk - n) (by omega)
  rw [show n + (stk - n) = stk by omega] at hsplit
  rw [hsplit] at h
  refine Satisfies.mono ?_ h
  have e : (((nl ↦₈ 0#8) ∗ (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ stackAt sp n) ∗
        anyHeap) ∗ Fr) =
      (nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗
        (memRegion (sp - BitVec.ofNat 64 stk) (stk - n) ∗ anyHeap) := by
    sep_ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))

/-- Per-input `∃ (γ : GhostName)` whole-process harness parameterized by `exitStk`, `inputsOf`,
`argvAtRO`, and `__libc.need_locks`. -/
def MuslHarnessFineNeedLocksPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFine CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Construct `MuslHarnessFineNeedLocksPerInput` from a `NeedLocks` startup-and-exit witness and
`b2FineHookPool_of_needLocks`. -/
theorem muslHarnessFineNeedLocksPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFine CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFine, b2MainFrameFine, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩

/-- Layout-generic block-`617` startup return-address predicate (`blr x21` at `stage2+0x34` in `ProofLib/StdStartup/StdDetect.lean:69-72` `libcStartMainStage2EntryInstrs` returns to `stage2+0x38` = `bl exit` in `ProofLib/StdStartup/CleanupAndExit.lean:391` `muslExitChunks`). -/
def StdMainEntryLr (L : ProofLib.StdStartup.StdBinaryLayout) (sm : State) : Prop :=
  sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64

/-- Guarded twin of `MuslHarnessFineNeedLocksPerInput` carrying an entry-state predicate
`EntryGuard sm` at `mainPc` (e.g. `StdMainEntryLr L`); `MuslHarnessFineNeedLocksPerInput` is its
`EntryGuard := fun _ => True` specialization (`muslHarnessFineNeedLocksPerInput_eq_guarded_true`). -/
def MuslHarnessFineNeedLocksGuardedPerInput (exitStk : Nat) (libcAddr : BitVec 64)
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp)
    (EntryGuard : State → Prop) : Prop :=
  ElfStaticOk elf →
    ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
      ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
        let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
        elf.loadState (inputsOf i) = .ok s0 ∧
        Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
        sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
        EntryGuard sm ∧
        (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
        (sm.mem ⊨ b2MainEntryPreFine CodeOk A lim st stk Statics i sm ∗ Fr) ∧
        ∀ sr : State, Steps P sm sr → Returned sm sr →
          (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
          ∃ sx : State, Steps P sr sx ∧
            sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
            sx.fs = sr.fs ∧ sx.trace = sr.trace

theorem MuslHarnessFineNeedLocksGuardedPerInput.mono_guard
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    {EntryGuard EntryGuard' : State → Prop}
    (hImp : ∀ sm : State, EntryGuard sm → EntryGuard' sm)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard' := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hImp sm hG, hx0, hEntry, hexit⟩

theorem MuslHarnessFineNeedLocksGuardedPerInput.toUnguarded
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    {EntryGuard : State → Prop}
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, _hG, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩

theorem MuslHarnessFineNeedLocksPerInput.toGuardedTrue
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {st : FineBudget} {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp}
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics (fun _ => True) := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, hexit⟩ :=
    hH hE i hi
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, trivial, hx0, hEntry, hexit⟩

theorem muslHarnessFineNeedLocksGuardedPerInput_true_iff
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics (fun _ => True) ↔
      MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics :=
  ⟨MuslHarnessFineNeedLocksGuardedPerInput.toUnguarded,
   MuslHarnessFineNeedLocksPerInput.toGuardedTrue⟩

theorem muslHarnessFineNeedLocksPerInput_eq_guarded_true
    (exitStk : Nat) (libcAddr : BitVec 64) (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (inputsOf : Inputs → ProcessInputs) (mmpl : Obj.MultiPlacement)
    (lim : BudgetLimits) (st : FineBudget) (stk : Nat)
    (CodeOk : Memory → Prop) (Statics : SepProp) :
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics =
      MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
        mmpl lim st stk CodeOk Statics (fun _ => True) :=
  propext (muslHarnessFineNeedLocksGuardedPerInput_true_iff exitStk libcAddr elf P mainPc
    inputsOf mmpl lim st stk CodeOk Statics).symm

theorem muslHarnessFineNeedLocksGuardedPerInput_of_startup
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {stk : Nat} {CodeOk : Memory → Prop} {Statics : SepProp} {EntryGuard : State → Prop}
    (hsh : ∀ i : Inputs, CliStackShape (inputsOf i))
    (hLayout : CliElfMallocngLayout elf lim)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hStartup : ElfStaticOk elf →
      ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
        ∃ (s0 sm : State) (Fr : SepProp) (auxvPtr : BitVec 64) (errnoVal : BitVec 32),
          elf.loadState (inputsOf i) = .ok s0 ∧
          Steps P s0 sm ∧ sm.pc = mainPc ∧ sm.status = .Running ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
          EntryGuard sm ∧
          (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
          StartupVmPreserved s0 sm ∧
          0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
          CodeOk sm.mem ∧ mallocngLib.CodeLoaded mmpl sm.mem ∧
          stk ≤ sm.sp.toNat ∧
          (sm.mem ⊨
            mallocngLib.dataInit mmpl ∗
              ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((libcAddr + 3#64) ↦₈ 0#8) ∗
              ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
              ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
              MallocngAuxvAt auxvPtr ∗
              (argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
                stackAt sm.sp stk ∗ Statics ∗ Fr)) ∧
          ∀ sr : State, Steps P sm sr → Returned sm sr →
            (sr.mem ⊨ ((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp exitStk ∗ Fr ∗ anyHeap) →
            ∃ sx : State, Steps P sr sx ∧
              sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
              sx.fs = sr.fs ∧ sx.trace = sr.trace) :
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim fineCostModel.init stk CodeOk Statics EntryGuard := by
  intro hE i hi
  obtain ⟨s0, sm, Fr, auxvPtr, errnoVal, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0,
    hVm, htpLo, htpHi, hCO, hCL, hsp, hmem, hexit⟩ := hStartup hE i hi
  obtain ⟨γ, hPool⟩ :=
    b2FineHookPool_of_needLocks hCL (hsh i) hLayout hload hVm htpLo htpHi hlibc hmem
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨ b2MainEntryPreFine CodeOk A lim fineCostModel.init stk Statics i sm ∗ Fr := by
    simp only [b2MainEntryPreFine, b2MainFrameFine, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hsp⟩, ?_⟩
    let Argv := argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString)
    let Stk := stackAt sm.sp stk
    have heq :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fr)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fr) := by sep_ac_rfl
    exact heq ▸ hPool
  exact ⟨s0, sm, Fr, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hG, hx0, hEntry, hexit⟩

/-- Guarded counterpart of `outcome_of_main_strict_b2_needLocks_perInput_at` under
`MuslHarnessFineNeedLocksGuardedPerInput` at `EntryGuard`. -/
theorem outcome_of_main_strict_b2_needLocks_guarded_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {EntryGuard : State → Prop}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        { (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf) with
          pre := fun x s => ⌜EntryGuard s⌝ ∗
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
              lim st stk Statics Run inputsOf).pre x s })
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hG, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  let baseSpec := b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf
  have hpre : sm.mem ⊨
      ({ baseSpec with pre := fun x s => ⌜EntryGuard s⌝ ∗ baseSpec.pre x s }).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [baseSpec, b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG, ⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Commute `((nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗ anyHeap)` into `F3Relink.HarnessSpec.MuslHarnessNeedLocksN`'s
`stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap` return-frame order. -/
theorem satisfies_stack_needLocks_of_needLocks_stack
    {m : Memory} {nl sp : BitVec 64} {n : Nat} {Fr : SepProp}
    (h : m ⊨ (nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗ anyHeap) :
    m ⊨ stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap := by
  have hEq :
      ((nl ↦₈ 0#8) ∗ stackAt sp n ∗ Fr ∗ anyHeap) =
      (stackAt sp n ∗ (nl ↦₈ 0#8) ∗ Fr ∗ anyHeap) := by sep_ac_rfl
  exact hEq ▸ h

/-- Strict `NeedLocks` whole-process outcome theorem. -/
theorem outcome_of_main_strict_b2_needLocks_perInput_at
    {exitStk : Nat} {libcAddr : BitVec 64} {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {inputsOf : Inputs → ProcessInputs}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr elf P mainPc inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (inputsOf i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [b2MainEntryPreFine, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run inputsOf).pre
        ⟨i, r⟩ sm ∗ Fr := by
    simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    have hpost' : sf.mem ⊨ (((libcAddr + 3#64) ↦₈ 0#8) ∗ stackAt sm.sp stk ∗ anyHeap) ∗ Fr := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame_needLocks_n hstk hstk' hpost')
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0, hfs_eq i]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · have hs0 : allocFailedEvent ∉ s0.trace := by rw [htr0]; simp
      exact absurd (List.mem_of_mem_drop hA)
        (steps_preserves_no_allocFailed hsvc hext hovr hsteps01 hs0)
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 2 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 1 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {Run : Inputs → RunAnswer → Prop} {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          lim st stk Statics Run inputsOf))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq hCode hH
      hmain hstk hstk' hi hl hrun hnover hnstin rfl hcoins hcommit, hp⟩

/-! ## Uniform-`∀ γ tp` `MainOkCliExt*B2NeedLocks` Predicates -/

/-- `NeedLocks` + `argvAtRO` 5-clause PQXDH `main` specification. -/
def MainOkCliExtPqB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ p : PqParty, PqxdhPartyInSpecDomain WP p →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
          p.session = none →
          ∃ a, Run (pqInitInputs WP p b t) a ∧
            observe (pqInitInputs WP p b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP p b t) (pqInitModel X WP p b t) ∧
            CommitOk (pqInitInputs WP p b t) (MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP p m r) a ∧
            observe (pqSendInputs WP p m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP p m r) (pqSendModel WP p m r.toList) ∧
            CommitOk (pqSendInputs WP p m r) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP p (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP p (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP p c rc) ∧
            CommitOk (pqRecvInputs WP p (wireWhisper :: c) rc) (MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, p.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP p (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP p m rc) ∧
            CommitOk (pqRecvInputs WP p (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP p c rc) a ∧
            observe (pqRecvInputs WP p c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP p c rc).files) ∧
            CommitOk (pqRecvInputs WP p c rc) (MainResult.ofAnswer a))

/-- `NeedLocks` + `argvAtRO` `NoMatch` `main` specification. -/
def MainOkCliExtOverB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf)) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) (MainResult.ofAnswer a)

/-- Specialization of `MainOkCliExtPqB2NeedLocksPlacedAt` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, and `lim := cliBudgetLimits`. -/
abbrev MainOkCliF3PqB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk cliBudgetLimits

/-- Specialization of `MainOkCliExtOverB2NeedLocksPlacedAt` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, and `lim := cliBudgetLimits`. -/
abbrev MainOkCliF3OverB2NeedLocksPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    CodeOk libcAddr brkStart stk cliBudgetLimits

/-! ## Strict `CliSpecPqxdh` and `CliSpecPqxdhNoMatch` Composers -/

theorem cliSpecPqxdh_ext_strict_of_b2_needLocks
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X p hp
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain hDropNz X W
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses p hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred hext hE htok hfs_eq hCode hH
        hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

/-! ## Strict Two-Placement ELF Predicates and Assumptions -/

/-- Strict (`0`-excused-abort) 2-placement ELF correctness under `(mpl, mmpl)`, extern family
`ext` (wrapped with `abortOnPanic` inside `cliRunExtPlacedSigAt`), and `main` block `mainIdx`. -/
def CliPqxdhExtElfCorrectStrictPlacedAt2
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunExtPlacedSigAt mpl ext mainIdx elf W) X ⟨W.C, W.Q⟩

/-- `inputsOf`-generalized 2-placement strict relocatable ELF correctness. -/
def CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩

/-- Static ELF and two-placement `(mpl, mmpl)` assumptions for `NeedLocks` execution. -/
structure CliElfExtB2NeedLocksAssumptions2
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop where
  elfStaticOk : ElfStaticOk elf
  codeMatches : CliElfCodeMatchesPlaced mpl mmpl elf
  tokenCells : CliElfTokenCellsPlacedAt mpl elf
  mallocngLayout : CliElfMallocngLayout elf lim
  base547NeZero : mpl.base 547 ≠ 0#64
  stkLo : exitStk ≤ stk
  stkHi : stk ≤ 2 ^ 64
  fsEq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i)
  codeLoaded : ∀ (W : CliHooks) (m : Memory),
    CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m
  harness : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl)

/-- `cliBudgetLimits` specialization of `CliElfExtB2NeedLocksAssumptions2` at
`ext := cliExternsPlaced mmpl`, `mainIdx := 617`, and `inputsOf := cliProcessInputs`. -/
abbrev CliElfF3B2NeedLocksAssumptions
    (mpl mmpl : Obj.MultiPlacement)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (elf : ElfImage) : Prop :=
  CliElfExtB2NeedLocksAssumptions2 mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    exitStk libcAddr stk CodeOk cliBudgetLimits elf

theorem cliPqxdhExtOnInputsElfCorrectStrictPlacedAt2_of_b2NeedLocksAssumptions
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl ext mainIdx inputsOf CodeOk
      libcAddr elf.brkStart stk lim) :
    CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2 mpl mmpl ext mainIdx inputsOf elf :=
  ⟨H.codeMatches, fun W X =>
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harness W) H.stkLo H.stkHi H.base547NeZero hover X⟩⟩

/-! ## Two-Placement Equality Bridges to `PlacedOomRecovery2` and `CliPqxdhElfCorrectPlaced` -/

theorem cliRunsToPlaced_iff_ext_of_progEq2
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    {i : Inputs} (hload : elf.loadState (cliProcessInputs i) = elf.loadState (inputsOf i))
    (o : Outcome) :
    CliRunsToPlaced mpl mmpl elf W i o ↔
      CliRunsToExtOnInputsAt mpl ext mainIdx inputsOf elf W i o := by
  unfold CliRunsToPlaced CliRunsToExtOnInputsAt
  rw [hprog, hload]

theorem cliRunPlacedSig_eq_on_input_of_progEq2
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    {i : Inputs} (hload : elf.loadState (cliProcessInputs i) = elf.loadState (inputsOf i)) :
    cliRunPlacedSig mpl mmpl elf W i =
      cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W i := by
  unfold cliRunPlacedSig cliRunExtOnInputsSigAt
  have hex : (∃ o, CliRunsToPlaced mpl mmpl elf W i o) ↔
      (∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx inputsOf elf W i o) :=
    exists_congr (cliRunsToPlaced_iff_ext_of_progEq2 hprog hload)
  by_cases h1 : ∃ o, CliRunsToPlaced mpl mmpl elf W i o
  · have h2 : ∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx inputsOf elf W i o :=
      hex.mp h1
    simp only [h1, h2, ↓reduceDIte]
    congr 1
    have hc1 : CliRunsToExtOnInputsAt mpl ext mainIdx inputsOf elf W i (Classical.choose h1) :=
      (cliRunsToPlaced_iff_ext_of_progEq2 hprog hload _).mp (Classical.choose_spec h1)
    exact cliRunsToExtOnInputsAt_unique hc1 (Classical.choose_spec h2)
  · have h2 : ¬ ∃ o, CliRunsToExtOnInputsAt mpl ext mainIdx inputsOf elf W i o :=
      fun hc => h1 (hex.mpr hc)
    simp only [h1, h2, ↓reduceDIte]

theorem cliRunPlacedSig_eq_cliRunExtPlacedSigAt_of_progEq2
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage} {W : CliHooks}
    (hprog : cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W) :
    cliRunPlacedSig mpl mmpl elf W = cliRunExtPlacedSigAt mpl ext mainIdx elf W := by
  funext i
  exact cliRunPlacedSig_eq_on_input_of_progEq2 hprog rfl

private theorem cliSpecPqxdh_congr_on_inputs
    {run₁ run₂ : CliRun} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    (heq : ∀ i : Inputs, CliPqxdhInputs WP i → run₁ i = run₂ i)
    (h : CliSpecPqxdh run₂ X WP) :
    CliSpecPqxdh run₁ X WP := by
  intro st hdom
  obtain ⟨h1, h2, h3, h4, h5⟩ := h st hdom
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    rw [heq _ ⟨st, hdom, Or.inl ⟨hnone, b, t, rfl⟩⟩]
    exact h1 b t hnone
  · intro m r hm
    have hi : CliPqxdhInputs WP (pqSendInputs WP st m r) :=
      ⟨st, hdom, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
    have h2' := h2 m r hm
    split_ifs at h2' ⊢ <;> (rw [heq _ hi]; exact h2')
  · intro c rc hc
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wireWhisper :: c) rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
    have h3' := h3 c rc hc
    split_ifs at h3' ⊢ <;> (rw [heq _ hi]; exact h3')
  · intro m rc hm hmatch
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
    have h4' := h4 m rc hm hmatch
    split_ifs at h4' ⊢ <;> (rw [heq _ hi]; exact h4')
  · intro c rc hc h2ne h3ne
    have hi : CliPqxdhInputs WP (pqRecvInputs WP st c rc) :=
      ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩
    have h5' := h5 c rc hc h2ne h3ne
    split_ifs at h5' ⊢ <;> (rw [heq _ hi]; exact h5')

private theorem cliSpecPqxdhNoMatch_congr_on_inputs
    {run₁ run₂ : CliRun} {X : UnreachedPqxdhPrimitives} {WP : PEParams}
    (heq : ∀ i : Inputs, CliPqxdhInputs WP i → run₁ i = run₂ i)
    (h : CliSpecPqxdhNoMatch run₂ X WP) :
    CliSpecPqxdhNoMatch run₁ X WP := by
  intro st hdom x g hsess m rc hm hnm
  have hi : CliPqxdhInputs WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
    ⟨st, hdom, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
  have h' := h st hdom x g hsess m rc hm hnm
  rw [heq _ hi]
  exact h'

theorem cliPqxdhElfCorrectStrictPlaced2_of_extOnInputsProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hload : ∀ (W : CliHooks) (i : Inputs),
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      elf.loadState (cliProcessInputs i) = elf.loadState (inputsOf i))
    (hStrict : CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2 mpl mmpl ext mainIdx inputsOf elf) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf := by
  refine ⟨hStrict.1, fun W X => ?_⟩
  have heq : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      cliRunPlacedSig mpl mmpl elf W i =
        cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W i :=
    fun i hi => cliRunPlacedSig_eq_on_input_of_progEq2 (hprog W) (hload W i hi)
  exact ⟨cliSpecPqxdh_congr_on_inputs heq (hStrict.2 W X).1,
    cliSpecPqxdhNoMatch_congr_on_inputs heq (hStrict.2 W X).2⟩

theorem cliPqxdhElfCorrectStrictPlaced2_of_extProgEq
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt2 mpl mmpl ext mainIdx elf) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_extOnInputsProgEq hprog (fun _ _ _ => rfl) hStrict

theorem cliPqxdhElfCorrectPlaced_of_extProgEq2
    {mpl mmpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {elf : ElfImage}
    (hprog : ∀ W : CliHooks,
      cliProgPlacedSig mpl mmpl W = cliProgExtPlacedSigAt mpl ext mainIdx W)
    (hStrict : CliPqxdhExtElfCorrectStrictPlacedAt2 mpl mmpl ext mainIdx elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_strict2 (cliPqxdhElfCorrectStrictPlaced2_of_extProgEq hprog hStrict)

/-! ## `cliBudgetLimits`-Pinned Strict and Shape-H ELF Composers -/

/-- Direct strict 2-placement F3 ELF composer pinned to `lim := cliBudgetLimits`,
`ext := cliExternsPlaced mmpl`, `mainIdx := 617`, and `inputsOf := cliProcessInputs`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_extProgEq
    (fun W => (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm)
    (cliPqxdhExtOnInputsElfCorrectStrictPlacedAt2_of_b2NeedLocksAssumptions hext H hmain hover)

theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_strict2
    (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks hext H hmain hover)

theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover

theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocks
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover

/-! ## Universal `LinkedAt` Binary-Level Composers -/

/-- Generic 2-placement strict binary composer (`CliPqxdhBinaryCorrectStrictPlaced2 bytes`) from
`ElfImage.parse bytes = .ok elf` and universal `(mpl, mmpl)` `f3B2NeedLocks` witnesses. -/
theorem cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hext : ∀ (mmpl : Obj.MultiPlacement) (W : CliHooks),
      ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (hAssump : ∀ mpl mmpl : Obj.MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhBinaryCorrectStrictPlaced2 bytes := by
  intro mpl mmpl hls hmng
  obtain ⟨exitStk, libcAddr, stk, CodeOk, H, hmain, hover⟩ := hAssump mpl mmpl hls hmng
  exact ⟨elf, hparse, cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks (hext mmpl) H hmain hover⟩

theorem cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hext : ∀ (mmpl : Obj.MultiPlacement) (W : CliHooks),
      ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (hAssump : ∀ mpl mmpl : Obj.MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  cliPqxdhBinaryCorrectPlaced_of_strict2
    (cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks hparse hext hAssump)

theorem cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks'
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : Obj.MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhBinaryCorrectStrictPlaced2 bytes :=
  cliPqxdhBinaryCorrectStrictPlaced2_of_f3B2NeedLocks hparse
    externPreservesNoAllocFailed_cliExternsPlaced hAssump

theorem cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks'
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hAssump : ∀ mpl mmpl : Obj.MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ∃ (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop),
        CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf ∧
        MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk ∧
        MainOkCliF3OverB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  cliPqxdhBinaryCorrectPlaced_of_f3B2NeedLocks hparse
    externPreservesNoAllocFailed_cliExternsPlaced hAssump

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
