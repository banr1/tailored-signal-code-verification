/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
import ProofLib.ProgramReflection

/-!
# Guarded F3 2-Placement `extB2NeedLocks` Strict Composer (`F3.L4B.CliStrictPlaced2G`)

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Route-2 (`w2_c12_route2_stmts.md` §3.2 `R2-G1..G8`) entry-guarded siblings of
  `F3.L4B.CliStrictPlaced2` threading `F3MemsetMemcpyEntryLrFalse mmpl` from
  `ElfMemsetEntryGuard.cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt` (`R2-G7`)
  and `Block617TransferFixedHypG` (`R2-G3`) into
  `CliStrictPlaced2.outcome_of_main_strict_b2_needLocks_guarded_perInput_at` (`R2-G4`),
  eliminating the entry guard internally at the process harness boundary so all whole-process
  conclusions (`cliRunExtOnInputsSigAt = some …`, `CliSpecPqxdh`, `CliPqxdhElfCorrectStrictPlaced2`,
  `CliPqxdhElfCorrectPlaced`) remain completely guard-free.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E
  (Bytes PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   djbKey initiateTapeLen kyberKey partyAddressName wirePrekey wireWhisper)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (Address ArgvFitsInitialStack CliHooks CliPqxdhElfCorrectPlaced CliSpecPqxdh CliSpecPqxdhNoMatch
   Cmd Inputs Outcome OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
   PrintableAsciiArg PublicBundle bundleDir cliExternsPlaced cliProcessInputs coinsFile dirsFold
   encodeDir fileCapBytes filesFold filesOf files_eq_entries initFsState_entries le32
   loadable_pqInitInputs loadable_pqRecvInputs loadable_pqSendInputs maxPlaintextBytes observe
   partyAddress pqInitInputs pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel
   pqSendInputs pqSendModel pqxdhExpectedOutcome publicBundleOf sessionFile stdinCapBytes
   stdioPaths)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainResult RunAnswer cliInputs)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cmdTag parseArgs parseArgs_cmd)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine
  (FineBudget fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfExtB2NeedLocksAssumptions2 CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2
   MainOkCliExtOverB2NeedLocksPlacedAt MainOkCliExtPqB2NeedLocksPlacedAt
   MuslHarnessFineNeedLocksGuardedPerInput b2MainSpecTightNeedLocksFineAt cliBudgetLimits
   cliPqxdhElfCorrectStrictPlaced2_of_extProgEq
   outcome_of_main_strict_b2_needLocks_guarded_perInput_at)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
  (ExternPreservesNoAllocFailed externPreservesNoAllocFailed_cliExternsPlaced
   externPreservesNoAllocFailed_none)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (CliElfTokenCellsPlacedAt cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
   cliRunExtOnInputsSigAt cliRunExtOnInputsSigAt_eq_some cliRunsToExtOnInputsAt_of_outcomeOf_observed
   cliRunsToExtOnInputsAt_of_outcomeOf_usage cliStaticsPlacedAt elfStaticOk_patchElfTokensPlacedAt
   loadState_patchElfTokensPlacedAt patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
  (CliPqxdhElfCorrectStrictPlaced2 cliPqxdhElfCorrectPlaced_of_strict2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG withEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)

/-- Combined `W`-independent Block-`617` entry-`lr`-false predicate covering both `memset` (`blk21`)
and `memcpy` (`blk20`), `rfl`-definitionally equal to
`ElfMemsetEntryGuard.F3MemsetMemcpyEntryLrFalse` while staying `CliElf`-free. -/
abbrev F3MemsetMemcpyEntryLrFalse (mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
  keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false

/-! ## 0. Import-Light PQXDH Input Side-Condition Helpers -/

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

/-! ## 1. Guarded Single-Input Route-B2 `NeedLocks` Call Bridges (`R2-G4`) -/

/-- Guarded single-input Route-B2 `NeedLocks` strict `stdinOverCap` bridge to
`cliRunExtOnInputsSigAt`, consuming `MuslHarnessFineNeedLocksGuardedPerInput` via
`CliStrictPlaced2.outcome_of_main_strict_b2_needLocks_guarded_perInput_at` (`R2-G4`). -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 2 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Guarded single-input Route-B2 `NeedLocks` strict `sendOverCap` bridge to
`cliRunExtOnInputsSigAt` (`R2-G4`). -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i =
      some (.exited 1 [] (filesOf i.files)) := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Guarded single-input Route-B2 `NeedLocks` strict call bridge to `cliRunExtOnInputsSigAt`
(`R2-G4`). -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_b2_needLocks_guarded_perInput_at rfl externPreservesNoAllocFailed_none
      hext (elfStaticOk_patchElfTokensPlacedAt hE) hfs_eq hCode hH
      (fun γ tp => by simpa only [withEntryGuard, hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (inputsOf i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

/-- Predicate-valued companion of `cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs`
(`R2-G4`). -/
theorem cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs} {exitStk : Nat} {libcAddr : BitVec 64}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {stk : Nat}
    {Statics : SepProp} {EntryGuard : State → Prop} {Run : Inputs → RunAnswer → Prop}
    {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) inputsOf
      mmpl lim st stk CodeOk Statics EntryGuard)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (withEntryGuard EntryGuard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
            lim st stk Statics Run inputsOf)))
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq hCode hH
      hmain hstk hstk' hi hl hrun hnover hnstin rfl hcoins hcommit, hp⟩

/-! ## 2. Guarded `MainOkCliExt*B2NeedLocksPlacedAtG` Predicates & Transfer Bridges (`R2-G1..G3`) -/

/-- Guard-parametric Route-B2 `NeedLocks` + `argvAtRO` 5-clause PQXDH `main` specification
(`R2-G1`). -/
@[expose] def MainOkCliExtPqB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (withEntryGuard EntryGuard
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf))) ∧
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

/-- Guard-parametric Route-B2 `NeedLocks` + `argvAtRO` `NoMatch` `main` specification
(`R2-G1`). -/
@[expose] def MainOkCliExtOverB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) (lim : BudgetLimits) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx)
          (withEntryGuard EntryGuard
            (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
              (fineHookRustCliAllocBudget γ mmpl tp brkStart)
              lim fineCostModel.init stk (cliStaticsPlacedAt mpl) Run inputsOf))) ∧
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

/-- F3 specialization of `MainOkCliExtPqB2NeedLocksPlacedAtG` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, `EntryGuard := F3MemsetMemcpyEntryLrFalse mmpl`,
and `lim := cliBudgetLimits` (`R2-G2`). -/
abbrev MainOkCliF3PqB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3MemsetMemcpyEntryLrFalse mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

/-- F3 specialization of `MainOkCliExtOverB2NeedLocksPlacedAtG` at `ext := cliExternsPlaced mmpl`,
`mainIdx := 617`, `inputsOf := cliProcessInputs`, `EntryGuard := F3MemsetMemcpyEntryLrFalse mmpl`,
and `lim := cliBudgetLimits` (`R2-G2`). -/
abbrev MainOkCliF3OverB2NeedLocksPlacedAtG
    (mpl mmpl : Obj.MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3MemsetMemcpyEntryLrFalse mmpl) CodeOk libcAddr brkStart stk cliBudgetLimits

/-- Lift an unguarded ghost `MainOkCliExtPqB2NeedLocksPlacedAt` witness across
`Block617TransferFixedHypG` at `F3MemsetMemcpyEntryLrFalse mmpl` (`R2-G3`). -/
theorem mainOkCliF3PqG_of_block617TransferFixedG
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3MemsetMemcpyEntryLrFalse mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

/-- Lift an unguarded ghost `MainOkCliExtOverB2NeedLocksPlacedAt` witness across
`Block617TransferFixedHypG` at `F3MemsetMemcpyEntryLrFalse mmpl` (`R2-G3`). -/
theorem mainOkCliF3OverG_of_block617TransferFixedG
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (hTr : Block617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl)
      (F3MemsetMemcpyEntryLrFalse mmpl) CodeOk_ghost CodeOk_real libcAddr brkStart stk)
    (hGhost : MainOkCliExtOverB2NeedLocksPlacedAt mpl mmpl EG 617 cliProcessInputs
      CodeOk_ghost libcAddr brkStart stk cliBudgetLimits) :
    MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk_real libcAddr brkStart stk := by
  intro hDropNz X W
  obtain ⟨Run, hmainW, hclauses⟩ := hGhost hDropNz X W
  exact ⟨Run, hTr W Run hmainW, hclauses⟩

/-! ## 3. Guarded Strict `CliSpecPqxdh` ∧ `CliSpecPqxdhNoMatch` Composers (`R2-G5`) -/

/-- Guarded twin of `CliStrictPlaced2.cliSpecPqxdh_ext_strict_of_b2_needLocks` eliminating
`EntryGuard` internally via `R2-G4` (`R2-G5`). -/
theorem cliSpecPqxdh_ext_strict_of_b2_needLocks_guarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard)
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
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
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqInitInputs WP p b t) (inputsLoadable_pqInitInputs WP p b t hp)
      hrun (not_isSendOverCap_pqInitInputs WP p b t)
      (not_isStdinOverCap_pqInitInputs WP p b t) hobs
      (coinsReadable_pqInitInputs WP p b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
        (isStdinOverCap_pqSendInputs WP p m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ IsStdinOverCap (pqSendInputs WP p m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_sendOverCap hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          (isSendOverCap_pqSendInputs WP p m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin (coinsReadable_pqSendInputs WP p m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
          hCode hH hmainW hstk hstk'
          (cliInputsOk_pqSendInputs WP p m r) (inputsLoadable_pqSendInputs WP p m r hp)
          hrun
          (not_isSendOverCap_of_stdin_le
            (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs (coinsReadable_pqSendInputs WP p m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP p (wireWhisper :: c) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        (isStdinOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        (isStdinOverCap_pqRecvInputs WP p c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_obs hext hE htok hfs_eq
        hCode hH hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP p c rc) (inputsLoadable_pqRecvInputs WP p c rc hp)
        hrun (not_isSendOverCap_pqRecvInputs WP p c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP p c rc) hcommit

/-- Guarded twin of `CliStrictPlaced2.cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks` eliminating
`EntryGuard` internally via `R2-G4` (`R2-G5`). -/
theorem cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_guarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {mainIdx : Nat}
    {inputsOf : Inputs → ProcessInputs} {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64}
    {CodeOk : Memory → Prop} {stk : Nat} {lim : BudgetLimits}
    {elf : ElfImage} {W : CliHooks}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hfs_eq : ∀ i : Inputs, initFsState (inputsOf i) = initFsState (cliInputs i))
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext mainIdx W).CodeLoaded m)
    (hH : MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard)
    (hstk : exitStk ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    (hDropNz : mpl.base 547 ≠ 0#64)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim) :
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhNoMatch (cliRunExtOnInputsSigAt mpl ext mainIdx inputsOf elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclause⟩ := hover hDropNz X W
  by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_stdinOverCap hext hE htok hfs_eq
      hCode hH hmainW hstk hstk'
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    exact
      cliRunExtOnInputsSigAt_of_strict_b2_needLocks_guarded_call_pred hext hE htok hfs_eq hCode hH
        hmainW hstk hstk'
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
        hobsEx (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit

/-! ## 4. Guarded Assumptions Bundle, Startup Discharger & ELF Composers (`R2-G6..G8`) -/

/-- Guarded extension of `CliElfExtB2NeedLocksAssumptions2` carrying `harnessG` at `EntryGuard`
(`R2-G6`). -/
structure CliElfExtB2NeedLocksAssumptions2G
    (mpl mmpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (mainIdx : Nat) (inputsOf : Inputs → ProcessInputs)
    (EntryGuard : State → Prop)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (lim : BudgetLimits) (elf : ElfImage) : Prop extends
    CliElfExtB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf where
  harnessG : ∀ W : CliHooks,
    MuslHarnessFineNeedLocksGuardedPerInput exitStk libcAddr (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext mainIdx W) (mpl.base mainIdx) inputsOf
      mmpl lim fineCostModel.init stk CodeOk (cliStaticsPlacedAt mpl) EntryGuard

/-- Forgetful projection from `CliElfExtB2NeedLocksAssumptions2G` to the unguarded
`CliElfExtB2NeedLocksAssumptions2` (`R2-G6`). -/
theorem CliElfExtB2NeedLocksAssumptions2G.toUnguarded
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (H : CliElfExtB2NeedLocksAssumptions2G mpl mmpl ext mainIdx inputsOf EntryGuard
      exitStk libcAddr stk CodeOk lim elf) :
    CliElfExtB2NeedLocksAssumptions2 mpl mmpl ext mainIdx inputsOf
      exitStk libcAddr stk CodeOk lim elf :=
  H.toCliElfExtB2NeedLocksAssumptions2

/-- Concrete F3 `cliBudgetLimits` + `F3MemsetMemcpyEntryLrFalse mmpl` specialization of
`CliElfExtB2NeedLocksAssumptions2G` (`R2-G6`). -/
abbrev CliElfF3B2NeedLocksAssumptionsG
    (mpl mmpl : Obj.MultiPlacement)
    (exitStk : Nat) (libcAddr : BitVec 64) (stk : Nat) (CodeOk : Memory → Prop)
    (elf : ElfImage) : Prop :=
  CliElfExtB2NeedLocksAssumptions2G mpl mmpl (cliExternsPlaced mmpl) 617 cliProcessInputs
    (F3MemsetMemcpyEntryLrFalse mmpl) exitStk libcAddr stk CodeOk cliBudgetLimits elf

/-- Guarded top strict 2-placement ELF theorem eliminating `EntryGuard` via `H.harnessG`
(`R2-G8`). -/
theorem cliPqxdhExtOnInputsElfCorrectStrictPlacedAt2_of_b2NeedLocksAssumptionsG
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {mainIdx : Nat} {inputsOf : Inputs → ProcessInputs}
    {EntryGuard : State → Prop}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (ext W))
    (H : CliElfExtB2NeedLocksAssumptions2G mpl mmpl ext mainIdx inputsOf EntryGuard
      exitStk libcAddr stk CodeOk lim elf)
    (hmain : MainOkCliExtPqB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim)
    (hover : MainOkCliExtOverB2NeedLocksPlacedAtG mpl mmpl ext mainIdx inputsOf EntryGuard CodeOk
      libcAddr elf.brkStart stk lim) :
    CliPqxdhExtOnInputsElfCorrectStrictPlacedAt2 mpl mmpl ext mainIdx inputsOf elf :=
  ⟨H.codeMatches, fun W X =>
    ⟨cliSpecPqxdh_ext_strict_of_b2_needLocks_guarded (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harnessG W) H.stkLo H.stkHi H.base547NeZero hmain X,
     cliSpecPqxdhNoMatch_ext_strict_of_b2_needLocks_guarded (hext W) H.elfStaticOk H.tokenCells
      H.fsEq (H.codeLoaded W) (H.harnessG W) H.stkLo H.stkHi H.base547NeZero hover X⟩⟩

/-- Guarded strict 2-placement F3 ELF composer concluding unchanged
`CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf` (`R2-G8`). -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_extProgEq
    (fun W => (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm)
    (cliPqxdhExtOnInputsElfCorrectStrictPlacedAt2_of_b2NeedLocksAssumptionsG hext H hmain hover)

/-- Guarded Shape-H (`CliPqxdhElfCorrectPlaced`) 2-placement F3 ELF composer (`R2-G8`). -/
theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (hext : ∀ W : CliHooks, ExternPreservesNoAllocFailed (cliExternsPlaced mmpl W))
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_strict2
    (cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG hext H hmain hover)

/-- `hext`-discharged convenience form of `cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG`
(`R2-G8`). -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf :=
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover

/-- `hext`-discharged convenience form of `cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG`
(`R2-G8`). -/
theorem cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG'
    {mpl mmpl : Obj.MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hover : MainOkCliF3OverB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  cliPqxdhElfCorrectPlaced_of_f3B2NeedLocksG
    (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain hover

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
