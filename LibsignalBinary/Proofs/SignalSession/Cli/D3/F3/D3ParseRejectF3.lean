/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SpecLemmas.FsFold
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs
import ProofLib.CoreLemmas
import ProofLib.ProgramReflection

/-!
# Two-Placement Pre-Key `recv` Combinators, `recvOverStdinCap`, & `pksmParseNone`

Two-placement `(mpl, mmpl)` whole-process combinators for `pqRecvInputs`, plus
`recvOverStdinCap` and unparseable pre-key rejection (`pksmParse body = none`) over
`Placed.cliRunPlacedSig` and `CliReachesOOMPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.E2E (
  PEParams UnreachedPqxdhPrimitives partyAddressName wirePrekey
)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (
  Address ArgvFitsInitialStack CliHooks CliPqxdhInputs CliReachesOOMPlaced Cmd Inputs Outcome
  OutcomeOrExcusedAbort PqParty PqxdhPartyInSpecDomain PrintableAsciiArg cliExternsPlaced
  cliProcessInputs coinsFile dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries
  initFsState_entries loadable_pqRecvInputs observe partyAddress pqInputs pqRecvInputs stdinCapBytes
  stdioPaths
)
open CryptoVerification.SignalSession.Cli (
  CliInputsOk CoinsReadable CommitOk InputsLoadable IsSendOverCap IsStdinOverCap MainCaseB2
  MainResult RunAnswer cliInputs
)
open CryptoVerification.SignalSession.Cli.MainHops (CallV cmdTag domainArgv_pqRecv parseArgs parseArgs_cmd)
open CryptoVerification.SignalSession.Cli.RunCompose (
  RunFilesOk RunHsOk RunSem SlotAns finish runAns runFiles runRel
)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Agree (decSigDef encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (
  addrParse_textBytes addrValE ownAddr_pqRecv parseArgs_recv runAns_pqRecvPrekey_eq runBounds_pqRecv
)
open CryptoVerification.SignalSession.Cli.Slots (
  distinctSid_party encOk₀ filesOkPeer_pqRecv filesOk₀ pqSessBytes_le_fileCapBytes
  runEncOk_pqRecv runFilesOk_of_peer scopeIn
)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt
  cliBudgetLimits cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
  cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_pred
  cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap cliRunPlacedSig_eq_on_input_of_progEq2
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq cliStaticsPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (outcomeOrExcusedAbort_of_eq)

/-! ## 1. Pure `Slots.scopeIn` & `RunSem` Domain Helpers -/

export LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3 (
  encodeInjOn_scopeIn ratchetScopeCoversPq_scopeIn
)

theorem runFilesOk_pqRecv_cli_f3 {S : RunSem}
    (hS : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    RunFilesOk S (pqRecvInputs W st c rc) :=
  runFilesOk_of_peer (.recv (partyAddress st.party.other)) rfl rfl (ownAddr_pqRecv W st c rc)
    (hS ▸ ⟨filesOkPeer_pqRecv W st c rc
      (fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs)
      (pqSessBytes_le_fileCapBytes hwf), distinctSid_party st.party, trivial⟩)

theorem runHsOk_pqRecvPrekey_body_f3 {S : RunSem}
    (W : PEParams) (st : PqParty) (body : List (BitVec 8)) (rc : BitVec 256)
    (hdec : ∀ pm, S.pksmParse body = some pm →
      S.decPkOk (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
        (addrValE st.party.other) (addrValE st.party) pm) :
    RunHsOk S (pqRecvInputs W st (wirePrekey :: body) rc) := by
  have ha : (pqRecvInputs W st (wirePrekey :: body) rc).argv =
      (Cmd.recv (partyAddress st.party.other)).argv := rfl
  have hin : (pqRecvInputs W st (wirePrekey :: body) rc).stdin = wirePrekey :: body := rfl
  refine ⟨fun _ _ _ _ h _ _ => ?_, fun _ _ _ _ pm hparse hown hme hstdin hpm => ?_⟩
  · rw [ha, parseArgs_recv] at h; cases h
  · rw [ha, parseArgs_recv] at hparse; injection hparse with hc; injection hc with hpeer
    rw [ownAddr_pqRecv] at hown; injection hown with hown'; subst hown'
    rw [addrParse_textBytes] at hme; injection hme with hme'
    rw [hin] at hstdin; injection hstdin with _ hrest; subst hrest
    rw [← hpeer, ← hme']; exact hdec pm hpm

def defaultExtrasF3 : UnreachedPqxdhPrimitives :=
  ⟨fun _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ => ([], []),
   fun _ => [], fun _ _ _ => false⟩

/-- Pure `RunSem` constructor matching `MainHops.cliRunSem` definitionally (`rfl`). -/
noncomputable def cliRunSemF3 (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) → SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (parseFn : List (BitVec 8) → Option PreKeySignalMessage) : RunSem :=
  ⟨encDef ⟨W.C, W.Q⟩ scopeIn, decSigDef ⟨W.C, W.Q⟩ scopeIn, initDef X ⟨W.C, W.Q⟩, decPk, parseFn,
   filesOk₀ scopeIn (fun _ => True), encOk₀ scopeIn, InitOk₀ ⟨W.C, W.Q⟩, decPkOk⟩

noncomputable abbrev cliRunSemParseNone (W : CliHooks) : RunSem :=
  cliRunSemF3 defaultExtrasF3 W (fun _ _ _ _ _ => some none) (fun _ _ _ _ => False) pksmParse

theorem runRel_pqRecv_parseNone_of_runSem {S : RunSem}
    (hS_files : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hS_pksm : S.pksmParse = pksmParse)
    (WP : PEParams) (st : PqParty) (hst : PqxdhPartyInSpecDomain WP st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32) (hnone : pksmParse body = none) :
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    runAns S inp = some none ∧ runRel S inp (some none) ∧
      observe inp.files (some none) = .exited 1 [] (filesOf inp.files) ∧
      CommitOk inp (MainResult.ofAnswer (some none)) := by
  have hans : runAns S (pqRecvInputs WP st (wirePrekey :: body) rc) = some none := by
    rw [runAns_pqRecvPrekey_eq, hS_pksm, hnone]
  have hrun : runRel S (pqRecvInputs WP st (wirePrekey :: body) rc) (some none) := by
    rw [← hans]
    exact ⟨domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc (Nat.succ_le_of_lt hbody),
      runFilesOk_pqRecv_cli_f3 hS_files WP st (wirePrekey :: body) rc hst,
      runEncOk_pqRecv S WP st (wirePrekey :: body) rc,
      runHsOk_pqRecvPrekey_body_f3 WP st body rc (fun pm hpm => by
        rw [hS_pksm, hnone] at hpm; cases hpm),
      rfl⟩
  exact ⟨hans, hrun, rfl, fun _ h => by cases h⟩

/-! ## 2. Pure `pqRecvInputs` Side-Condition Helpers & Generic F3 `pqRecvInputs` Combinators -/

private theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) : CoinsReadable (pqRecvInputs W st c rc) := by
  unfold CoinsReadable; rw [files_eq_entries]
  have hne : (normalizePath "coins").isEmpty = false := by rfl_kernel
  have hnsB : (stdioPaths.map normalizePath).contains (normalizePath "coins") = false := by rfl_kernel
  have hns : normalizePath "coins" ∉ stdioPaths.map normalizePath := fun hm =>
    Bool.noConfusion (hnsB.symm.trans (List.contains_iff_mem.mpr hm))
  rw [hne, initFsState_entries (cliInputs (pqRecvInputs W st c rc)) (normalizePath "coins") hns]
  change (filesFold (pqRecvInputs W st c rc).files (dirsFold (pqRecvInputs W st c rc).dirs {})).entries
      (normalizePath "coins") ≠ some .dir ∧
    ∀ bs, (filesFold (pqRecvInputs W st c rc).files (dirsFold (pqRecvInputs W st c rc).dirs {})).entries
      (normalizePath "coins") = some (.file bs) → bs.length ≤ fileCapBytes
  have hf : (pqRecvInputs W st c rc).files = encodeDir W st ++ [(coinsFile, keyToBytes32 rc)] := by
    simp [pqRecvInputs, pqInputs]
  rw [hf]; unfold filesFold; rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, FsState.setFile, FsState.setEntry, coinsFile]
  refine ⟨by simp, fun bs h => ?_⟩; simp at h; subst h; simp [keyToBytes32, fileCapBytes]

private theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf => ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
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

private theorem partyAddress_text_printable (P : Party) : PrintableAsciiArg (partyAddress P).text := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  refine ⟨fun h => ?_, fun ch hch => ?_⟩
  · have hl := congrArg String.utf8ByteSize h
    simp [partyAddress, Address.text, ht1, String.utf8ByteSize_append] at hl
  · rw [partyAddress_text_toList] at hch; cases P <;> revert ch hch <;> decide

private theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) : CliInputsOk (pqRecvInputs W st c rc) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [pqRecvInputs, pqInputs, Cmd.argv, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold PrintableAsciiArg; decide
    · exact partyAddress_text_printable st.party.other
  · have hlen : (partyAddress st.party.other).text.length = 38 := by
      generalize st.party.other = P; rw [← String.length_toList, partyAddress_text_toList]
      cases P <;> decide
    unfold ArgvFitsInitialStack pqRecvInputs pqInputs Cmd.argv
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlen]; decide

private theorem not_isStdinOverCap_of_stdin_le {i : Inputs} (h : i.stdin.length ≤ stdinCapBytes) :
    ¬ IsStdinOverCap i := fun ⟨_, hgt⟩ => Nat.not_lt.mpr h hgt

private theorem not_isSendOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) : ¬ IsSendOverCap (pqRecvInputs W st c rc) := by
  rintro ⟨⟨peer, hp⟩, -⟩
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  change parseArgs uuidTryParse ((Cmd.recv (partyAddress st.party.other)).argv.map bytesOfString) =
    some (.send peer) at hp
  rw [hp] at hv; injection hv with heq; subst heq; simp [CallV.tag, cmdTag] at htag

private theorem isStdinOverCap_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (h : stdinCapBytes < c.length) : IsStdinOverCap (pqRecvInputs W st c rc) := by
  obtain ⟨v, hv, htag⟩ := parseArgs_cmd (.recv (partyAddress st.party.other)) rfl
  exact ⟨⟨v, hv, by rw [htag]; simp [cmdTag]⟩, h⟩

theorem pqRecv_strict_obs_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {o : Outcome}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a = o ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if c.length > stdinCapBytes then .exited 2 [] (filesOf inp.files) else o) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  have hprogEq := (cliProgExtPlacedSigAt_cliExternsPlaced_eq mpl mmpl W).symm
  rw [cliRunPlacedSig_eq_on_input_of_progEq2 hprogEq rfl]
  by_cases hstin : c.length > stdinCapBytes
  · simp only [hstin, ↓reduceIte]
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_stdinOverCap
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      (isStdinOverCap_pqRecvInputs WP st c rc hstin)
  · simp only [hstin, ↓reduceIte]
    obtain ⟨a, hrun, hobs, hcommit⟩ := hclause (Nat.le_of_not_gt hstin)
    exact cliRunExtOnInputsSigAt_of_strict_b2_needLocks_call_obs
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl W)
      H.elfStaticOk H.tokenCells H.fsEq (H.codeLoaded W) (H.harness W) hmainW H.stkLo H.stkHi
      (cliInputsOk_pqRecvInputs WP st c rc) (inputsLoadable_pqRecvInputs WP st c rc hst)
      hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
      (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin))
      hobs (coinsReadable_pqRecvInputs WP st c rc) hcommit

theorem pqRecv_outcomeOrOom_obs_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {o : Outcome}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a = o ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) inp
      (· = if c.length > stdinCapBytes then .exited 2 [] (filesOf inp.files) else o) :=
  outcomeOrExcusedAbort_of_eq (pqRecv_strict_obs_of_f3B2NeedLocks H hmainW hst hclause)

theorem pqRecv_strict_pred_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {Pred : Outcome → Prop}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        Pred (observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a) ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    ∃ o : Outcome,
      cliRunPlacedSig mpl mmpl elf W inp = some o ∧
      (if c.length > stdinCapBytes then o = .exited 2 [] (filesOf inp.files) else Pred o) := by
  by_cases hstin : c.length > stdinCapBytes
  · have h := pqRecv_strict_obs_of_f3B2NeedLocks (rc := rc)
      (o := .exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files)) H hmainW hst
      (fun hle => False.elim (Nat.not_lt_of_ge hle hstin))
    dsimp only at h ⊢; simp only [hstin, ↓reduceIte] at h ⊢; exact ⟨_, h, rfl⟩
  · obtain ⟨a, hrun, hp, hcommit⟩ := hclause (Nat.le_of_not_gt hstin)
    have h := pqRecv_strict_obs_of_f3B2NeedLocks (rc := rc) H hmainW hst
      (fun _ => ⟨a, hrun, rfl, hcommit⟩)
    dsimp only at h ⊢; simp only [hstin, ↓reduceIte] at h ⊢; exact ⟨_, h, hp⟩

theorem pqRecv_outcomeOrOom_pred_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage} {W : CliHooks} {Run : Inputs → RunAnswer → Prop}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmainW : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {Pred : Outcome → Prop}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hclause : c.length ≤ stdinCapBytes →
      ∃ a, Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a ∧
        Pred (observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a) ∧
        CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (MainResult.ofAnswer a)) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st c rc
    OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
      (cliRunPlacedSig mpl mmpl elf W) inp
      (fun o => if c.length > stdinCapBytes then o = .exited 2 [] (filesOf inp.files) else Pred o) :=
  Or.inl (pqRecv_strict_pred_of_f3B2NeedLocks H hmainW hst hclause)

/-! ## 3. `recvOverStdinCap` -/

theorem d3_recvOverStdinCap_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hover : (wirePrekey :: body).length > stdinCapBytes) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp = some (.exited 2 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, _⟩ := hmain H.base547NeZero defaultExtrasF3 W
  have h := pqRecv_strict_obs_of_f3B2NeedLocks (rc := rc) (o := .exited 2 []
      (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc).files)) H hmainW hst
    (fun hle => False.elim (Nat.not_lt_of_ge hle hover))
  dsimp only at h ⊢; simpa only [hover, ↓reduceIte] using h

theorem d3_recvOverStdinCap_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        (wirePrekey :: body).length > stdinCapBytes →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp (· = .exited 2 [] (filesOf inp.files)) :=
  fun W st hst body rc hover =>
    outcomeOrExcusedAbort_of_eq (d3_recvOverStdinCap_strict_of_f3 H hmain W st hst body rc hover)

/-! ## 4. `CliPqOrD3RecvInputs`, `pqD3ScopedRun`, & `pksmParseNone` -/

def CliPqOrD3RecvInputs (WP : PEParams) (i : Inputs) : Prop :=
  CliPqxdhInputs WP i ∨
  ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
    PqxdhPartyInSpecDomain WP st ∧ i = pqRecvInputs WP st ct rc

def pqD3ScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop) (i : Inputs) (a : RunAnswer) : Prop :=
  CliPqOrD3RecvInputs WP i ∧ Run₀ i a

theorem pqScopedRun_le_pqD3ScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop)
    {i : Inputs} {a : RunAnswer} (h : CliPqxdhInputs WP i ∧ Run₀ i a) :
    pqD3ScopedRun WP Run₀ i a := ⟨Or.inl h.1, h.2⟩

theorem mainCaseB2_mono_run {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    (hle : ∀ i a, Run₁ i a → Run₂ i a) {SendOverCap StdinOverCap : Inputs → Prop}
    {i : Inputs} {r : MainResult} (h : MainCaseB2 Run₁ SendOverCap StdinOverCap i r) :
    MainCaseB2 Run₂ SendOverCap StdinOverCap i r := by
  cases h with
  | usage h1 h2 => exact .usage h1 h2
  | stdinOverCap h1 => exact .stdinOverCap h1
  | sendOverCap h1 h2 h3 => exact .sendOverCap h1 h2 h3
  | call hrun h1 h2 h3 h4 => exact .call (hle _ _ hrun) h1 h2 h3 h4

theorem subroutine_ok_b2MainSpecTightNeedLocksFineAt_antitone
    {prog : Program} {entry_pc libcAddr : BitVec 64} {CodeOk : Memory → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {stk : Nat} {Statics : SepProp} {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    {inputsOf : Inputs → ProcessInputs}
    (hle : ∀ i a, Run₁ i a → Run₂ i a)
    (hok : subroutine_ok prog entry_pc
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run₂ inputsOf)) :
    subroutine_ok prog entry_pc
      (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk A lim st stk Statics Run₁ inputsOf) := by
  refine subroutine_ok.of_codeLoaded fun g R s0 hpc hst hpre hal _ =>
    hok.mono_outcome g R s0 hpc hst ?_ hal fun _ hout => hout
  simp only [b2MainSpecTightNeedLocksFineAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hpre.1.1, mainCaseB2_mono_run hle hpre.1.2.1, hpre.1.2.2⟩, hpre.2⟩

def MainOkParseNoneD3F3
    (mpl mmpl : MultiPlacement) (CodeOk : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (rc : BitVec 256),
          body.length < 2 ^ 32 → pksmParse body = none →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧ observe inp.files a = .exited 1 [] (filesOf inp.files) ∧
            CommitOk inp (MainResult.ofAnswer a)

theorem mainOkParseNoneD3F3_of_runSem
    {mpl mmpl : MultiPlacement} {CodeOk : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (SOf : CliHooks → RunSem)
    (hS_files : ∀ W, (SOf W).filesOk = filesOk₀ scopeIn (fun _ => True))
    (hS_pksm : ∀ W, (SOf W).pksmParse = pksmParse)
    (hmainS : mpl.base 547 ≠ 0#64 → ∀ W : CliHooks, ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (SOf W))) cliProcessInputs)) :
    MainOkParseNoneD3F3 mpl mmpl CodeOk libcAddr brkStart stk := by
  intro hDropNz W
  refine ⟨pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (SOf W)), hmainS hDropNz W,
    fun st hst body rc hbody hnone => ?_⟩
  obtain ⟨_, hrun, hobs, hcommit⟩ :=
    runRel_pqRecv_parseNone_of_runSem (hS_files W) (hS_pksm W) ⟨W.C, W.Q⟩ st hst body rc hbody hnone
  exact ⟨some none, ⟨Or.inr ⟨st, wirePrekey :: body, rc, hst, rfl⟩, hrun⟩, hobs, hcommit⟩

theorem d3_pksmParseNone_strict_of_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (W : CliHooks) (st : PqParty) (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (body : List (BitVec 8)) (rc : BitVec 256)
    (hbody : body.length < 2 ^ 32) (hnone : pksmParse body = none) :
    let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
    cliRunPlacedSig mpl mmpl elf W inp =
      some (if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
        else .exited 1 [] (filesOf inp.files)) := by
  obtain ⟨Run, hmainW, hcl⟩ := hparseNone H.base547NeZero W
  exact pqRecv_strict_obs_of_f3B2NeedLocks H hmainW hst (fun _ => hcl st hst body rc hbody hnone)

theorem d3_pksmParseNone_f3
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop} {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hparseNone : MainOkParseNoneD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    ∀ (W : CliHooks) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      ∀ (body : List (BitVec 8)) (rc : BitVec 256),
        body.length < 2 ^ 32 → pksmParse body = none →
        let inp := pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc
        OutcomeOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)
          (cliRunPlacedSig mpl mmpl elf W) inp
          (· = if (wirePrekey :: body).length > stdinCapBytes then .exited 2 [] (filesOf inp.files)
            else .exited 1 [] (filesOf inp.files)) :=
  fun W st hst body rc hbody hnone =>
    outcomeOrExcusedAbort_of_eq
      (d3_pksmParseNone_strict_of_f3 H hparseNone W st hst body rc hbody hnone)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
