/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopATailPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBStepPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# Whole-Program `FitsEnv` to `MainEntryBudgetFitsCap` Bridge

Discharges `MainEntryBudgetFitsCap` and `MainEntryBudgetFitsCapOf` from whole-`main` `FitsEnv`
(`RealCliMainBinaryEnvOf E i` on `Dom i`, paired with `SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs`
on `argvLen ≤ 1820`) and a domain-scoped `RunEnv → CliRunBinaryEnv` inclusion, parameterized over
any callee-envelope family `E : RunCall → CliRunCalleeEnvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal

open Arm64 (pageAlignUp)
open Arm64.Obj (Image)
open Arm64.Process (bytesOfString initFsState)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (GhostState IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage PreKeySignalMessage SessionRecord StoreCall fullTrace messageDecryptSignal
   messageDecryptSignal_trace_prefix messageEncrypt messageEncrypt_trace_prefix)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields RecordExtras UnreachedPqxdhPrimitives initiateTapeLen
   partyAddressName pqxdhSpqrModel recvPrekeyState wirePrekey wireWhisper)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs PqParty baseKeysFile bundleDir identityFile
   oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress pqInitInputs pqInputs pqRecvInputs
   pqSendInputs sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk DirGhost IdGhost KyberGhost RunAnswer StoresGhost addressText baseKeysName cliInputs
   keyName pathOf removePreKey utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV DirWrOk IoModel RunCall StoreCallPeerPlaced StoresWrOk addrParse argvFits_length_le cliIo
   inputOf keyName_length messageDecryptSignal_calls_peer_placed messageEncrypt_calls_peer_placed
   namedWrites namedWrites_ascii okPeerPath parseArgs saveUpd_own saveUpd_peers_path storesDirs
   storesDirs_writes)
open CryptoVerification.SignalSession.Cli.RunCompose
  (BundleV RunSem SlotAns finish readBundleV runAns runFiles runRel unixEpoch)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm cliAnswers cliFinal cliStep decPkAcceptWith decPkDef decPkDefD2c
   decPkDefD2c_eq_decPkDef_of_match decPkDefD2c_eq_decPkDef_of_noCurrent
   decPkDefD2c_eq_decPkDef_of_untrusted decPkDefD2c_namedWrites_sub decPkDefD2c_of_load_err
   decPkDefD2c_of_not_match decPkDef_namedWrites_sub decSigDef decSigKey encDef encKey initDef
   initParty pkRecvCoins pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrValE runAns_pqInit_eq runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq
   runAns_pqSend_eq)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn)
open CryptoVerification.SignalSession.CliExt (pathStr)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FreeOnlyEvs SeqEnv
   fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineBudget FineScale FineStepBound FineStepBound_mono_meta Guaranteed63Threshold MmapThresholdReq
   fineCostModel fineFootprint fineMaxDynIvs fineMaxGroups fineMaxMetaAreas finePeak63Bytes
   finePeak63Count fineStepReserve toFineEvent)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (addrParse_name_bounds specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliWriteFileEnv M1PhaseEnv M2CollectEnv M2CollectStepEnv M5DirStepEnv M5LoopAEntryEnv M5PhaseEnv
   M5WriteStepEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf realCliMainBinaryEnvOf_90pct_fitsEnv_concrete
   realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_concrete realCliMainBinaryEnvOf_fitsEnv_concrete)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal (cliRealNinetyPctOneGiB)
open LibsignalBinary.Proofs.PeakBudget.MainResidualFitsEnv
  (M2PhaseEnv PostM1SetupEnv PostSetupTailEnv fitsEnv_freeOnly_of_st3 fitsEnv_m2EarlyExit_of_st1
   fitsEnv_m3EarlyExit_of_st2 fitsEnv_run_and_st4_of_st3 fitsEvents_and_fitsEnv_stepEvents_of_seqEnv
   fitsEvents_and_st2_of_st1 fitsEvents_and_st3_of_st2 m3BoundedSetupEnv_nil mainSt01_of_st0
   mainSt0_init_of_fitsEnv mainSt4 postM1SetupEnv_nil postM1SetupEnv_of_m2Phase
   postM1SetupEnv_of_seq_m2Phase_m3 realCliMainBinaryEnvOf_eq_seqEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (AddrOptBoundedEnv BoundedReadFileEnv BoundedReadStdinEnv BundleOptBoundedEnv
   CliMainBoundedSetupEnv M2CollectFullEnv M3BoundedSetupEnv ValidPostSetupWitness
   addrOptBoundedEnv_nil addrOptBoundedEnv_of_alloc_le boundedReadFileEnv_of_readFileRuleEnv_cliIo
   bundleOptBoundedEnv_nil bundleOptBoundedEnv_of_alloc_le
   cliMainSetupEarlyExit_90pct_fitsEnv_le1820 cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (FineBudgetDom MainEntryBudgetFitsCap MainEntryBudgetFitsCapOf domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
  (cliRunSemD2c_placed pqScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.StepsPlacedBudget
  (M2CollectLoopEnv m2GrowEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitPlacedBudget
  (initBranchEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.KeygenPlacedBudget
  (keygenBranchEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.SendRecvPlacedBudget
  (sendRecvEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2DispatchPlacedBudget
  (m2DispatchEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2PlacedBudget (M2PreDeallocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3PlacedBudget (M3Env M3EnvReadOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DirStepPlacedBudget (M5DirOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPlacedBudget
  (M5LoopARestOkEnv M5LoopAStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopAPathPlacedBudget
  (M5LoopABuildPathEnv m5LoopABuildPathEvents m5LoopAPathCap)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBPlacedBudget (M5LoopBRestOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBStepPlacedBudget (M5LoopBStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopBWritePlacedBudget
  (M5LoopBErrNonemptyEnv M5LoopBNonemptyStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5LoopPlacedBudget (M5DirsOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5PlacedBudget (M5Env)

/-! ## 1. Sequential and `FreeOnlyEvs` Algebra -/

private theorem seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

private theorem freeOnlyEvs_nil : FreeOnlyEvs [] :=
  fun _ h => nomatch h

private theorem freeOnlyEvs_append {xs ys : List AllocEvent}
    (hx : FreeOnlyEvs xs) (hy : FreeOnlyEvs ys) :
    FreeOnlyEvs (xs ++ ys) := by
  intro e he
  rcases List.mem_append.mp he with h1 | h2
  · exact hx e h1
  · exact hy e h2

private theorem freeOnlyEvs_rustDealloc (sz align : Nat) :
    FreeOnlyEvs (rustDeallocEvents sz align) :=
  FreeOnlyEvs.singleton align sz

/-! ## 2. `M2` Envelope Inclusion (`M2PreDeallocEnv` & `m2DispatchEvents` → `M2PhaseEnv`) -/

private theorem iterSeqEnv_m2CollectStep_nil :
    ∀ xs : List Nat, IterSeqEnv M2CollectStepEnv xs []
  | [] => rfl
  | _ :: _ => Or.inl (Or.inl rfl)

private theorem m2CollectLoopEnv_to_iterSeqEnv {n k : Nat} {evs : List AllocEvent}
    (h : M2CollectLoopEnv n k evs) :
    IterSeqEnv M2CollectStepEnv (List.range' k (n - k)) evs := by
  induction h with
  | done =>
    exact iterSeqEnv_m2CollectStep_nil _
  | @skip k evs hk_lt _ ih =>
    have hrem : n - k = (n - (k + 1)) + 1 := by omega
    rw [hrem]
    exact Or.inr ⟨[], evs, rfl, Or.inl rfl, ih⟩
  | @grow k evs _ hk_lt _ ih =>
    have hrem : n - k = (n - (k + 1)) + 1 := by omega
    rw [hrem]
    exact Or.inr ⟨m2GrowEventsAt k, evs, rfl, Or.inr rfl, ih⟩

private theorem entryM2CollectEnv_imp_full {n : Nat} {evs : List AllocEvent}
    (h :
      LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Collect.EntryPlacedBudget.M2CollectEnv
        n evs) :
    M2CollectFullEnv n evs :=
  Or.inr (seqEnv_mono (fun _ hx => hx) (fun _ hy => m2CollectLoopEnv_to_iterSeqEnv hy) h)

private theorem addressEvents_in_addrOpt (uuidParse : UuidParser) (bs : List (BitVec 8)) :
    AddrOptBoundedEnv (addressEvents uuidParse bs) := by
  unfold addressEvents
  cases hp : addrParse uuidParse bs with
  | none => exact addrOptBoundedEnv_nil
  | some a =>
    exact addrOptBoundedEnv_of_alloc_le
      (Nat.le_trans (addrParse_name_bounds uuidParse bs hp).1 (by decide))

private theorem argv_elem_bytes_le_16384 {argv : List String}
    (hfit : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384)
    {a : String} (ha : a ∈ argv) :
    (bytesOfString a).length ≤ 16384 := by
  have hlen : (bytesOfString a).length = a.length := by
    unfold bytesOfString
    simp [String.length]
  have hmem : a.length + 1 + 8 ∈ argv.map (fun s => s.length + 1 + 8) :=
    List.mem_map_of_mem ha
  have hle : a.length + 1 + 8 ≤ (argv.map fun s => s.length + 1 + 8).sum :=
    List.le_sum_of_mem hmem
  omega

private theorem m2DispatchEvents_in_addr_bundle {i : Inputs} (hok : CliInputsOk i) :
    SeqEnv AddrOptBoundedEnv (SeqEnv BundleOptBoundedEnv FreeOnlyEvs)
      (m2DispatchEvents uuidTryParse (i.argv.map bytesOfString)) := by
  rcases i with ⟨argv, stdin, files⟩
  match argv with
  | [] => exact Or.inl addrOptBoundedEnv_nil
  | [_] => exact Or.inl addrOptBoundedEnv_nil
  | [a1, a2] =>
    dsimp only [List.map, m2DispatchEvents, sendRecvEvents]
    split
    · exact Or.inl (addressEvents_in_addrOpt uuidTryParse (bytesOfString a2))
    · exact Or.inl addrOptBoundedEnv_nil
  | [a1, a2, a3] =>
    dsimp only [List.map, m2DispatchEvents]
    split
    · unfold initBranchEvents
      split
      · cases hp : addrParse uuidTryParse (bytesOfString a2) with
        | none => exact Or.inl addrOptBoundedEnv_nil
        | some peer =>
          have hpeer : peer.name.length ≤ 16384 :=
            Nat.le_trans (addrParse_name_bounds uuidTryParse (bytesOfString a2) hp).1 (by decide)
          have hbs3 : (bytesOfString a3).length ≤ 16384 :=
            argv_elem_bytes_le_16384 hok.2 (by simp)
          exact Or.inr ⟨_, _, rfl, addrOptBoundedEnv_of_alloc_le hpeer,
            Or.inl (bundleOptBoundedEnv_of_alloc_le hbs3)⟩
      · exact Or.inl addrOptBoundedEnv_nil
    · split
      · unfold keygenBranchEvents
        split
        · exact Or.inl (addressEvents_in_addrOpt uuidTryParse (bytesOfString a2))
        · exact Or.inl addrOptBoundedEnv_nil
      · exact Or.inl addrOptBoundedEnv_nil
  | _ :: _ :: _ :: _ :: _ => exact Or.inl addrOptBoundedEnv_nil

private theorem seqEnv_append_freeOnly_tail {E₁ E₂ : List AllocEvent → Prop}
    (h2nil : E₂ [])
    {evs ef : List AllocEvent}
    (h : SeqEnv E₁ (SeqEnv E₂ FreeOnlyEvs) evs) (hf : FreeOnlyEvs ef) :
    SeqEnv E₁ (SeqEnv E₂ FreeOnlyEvs) (evs ++ ef) := by
  rcases h with h1 | ⟨e1, e23, rfl, h1, h23⟩
  · exact Or.inr ⟨evs, ef, rfl, h1, Or.inr ⟨[], ef, rfl, h2nil, hf⟩⟩
  · rcases h23 with h2 | ⟨e2, e3, rfl, h2, h3⟩
    · exact Or.inr ⟨e1, e23 ++ ef, List.append_assoc e1 e23 ef, h1,
        Or.inr ⟨e23, ef, rfl, h2, hf⟩⟩
    · exact Or.inr ⟨e1, e2 ++ (e3 ++ ef), by simp [List.append_assoc], h1,
        Or.inr ⟨e2, e3 ++ ef, rfl, h2, freeOnlyEvs_append h3 hf⟩⟩

private theorem m2PreDeallocEnv_imp_m2PhaseEnv {i : Inputs} (hok : CliInputsOk i)
    {evs : List AllocEvent}
    (h : M2PreDeallocEnv uuidTryParse (i.argv.map bytesOfString) evs) :
    M2PhaseEnv i.argv.length evs := by
  unfold M2PreDeallocEnv at h
  rw [List.length_map] at h
  refine seqEnv_mono (fun _ hc => entryM2CollectEnv_imp_full hc) (fun _ hd => ?_) h
  rw [hd]
  exact m2DispatchEvents_in_addr_bundle hok

/-! ## 3. `M3` Envelope Inclusion (`M3EnvReadOf` / `M3Env` → `M3BoundedSetupEnv`) -/

/-- `BoundedReadFileEnv` membership of the compiled `2 MiB` over-cap `read_file` schedule
(`readFileOverCapEvents`). -/
theorem boundedReadFileEnv_overCapSchedule :
    BoundedReadFileEnv
      (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++ rustDeallocEvents 2097152 1) := by
  rw [specCliIoReadSchedule_events_eq 9 2097152]
  exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨2097152, rfl⟩, FreeOnlyEvs.singleton 1 2097152⟩))

private theorem readStdinBoundedEnv_imp_bounded {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : ReadStdinBoundedEnv bs evs) :
    BoundedReadStdinEnv evs := by
  rcases h with h1 | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · by_cases hle : bs.length ≤ 1048576
    · simp only [hle, ↓reduceIte] at h1
      exact Or.inr (Or.inl ⟨bs, hle, h1⟩)
    · simp only [hle, ↓reduceIte] at h1
      exact Or.inl h1
  · rw [specCliIoReadSchedule_events_eq 8 bs.length]
    exact Or.inr (Or.inr (Or.inl ⟨bs.length, rfl⟩))
  · rw [specCliIoReadSchedule_events_eq 8 1048576]
    exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, ⟨1048576, rfl⟩, FreeOnlyEvs.singleton 1 1048576⟩))

theorem m3EnvReadOf_imp_m3BoundedSetupEnv
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (i : Inputs) (c : CallV) {evs : List AllocEvent}
    (h : M3EnvReadOf ReadStdinBoundedEnv ReadEnv i c evs) :
    M3BoundedSetupEnv evs := by
  unfold M3EnvReadOf at h
  by_cases htag : 1 < c.tag
  · simp only [htag, ↓reduceIte] at h
    exact seqEnv_mono
      (fun _ hs => readStdinBoundedEnv_imp_bounded hs)
      (fun _ hc => Or.inl (hReadSub _ _ _ hc))
      h
  · simp only [htag, ↓reduceIte] at h
    exact Or.inr ⟨[], evs, rfl, Or.inl rfl,
      Or.inl (hReadSub _ _ _ h)⟩

private theorem m3Env_imp_m3BoundedSetupEnv (i : Inputs) (c : CallV) {evs : List AllocEvent}
    (h : M3Env cliIo i c evs) :
    M3BoundedSetupEnv evs :=
  m3EnvReadOf_imp_m3BoundedSetupEnv
    (fun files path _ hc => boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hc)
    i c h

/-! ## 4. `M4` Stdin-Cap Transfer (`(inputOf i c).length ≤ stdinCapBytes → i.stdin.length ≤ msgCapBytes`) -/

theorem stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf
    {WP : PEParams} {st : PqParty} {ct : List (BitVec 8)} {rc : BitVec 256} {c : CallV}
    (hp : parseArgs uuidTryParse ((pqRecvInputs WP st ct rc).argv.map bytesOfString) = some c)
    (hin : (inputOf (pqRecvInputs WP st ct rc) c).length ≤ stdinCapBytes) :
    (pqRecvInputs WP st ct rc).stdin.length ≤ msgCapBytes := by
  have htag : 1 < c.tag := by
    have ha : (pqRecvInputs WP st ct rc).argv =
        (CryptoVerification.SignalSession.Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [ha, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hp
    injection hp with hc
    subst hc
    dsimp only [CallV.tag]
    decide
  have hinp : inputOf (pqRecvInputs WP st ct rc) c = (pqRecvInputs WP st ct rc).stdin := by
    unfold inputOf
    cases hc : c <;> simp_all [CallV.tag]
  rw [hinp] at hin
  exact hin

theorem stdin_le_msgCapBytes_of_pqInitInputs
    (WP : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    (pqInitInputs WP st b t).stdin.length ≤ msgCapBytes :=
  Nat.zero_le _

theorem stdin_le_msgCapBytes_of_pqInputs_and_inputOf {WP : PEParams} {i : Inputs} {c : CallV}
    (hi : CliPqxdhInputs WP i)
    (hp : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hin : (inputOf i c).length ≤ stdinCapBytes) :
    i.stdin.length ≤ msgCapBytes := by
  rcases hi with ⟨st, _, h1 | h2 | h3 | h4 | h5⟩
  · rcases h1 with ⟨_, b, t, rfl⟩
    exact Nat.zero_le _
  · rcases h2 with ⟨m, r, _, rfl⟩
    have htag : 1 < c.tag := by
      have ha : (pqSendInputs WP st m r).argv =
          (CryptoVerification.SignalSession.Cmd.send (partyAddress st.party.other)).argv := rfl
      rw [ha, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_send] at hp
      injection hp with hc
      subst hc
      dsimp only [CallV.tag]
      decide
    have hinp : inputOf (pqSendInputs WP st m r) c = (pqSendInputs WP st m r).stdin := by
      unfold inputOf
      cases hc : c <;> simp_all [CallV.tag]
    rw [hinp] at hin
    exact hin
  · rcases h3 with ⟨ct, rc, _, rfl⟩
    have htag : 1 < c.tag := by
      have ha : (pqRecvInputs WP st (wireWhisper :: ct) rc).argv =
          (CryptoVerification.SignalSession.Cmd.recv (partyAddress st.party.other)).argv := rfl
      rw [ha, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hp
      injection hp with hc
      subst hc
      dsimp only [CallV.tag]
      decide
    have hinp : inputOf (pqRecvInputs WP st (wireWhisper :: ct) rc) c =
        (pqRecvInputs WP st (wireWhisper :: ct) rc).stdin := by
      unfold inputOf
      cases hc : c <;> simp_all [CallV.tag]
    rw [hinp] at hin
    exact hin
  · rcases h4 with ⟨m, rc, _, rfl⟩
    have htag : 1 < c.tag := by
      have ha : (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).argv =
          (CryptoVerification.SignalSession.Cmd.recv (partyAddress st.party.other)).argv := rfl
      rw [ha, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hp
      injection hp with hc
      subst hc
      dsimp only [CallV.tag]
      decide
    have hinp : inputOf (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) c =
        (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).stdin := by
      unfold inputOf
      cases hc : c <;> simp_all [CallV.tag]
    rw [hinp] at hin
    exact hin
  · rcases h5 with ⟨ct, rc, _, _, _, rfl⟩
    have htag : 1 < c.tag := by
      have ha : (pqRecvInputs WP st ct rc).argv =
          (CryptoVerification.SignalSession.Cmd.recv (partyAddress st.party.other)).argv := rfl
      rw [ha, CryptoVerification.SignalSession.Cli.RunRefine.parseArgs_recv] at hp
      injection hp with hc
      subst hc
      dsimp only [CallV.tag]
      decide
    have hinp : inputOf (pqRecvInputs WP st ct rc) c = (pqRecvInputs WP st ct rc).stdin := by
      unfold inputOf
      cases hc : c <;> simp_all [CallV.tag]
    rw [hinp] at hin
    exact hin

/-! ## 5. `M5` Write-Count and Path-Length Bounds on `cliRunSemD2c_placed` -/

private theorem identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem byteArray_toList_eq_data_local : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def kutf8Local (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem utf8_eq_kutf8Local (s : String) : utf8 s = kutf8Local s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8Local, List.utf8Encode, byteArray_toList_eq_data_local]

private theorem utf8_append_local (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [utf8_eq_kutf8Local, utf8_eq_kutf8Local, utf8_eq_kutf8Local]
  simp [kutf8Local, String.toList_append, List.flatMap_append]

private theorem pathOf_id_addrValE_local (P : Party) :
    pathOf (utf8 "identities") (addrValE P).name = utf8 (identityFile (partyAddressName P)) := by
  have hne : utf8 "identities" ≠ [] := by rw [utf8_eq_kutf8Local]; decide
  simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
  rw [← utf8_append_local, ← utf8_append_local]
  rfl

private theorem pathOf_sess_addrValE_local (P : Party) :
    pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
  have hne : utf8 "sessions" ≠ [] := by rw [utf8_eq_kutf8Local]; decide
  have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
    have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
    simp only [addressText, addrValE, CryptoVerification.SignalSession.Cli.decimalText, h1,
      CryptoVerification.SignalSession.Address.text, partyAddress]
    rw [← utf8_append_local, ← utf8_append_local]
  rw [had]
  simp only [pathOf, hne, ↓reduceIte, sessionFile]
  rw [← utf8_append_local, ← utf8_append_local]
  rfl

private theorem okPeerPath_id_local (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  rw [pathOf_id_addrValE_local]
  refine ⟨?_, .inl ?_⟩
  · rw [utf8_eq_kutf8Local]
    intro b hb
    have hall :
        (kutf8Local (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [utf8_eq_kutf8Local]
    cases P <;> decide

private theorem utf8_inj_local {s₁ s₂ : String} (h : utf8 s₁ = utf8 s₂) : s₁ = s₂ := by
  have hmap := congrArg (List.map UInt8.ofBitVec) h
  have hrt : ∀ b : UInt8, UInt8.ofBitVec (BitVec.ofNat 8 b.toNat) = b := fun b => by
    simp [UInt8.ofBitVec_toBitVec]
  simp only [utf8, List.map_map, Function.comp_def, hrt, List.map_id'] at hmap
  have hba : s₁.toByteArray = s₂.toByteArray := by
    rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
    rcases hs1 : s₁.toUTF8 with ⟨⟨xs₁⟩⟩
    rcases hs2 : s₂.toUTF8 with ⟨⟨xs₂⟩⟩
    rw [hs1, hs2, byteArray_toList_eq_data_local, byteArray_toList_eq_data_local] at hmap
    dsimp only at hmap
    subst hmap
    rfl
  exact String.toByteArray_inj.mp hba

private theorem sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  have h1 : toString (1 : Nat) = "1" := by
    apply utf8_inj_local
    have hdt : utf8 (toString (1 : Nat)) = [BitVec.ofNat 8 (0x30 + 1)] :=
      CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit 1 (by omega)
    have hu1 : utf8 "1" = [BitVec.ofNat 8 (0x30 + 1)] := by
      rw [utf8_eq_kutf8Local]; decide
    exact hdt.trans hu1.symm
  simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text, h1,
    String.append_assoc]

private theorem okPeerPath_sess_local (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  rw [pathOf_sess_addrValE_local]
  refine ⟨?_, .inr ?_⟩
  · rw [utf8_eq_kutf8Local, sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (kutf8Local ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [utf8_eq_kutf8Local, sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar
      dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

private theorem string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, byteArray_toList_eq_data_local]
  rw [hutf]
  exact list_length_le_flatMap_utf8EncodeChar l

private theorem u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  have h1 : (toString (1 : Nat)).length ≤ 10 := u32_toString_len_le_10 1#32
  unfold sessionFile partyAddress CryptoVerification.SignalSession.Address.text
  dsimp only
  simp only [String.length_append]
  have hs : ("sessions/").length = 9 := by decide
  have hd : (".").length = 1 := by decide
  cases P
  · have hp : (partyAddressName Party.A).length ≤ 40 := by decide
    omega
  · have hp : (partyAddressName Party.B).length ≤ 40 := by decide
    omega

private theorem oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile
  rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := u32_toString_len_le_10 id
  unfold baseKeysFile
  simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := u32_toString_len_le_10 id
  unfold oneTimePreKeyFile
  rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons hd tl ih =>
    unfold DirGhost.setOrPush
    split
    · simp
    · simp only [List.length_cons]
      omega

private theorem dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact setOrPush_length_le_succ d.changed k v

private theorem saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem cliStep_writes_length_le_succ (F : FsFiles) (g : StoresGhost)
    (c : StoreCall AddrVal (List (BitVec 8))) :
    (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
  cases c with
  | loadSession _ => exact Nat.le_succ _
  | isTrustedIdentity _ _ _ => exact Nat.le_succ _
  | saveIdentity rem k =>
    obtain ⟨hp, ho⟩ := saveUpd_peers_writes_length_le_succ F g.identity rem k
    dsimp only [cliStep, StoresGhost.writes]
    rw [ho]
    simp only [List.length_append]
    omega
  | storeSession rem r =>
    dsimp only [cliStep, StoresGhost.writes]
    have hs := dirPut_writes_length_le_succ g.sessions (addressText rem)
      (CryptoVerification.E2E.Record.encodeRecord r)
    simp only [List.length_append]
    omega

private theorem foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    dsimp only [List.foldl, List.length_cons]
    have h1 := cliStep_writes_length_le_succ F g c
    have h2 := foldl_cliStep_writes_length_le F cs (cliStep F g c)
    omega

private theorem namedWrites_length_le (ws : List (List (BitVec 8) × List (BitVec 8))) :
    (namedWrites ws).length ≤ ws.length := by
  unfold namedWrites
  exact Nat.le_of_eq (List.length_map _)

private theorem pathStr_length_of_ascii {p : List (BitVec 8)}
    (_hasc : ∀ b ∈ p, b.toNat < 128) :
    (pathStr p).length = p.length := by
  unfold pathStr
  simp [String.length]

private theorem peer_writes_bounds_of_storesWrOk {P : Party} {g' : StoresGhost}
    (hg : g'.writes.length ≤ 4)
    (hok : StoresWrOk (okPeerPath P) g') :
    (namedWrites g'.writes).length ≤ 4 ∧
      ∀ q ∈ namedWrites g'.writes, q.1.length ≤ 64 := by
  refine ⟨Nat.le_trans (namedWrites_length_le g'.writes) hg, fun q hq => ?_⟩
  have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
    fun w hw => (hok.writes w hw).1
  rw [namedWrites_ascii g'.writes hasc] at hq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  rcases (hok.writes w hw).2 with hp | hp <;> rw [hp]
  · exact identityFile_len_le_64 P
  · exact sessionFile_len_le_64 P

private theorem initDef_writes_bounds {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {bv : BundleV} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : Unit}
    (h : initDef X W F (addrValE P) me bv coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold initDef at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · split at h
      · split at h
        · cases h
        · next x gs _ =>
          injection h with h1
          injection h1 with h2
          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
          obtain ⟨hp, ho⟩ := saveUpd_peers_writes_length_le_succ F StoresGhost.opened.identity
            (addrValE P) bv.idKey
          have hs := dirPut_writes_length_le_succ StoresGhost.opened.sessions
            (addressText (addrValE P))
            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
          have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
          have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
          have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
          dsimp only [StoresGhost.writes]
          rw [ho]
          simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
          omega
      · cases h

private theorem encDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {ptext coins : List (BitVec 8)}
    {g' : StoresGhost} {v : CiphertextMessage}
    (h : encDef W Scope F (addrValE P) me ptext coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold encDef at h
  split at h
  · next m calls heq =>
    injection h with h1
    injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨k, r, -, hpref⟩ :=
      messageEncrypt_trace_prefix W.C protoSignalCodec (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (encKey Scope F (addrValE P)))
        ptext (addrValE P) me unixEpoch coins
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]
    omega
  · cases h
  · cases h

private theorem decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1
    injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨k, r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]
    omega
  · cases h
  · cases h

private theorem storesWrOk_foldl_local (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ okPeerPath_id_local P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ okPeerPath_sess_local P) _ } hp hs

private theorem storesWrOk_encDef_local {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {ptext coins : List (BitVec 8)}
    {g' : StoresGhost} {v : CiphertextMessage}
    (h : encDef W Scope F (addrValE P) me ptext coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold encDef at h
  split at h
  · next msg calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageEncrypt_calls_peer_placed
      W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (encKey Scope F (addrValE P)))
      ptext (addrValE P) me unixEpoch coins
    rw [heq] at hc
    exact storesWrOk_foldl_local F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem storesWrOk_decSigDef_local {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (coinsOf coins)
    rw [heq] at hc
    exact storesWrOk_foldl_local F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem decPkAcceptWith_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {F : FsFiles} {P : Party}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)}
    {mkBytes : CryptoVerification.E2E.RecordExtras →
      CryptoGames.LibsignalSession.GhostState (List (BitVec 8)) → List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkAcceptWith X W F (addrValE P) pm coins
      ({ StoresGhost.opened.identity with
         peers := StoresGhost.opened.identity.peers.put (addrValE P).name
           pm.identityKey.serialize }) mkBytes = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkAcceptWith at h
  dsimp only at h
  cases hpk : pkToE? pm with
  | none => rw [hpk] at h; cases h
  | some m =>
    rw [hpk] at h; dsimp only at h
    cases hsk : pkStoreKeys F m with
    | none => rw [hsk] at h; cases h
    | some k =>
      rw [hsk] at h
      cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
      | error _ => rw [hkp] at h; cases h
      | ok kp =>
        rw [hkp] at h
        cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
        | error _ => rw [hreg] at h; cases h
        | ok reg =>
          rw [hreg] at h; dsimp only at h
          cases hrecv : recvPrekeyState X W
              (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
          | none => rw [hrecv] at h; cases h
          | some o =>
            rw [hrecv] at h
            cases o with
            | none => cases h
            | some triple =>
              rcases triple with ⟨x, gs, _⟩
              dsimp only at h
              cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                  pm.signedPreKeyId pm.baseKey with
              | mk kres kyber' =>
                rw [hkm] at h
                cases kres with
                | error _ => cases h
                | ok u =>
                  cases u
                  dsimp only at h
                  injection h with h1
                  injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  have hkyb : kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
                    unfold KyberGhost.mark at hkm
                    cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F
                        (keyName m.kpkId) with
                    | error _ => rw [hot] at hkm; cases hkm
                    | ok bs =>
                      rw [hot] at hkm
                      cases bs with
                      | cons _ _ =>
                        dsimp only at hkm
                        injection hkm with _ hk; subst hk
                        dsimp only
                        have h1 := dirPut_writes_length_le_succ StoresGhost.opened.kyber.oneTime
                          (keyName m.kpkId) []
                        have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                        have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                        omega
                      | nil =>
                        dsimp only at hkm
                        cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F
                            (baseKeysName m.kpkId) with
                        | error _ => rw [hlr] at hkm; cases hkm
                        | ok seen =>
                          rw [hlr] at hkm; dsimp only at hkm
                          split at hkm
                          · cases hkm
                          · split at hkm
                            · cases hkm
                            · injection hkm with _ hk; subst hk
                              dsimp only
                              have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                              have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                              rw [h0a, Nat.zero_add]
                              exact Nat.le_trans (dirPut_writes_length_le_succ _ _ _) (by rw [h0b])
                  have hp_le := dirPut_writes_length_le_succ StoresGhost.opened.identity.peers
                    (addrValE P).name pm.identityKey.serialize
                  have hs_le := dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P)) (mkBytes x gs)
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  unfold StoresGhost.writes
                  dsimp only
                  simp only [List.length_append, h0_own, h0_signed, h0_pub]
                  cases pm.preKeyId with
                  | none =>
                    dsimp only
                    have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                    omega
                  | some j =>
                    dsimp only
                    unfold removePreKey
                    cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                    | error _ =>
                      dsimp only
                      have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                      omega
                    | ok bs =>
                      cases bs with
                      | nil =>
                        dsimp only
                        have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                        omega
                      | cons _ _ =>
                        dsimp only
                        have hot_put := dirPut_writes_length_le_succ StoresGhost.opened.oneTime
                          (keyName j) []
                        have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                        omega

private theorem decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h
    dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h
        dsimp only at h
        have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd F (addrValE P) pm.identityKey =
            { StoresGhost.opened.identity with
              peers := StoresGhost.opened.identity.peers.put (addrValE P).name
                pm.identityKey.serialize } := by
          unfold IdGhost.trusted at htr
          unfold IdGhost.saveUpd
          cases hp : StoresGhost.opened.identity.peer cliIo.rd F (addrValE P) with
          | error _ => rw [hp] at htr; cases htr
          | ok _ => rfl
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h
          dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (CryptoVerification.E2E.pqxdhSpqrSession W)
                  ((CryptoVerification.E2E.pqxdhSessionParams W).expectedAddrs
                    (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1
                  injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (CryptoVerification.E2E.Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]
                  rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err =>
                  cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h
          dsimp only at h
          change decPkAcceptWith X W F (addrValE P) pm coins
            (StoresGhost.opened.identity.saveUpd cliIo.rd F (addrValE P) pm.identityKey)
            (fun x gs => CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs) =
            some (some (g', pt)) at h
          rw [hsave] at h
          exact decPkAcceptWith_writes_len_le_4 h

private theorem decPkDefD2c_writes_bounds {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDefD2c X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    (namedWrites g'.writes).length ≤ 4 ∧
      ∀ q ∈ namedWrites g'.writes, q.1.length ≤ 64 := by
  obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub h
  have hlen4 : g'.writes.length ≤ 4 := by
    cases hload : loadRec Scope F (addrValE P) with
    | error e =>
      rw [decPkDefD2c_of_load_err X W Scope F _ me pm coins hload] at h; cases h
    | ok opt =>
      cases opt with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F _ me pm coins
          (fun _ hl => by rw [hload] at hl; cases hl)] at h
        exact decPkDef_writes_len_le_4 h
      | some r =>
        cases hcur : r.currentSession with
        | none =>
          rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F _ me pm coins
            (fun _ hl => by
              rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)] at h
          exact decPkDef_writes_len_le_4 h
        | some s =>
          by_cases hm : SessMatchesPm s pm
          · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F _ me pm coins hload hcur hm] at h
            exact decPkDef_writes_len_le_4 h
          · by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F
                (addrValE P) pm.identityKey = .ok true
            · rw [decPkDefD2c_of_not_match X W Scope F _ me pm coins hload hcur htr hm] at h
              have hsave : StoresGhost.opened.identity.saveUpd cliIo.rd F (addrValE P)
                  pm.identityKey =
                  { StoresGhost.opened.identity with
                    peers := StoresGhost.opened.identity.peers.put (addrValE P).name
                      pm.identityKey.serialize } := by
                unfold IdGhost.trusted at htr
                unfold IdGhost.saveUpd
                cases hp : StoresGhost.opened.identity.peer cliIo.rd F (addrValE P) with
                | error _ => rw [hp] at htr; cases htr
                | ok _ => rfl
              rw [hsave] at h
              exact decPkAcceptWith_writes_len_le_4 h
            · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F _ me pm coins htr] at h
              exact decPkDef_writes_len_le_4 h
  refine ⟨Nat.le_trans (namedWrites_length_le g'.writes) hlen4, fun q hq => ?_⟩
  rcases hsub q hq with h | h | h | h | h <;> rw [h]
  · exact identityFile_len_le_64 P
  · exact sessionFile_len_le_64 P
  · exact oneTimeKyberPreKeyFile_len_le_64 kpkId
  · exact baseKeysFile_len_le_64 kpkId
  · exact oneTimePreKeyFile_len_le_64 opkId

private theorem finish_some_some_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1
      injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

theorem pqRunAns_namedWrites_bounds {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {i : Inputs} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns (cliRunSemD2c_placed X W) i = some (some (ws, out))) :
    ws.length ≤ 4 ∧ ∀ q ∈ ws, q.1.length ≤ 64 := by
  rcases hi with ⟨st, _, h1 | h2 | h3 | h4 | h5⟩
  · rcases h1 with ⟨_, b, t, rfl⟩
    rw [runAns_pqInit_eq] at ha
    cases hbv : readBundleV (runFiles (pqInitInputs ⟨W.C, W.Q⟩ st b t))
        (bytesOfString CryptoVerification.SignalSession.bundleDir) 1#8 with
    | none => rw [hbv] at ha; cases ha
    | some bv =>
      rw [hbv] at ha
      dsimp only at ha
      obtain ⟨g', v, hg, rfl, _⟩ := finish_some_some_inv ha
      change initDef X ⟨W.C, W.Q⟩ (runFiles (pqInitInputs ⟨W.C, W.Q⟩ st b t))
        (addrValE st.party.other) (addrValE st.party) bv t.toList = some (some (g', v)) at hg
      have hlen := initDef_writes_bounds hg
      have hwr : StoresWrOk (okPeerPath st.party.other) g' := by
        unfold initDef at hg; dsimp only at hg
        split at hg
        · cases hg
        · split at hg
          · cases hg
          · cases hg
          · split at hg
            · split at hg
              · cases hg
              · injection hg with h1; injection h1 with h2
                obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                have h0 := StoresWrOk.opened (okPeerPath st.party.other)
                have hid := okPeerPath_id_local st.party.other
                have hsess := okPeerPath_sess_local st.party.other
                exact { h0 with
                  own := by rw [saveUpd_own]; exact h0.own
                  peers := DirWrOk.saveUpd h0.peers hid
                  sessions := h0.sessions.put hsess _ }
            · cases hg
      exact peer_writes_bounds_of_storesWrOk hlen hwr
  · rcases h2 with ⟨m, r, _, rfl⟩
    rw [runAns_pqSend_eq] at ha
    obtain ⟨g', v, hg, rfl, _⟩ := finish_some_some_inv ha
    change encDef ⟨W.C, W.Q⟩ scopeIn _ _ _ _ _ = some (some (g', v)) at hg
    exact peer_writes_bounds_of_storesWrOk (encDef_writes_bounds hg) (storesWrOk_encDef_local hg)
  · rcases h3 with ⟨ct, rc, _, rfl⟩
    rw [runAns_pqRecvWhisper_eq] at ha
    cases hsm : SignalMessage.tryFrom protoSignalCodec ct with
    | error _ => rw [hsm] at ha; cases ha
    | ok msg =>
      rw [hsm] at ha
      dsimp only at ha
      obtain ⟨g', v, hg, rfl, _⟩ := finish_some_some_inv ha
      change decSigDef ⟨W.C, W.Q⟩ scopeIn _ _ _ _ _ = some (some (g', v)) at hg
      exact peer_writes_bounds_of_storesWrOk (decSigDef_writes_bounds hg) (storesWrOk_decSigDef_local hg)
  · rcases h4 with ⟨m, rc, _, rfl⟩
    rw [runAns_pqRecvPrekey_eq] at ha
    have hpk : (cliRunSemD2c_placed X W).pksmParse = pksmParse := rfl
    have hdp : (cliRunSemD2c_placed X W).decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn := rfl
    rw [hpk, hdp] at ha
    cases hpm : pksmParse m.bytes with
    | none => rw [hpm] at ha; cases ha
    | some pm =>
      rw [hpm] at ha
      dsimp only at ha
      obtain ⟨g', v, hg, rfl, _⟩ := finish_some_some_inv ha
      exact decPkDefD2c_writes_bounds hg
  · rcases h5 with ⟨ct, rc, _, h2, h3, rfl⟩
    rw [runAns_pqRecvBad (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩ st ct rc h2 h3] at ha
    cases ha

/-! ## 6. `M5Env sg` `FineBudgetDom` Dominance by `M5PhaseEnv` (`dir32`, `nm64`) -/

private def dir32 : List (BitVec 8) := List.replicate 32 0#8
private def nm64 : List (BitVec 8) := List.replicate 64 0#8

private def evsModel : List AllocEvent :=
  [.alloc 32, .realloc 1 32 64, .realloc 1 64 128, .free 1 128]

private theorem evsModel_in_m5DirStepEnv :
    M5DirStepEnv dir32 [nm64] evsModel := by
  have hne : dir32 ≠ [] := by decide
  refine Or.inl (Or.inl ?_)
  unfold M5WriteStepEnv
  simp only [hne, ↓reduceIte]
  unfold M5LoopAEntryEnv
  have hd : dir32.length = 32 := by decide
  have hn : nm64.length = 64 := by decide
  have hneed : reserveCap 32 32 1 - (32 + 1) < 64 := by decide
  simp only [hd, hn, hneed]
  have h1 : ([.alloc 32] : List AllocEvent) = rustAllocEvents 32 1 := by decide
  have h2 : ([.realloc 1 32 64] : List AllocEvent) =
      rustReallocEvents 32 (reserveCap 32 32 1) 1 := by decide
  have h3 : ([.realloc 1 64 128] : List AllocEvent) =
      rustReallocEvents (reserveCap 32 32 1)
        (reserveCap (reserveCap 32 32 1) (32 + 1) 64) 1 := by decide
  have h5 : ([.free 1 128] : List AllocEvent) =
      rustDeallocEvents (reserveCap (reserveCap 32 32 1) (32 + 1) 64) 1 := by decide
  change ConcatEnv _ _ ([.alloc 32] ++ [.realloc 1 32 64] ++ [.realloc 1 64 128] ++ [] ++ [.free 1 128])
  exact ConcatEnv.append
    (ConcatEnv.append
      (ConcatEnv.append (ConcatEnv.append h1 h2) h3)
      (Or.inl rfl))
    h5

private theorem fineBudgetDom_refl (b : FineBudget) : FineBudgetDom b b :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

private theorem fineBudgetDom_trans {b₁ b₂ b₃ : FineBudget}
    (h12 : FineBudgetDom b₁ b₂) (h23 : FineBudgetDom b₂ b₃) :
    FineBudgetDom b₁ b₃ :=
  ⟨Nat.le_trans h12.1 h23.1, Nat.le_trans h12.2.1 h23.2.1,
   Nat.le_trans h12.2.2.1 h23.2.2.1, Nat.le_trans h12.2.2.2.1 h23.2.2.2.1,
   Nat.le_trans h12.2.2.2.2.1 h23.2.2.2.2.1, Nat.le_trans h12.2.2.2.2.2 h23.2.2.2.2.2⟩

private theorem fineBudgetDom_stepAligned (align req : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepAligned align req b₁) (FineBudget.stepAligned align req b₂) := by
  rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
  unfold FineBudgetDom FineBudget.stepAligned
  dsimp only
  split
  · unfold finePeak63Bytes finePeak63Count at *; dsimp only
    exact ⟨hSB, hGS, by omega, by omega, by omega, by omega⟩
  · split
    · unfold finePeak63Bytes finePeak63Count at *; dsimp only
      exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩
    · unfold finePeak63Bytes finePeak63Count at *; dsimp only
      exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩

private theorem fineBudgetDom_stepFree (align req : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepFree align req b₁) (FineBudget.stepFree align req b₂) := by
  rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
  unfold FineBudgetDom FineBudget.stepFree
  dsimp only
  split
  · unfold finePeak63Bytes finePeak63Count at *; dsimp only
    exact ⟨hSB, hGS, by omega, by omega, by omega, by omega⟩
  · unfold finePeak63Bytes finePeak63Count at *; dsimp only
    exact ⟨hSB, hGS, by omega, by omega, by omega, by omega⟩

private theorem fineBudgetDom_stepReallocAdd (align newSz : Nat) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (FineBudget.stepReallocAdd align newSz b₁)
      (FineBudget.stepReallocAdd align newSz b₂) := by
  unfold FineBudget.stepReallocAdd
  dsimp only
  split
  · exact fineBudgetDom_stepAligned align newSz h
  · rcases h with ⟨hSB, hGS, hLB, hPB, hLC, hPC⟩
    unfold FineBudgetDom finePeak63Bytes finePeak63Count at *; dsimp only
    exact ⟨by omega, by omega, hLB, by omega, hLC, by omega⟩

private theorem fineBudgetDom_step (ev : AllocEvent) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    FineBudgetDom (fineCostModel.step ev b₁) (fineCostModel.step ev b₂) := by
  change FineBudgetDom (FineBudget.step (toFineEvent ev) b₁) (FineBudget.step (toFineEvent ev) b₂)
  cases ev with
  | alloc req => exact fineBudgetDom_stepAligned 16 req h
  | aligned align req => exact fineBudgetDom_stepAligned align req h
  | free align req => exact fineBudgetDom_stepFree align req h
  | realloc align oldSz newSz =>
    exact fineBudgetDom_stepFree align oldSz (fineBudgetDom_stepReallocAdd align newSz h)

private theorem fineBudgetDom_stepEvents :
    ∀ (evs : List AllocEvent) {b₁ b₂ : FineBudget},
      FineBudgetDom b₁ b₂ →
      FineBudgetDom (fineCostModel.stepEvents evs b₁) (fineCostModel.stepEvents evs b₂)
  | [], _, _, h => h
  | ev :: evs, _, _, h => fineBudgetDom_stepEvents evs (fineBudgetDom_step ev h)

private theorem fineMaxGroups_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxGroups b₁ ≤ fineMaxGroups b₂ := by
  rcases h with ⟨_, hGS, _, _, _, hPC⟩
  unfold fineMaxGroups
  have hDiv :
      (b₁.cumSmallGroupsS + FineScale - 1) / FineScale ≤
        (b₂.cumSmallGroupsS + FineScale - 1) / FineScale :=
    Nat.div_le_div_right (by omega)
  omega

private theorem fineMaxMetaAreas_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxMetaAreas b₁ ≤ fineMaxMetaAreas b₂ := by
  have hG := fineMaxGroups_mono_dom h
  unfold fineMaxMetaAreas
  have hDiv := Nat.div_le_div_right (c := 101) (a := 7 + fineMaxGroups b₁)
    (b := 7 + fineMaxGroups b₂) (by omega)
  omega

private theorem fineMaxDynIvs_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineMaxDynIvs b₁ ≤ fineMaxDynIvs b₂ := by
  have hG := fineMaxGroups_mono_dom h
  have hM := fineMaxMetaAreas_mono_dom h
  unfold fineMaxDynIvs
  omega

private theorem fineFootprint_mono_dom {b₁ b₂ : FineBudget} (h : FineBudgetDom b₁ b₂) :
    fineFootprint b₁ ≤ fineFootprint b₂ := by
  have hM := fineMaxMetaAreas_mono_dom h
  rcases h with ⟨hSB, _, _, hPB, _, _⟩
  unfold fineFootprint
  omega

private theorem fineStepReserve_mono_dom (ev : AllocEvent) {b₁ b₂ : FineBudget}
    (h : FineBudgetDom b₁ b₂) :
    fineCostModel.stepReserve ev b₁ ≤ fineCostModel.stepReserve ev b₂ := by
  have hM := fineMaxMetaAreas_mono_dom h
  change fineStepReserve (toFineEvent ev) b₁ ≤ fineStepReserve (toFineEvent ev) b₂
  cases ev <;> exact FineStepBound_mono_meta hM

private theorem fitsEvents_of_fineBudgetDom {lim : BudgetLimits} :
    ∀ (evs : List AllocEvent) {b₁ b₂ : FineBudget},
      FineBudgetDom b₁ b₂ →
      FitsEvents fineCostModel lim b₂ evs →
      FitsEvents fineCostModel lim b₁ evs
  | [], _, _, _, _ => trivial
  | ev :: evs, _, _, hdom, ⟨⟨hw, hstep⟩, hrest⟩ =>
    ⟨⟨hw, hstep.mono (fineStepReserve_mono_dom ev hdom)
      (fineMaxDynIvs_mono_dom hdom) (fineFootprint_mono_dom hdom)⟩,
     fitsEvents_of_fineBudgetDom evs (fineBudgetDom_step ev hdom) hrest⟩

private theorem fitsEnv_of_fineBudgetDom {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {b₁ b₂ : FineBudget} (hdom : FineBudgetDom b₁ b₂)
    (h : FitsEnv fineCostModel lim b₂ Env) :
    FitsEnv fineCostModel lim b₁ Env :=
  fun evs hevs => fitsEvents_of_fineBudgetDom evs hdom (h evs hevs)

private theorem writeFileEnv_eq_nil_of_le_64 {len : Nat} (hlen : len ≤ 64)
    {evs : List AllocEvent} (h : WriteFileEnv len evs) :
    evs = [] := by
  rcases h with rfl | ⟨hle, _⟩
  · rfl
  · omega

private def checkPageAlignLe128 : Bool :=
  (List.range 129).all fun req => decide (pageAlignUp (req + 0 + 8192) ≤ 12288)

private theorem checkPageAlignLe128_true : checkPageAlignLe128 = true := by decide

private theorem fineStepBound_le_alloc32_of_le_128 {req align : Nat}
    (hreq : req ≤ 128) (hal : align ≤ 16) (m : Nat) :
    FineStepBound req align m ≤ FineStepBound 32 16 m := by
  unfold FineStepBound
  have hpad : max align 16 - 16 = 0 := by omega
  rw [hpad]
  have hp32 : pageAlignUp (32 + (max 16 16 - 16) + 8192) = 12288 := by decide
  rw [hp32]
  have hp_le : pageAlignUp (req + 0 + 8192) ≤ 12288 :=
    of_decide_eq_true (List.all_eq_true.mp checkPageAlignLe128_true req
      (List.mem_range.mpr (by omega)))
  omega

private theorem fitsEvent_small_of_dom_alloc32 {lim : BudgetLimits}
    {ev ev₂ : AllocEvent} {b₁ b₂ : FineBudget}
    (hwf : ev.withinMaxAlloc)
    (hdom : FineBudgetDom b₁ b₂)
    (hres : fineCostModel.stepReserve ev b₁ ≤ fineCostModel.stepReserve ev₂ b₂)
    (h₂ : FitsEvent fineCostModel lim b₂ ev₂) :
    FitsEvent fineCostModel lim b₁ ev :=
  ⟨hwf, h₂.2.mono hres (fineMaxDynIvs_mono_dom hdom) (fineFootprint_mono_dom hdom)⟩

private theorem stepReserve_small_le_model_ev {ev ev₂ : AllocEvent} {b₁ b₂ : FineBudget}
    (hdom : FineBudgetDom b₁ b₂)
    (hev : (∃ r, r ≤ 128 ∧ ev = .alloc r) ∨
           (∃ old r, r ≤ 128 ∧ ev = .realloc 1 old r) ∨
           (∃ sz, ev = .free 1 sz))
    (hev₂ : ev₂ = .alloc 32 ∨ ev₂ = .realloc 1 32 64 ∨ ev₂ = .realloc 1 64 128) :
    fineCostModel.stepReserve ev b₁ ≤ fineCostModel.stepReserve ev₂ b₂ := by
  have hM := fineMaxMetaAreas_mono_dom hdom
  have hlhs : fineCostModel.stepReserve ev b₁ ≤ FineStepBound 32 16 (fineMaxMetaAreas b₁) := by
    change fineStepReserve (toFineEvent ev) b₁ ≤ FineStepBound 32 16 (fineMaxMetaAreas b₁)
    rcases hev with ⟨r, hr, rfl⟩ | ⟨old, r, hr, rfl⟩ | ⟨sz, rfl⟩
    · exact fineStepBound_le_alloc32_of_le_128 hr (Nat.le_refl 16) _
    · exact fineStepBound_le_alloc32_of_le_128 hr (by decide) _
    · exact fineStepBound_le_alloc32_of_le_128 (Nat.zero_le _) (Nat.le_refl 16) _
  have hrhs : FineStepBound 32 16 (fineMaxMetaAreas b₂) = fineCostModel.stepReserve ev₂ b₂ := by
    have h1 : pageAlignUp (32 + (max 16 16 - 16) + 8192) = 12288 := by decide
    have h2 : pageAlignUp (64 + (max 1 16 - 16) + 8192) = 12288 := by decide
    have h3 : pageAlignUp (128 + (max 1 16 - 16) + 8192) = 12288 := by decide
    rcases hev₂ with rfl | rfl | rfl
    · rfl
    · change FineStepBound 32 16 (fineMaxMetaAreas b₂) = FineStepBound 64 1 (fineMaxMetaAreas b₂)
      unfold FineStepBound
      rw [h1, h2]
    · change FineStepBound 32 16 (fineMaxMetaAreas b₂) = FineStepBound 128 1 (fineMaxMetaAreas b₂)
      unfold FineStepBound
      rw [h1, h3]
  exact Nat.le_trans hlhs (hrhs ▸ FineStepBound_mono_meta hM)

private def IsSmallEv (e : AllocEvent) : Prop :=
  (∃ r, r ≤ 128 ∧ e = .alloc r) ∨
  (∃ old r, old ≤ 128 ∧ r ≤ 128 ∧ e = .realloc 1 old r) ∨
  (∃ sz, sz ≤ 128 ∧ e = .free 1 sz)

private def SmallStepEq (y x d : FineBudget) : Prop :=
  y.cumSmallBytes = x.cumSmallBytes + d.cumSmallBytes ∧
  y.cumSmallGroupsS = x.cumSmallGroupsS + d.cumSmallGroupsS ∧
  y.live63Bytes = x.live63Bytes ∧
  finePeak63Bytes y = finePeak63Bytes x ∧
  y.live63Count = x.live63Count ∧
  finePeak63Count y = finePeak63Count x

private theorem step_small_fields {e : AllocEvent} (he : IsSmallEv e) (x : FineBudget) :
    SmallStepEq (fineCostModel.step e x) x (fineCostModel.step e fineCostModel.init) := by
  have hinit : fineCostModel.init = FineBudget.init := rfl
  rw [hinit]
  rcases he with ⟨r, hr, rfl⟩ | ⟨old, r, hold, hr, rfl⟩ | ⟨sz, hsz, rfl⟩
  · have hg : ¬ Guaranteed63Threshold ≤ r := by
      have : Guaranteed63Threshold = 135168 := by decide
      omega
    have hm : r + (max 16 16 - 16) ≤ MmapThresholdReq := by
      have : MmapThresholdReq = 131051 := by decide
      omega
    change SmallStepEq (FineBudget.step (toFineEvent (.alloc r)) x) x
      (FineBudget.step (toFineEvent (.alloc r)) FineBudget.init)
    unfold SmallStepEq toFineEvent FineBudget.step FineBudget.stepAlloc
      FineBudget.stepAligned FineBudget.init finePeak63Bytes finePeak63Count
    dsimp only
    simp only [hg, hm, ↓reduceIte]
    exact ⟨by omega, by omega, trivial, by omega, trivial, by omega⟩
  · have hg1 : ¬ Guaranteed63Threshold ≤ r := by
      have : Guaranteed63Threshold = 135168 := by decide
      omega
    have hm : r ≤ MmapThresholdReq := by
      have : MmapThresholdReq = 131051 := by decide
      omega
    have hg2 : ¬ Guaranteed63Threshold ≤ old := by
      have : Guaranteed63Threshold = 135168 := by decide
      omega
    change SmallStepEq (FineBudget.step (toFineEvent (.realloc 1 old r)) x) x
      (FineBudget.step (toFineEvent (.realloc 1 old r)) FineBudget.init)
    unfold SmallStepEq toFineEvent FineBudget.step FineBudget.stepRealloc
      FineBudget.stepReallocAdd FineBudget.stepFree FineBudget.init
      finePeak63Bytes finePeak63Count
    dsimp only
    simp only [hg1, hm, hg2, ↓reduceIte]
    exact ⟨by omega, by omega, trivial, by omega, trivial, by omega⟩
  · have hg : ¬ Guaranteed63Threshold ≤ sz := by
      have : Guaranteed63Threshold = 135168 := by decide
      omega
    change SmallStepEq (FineBudget.step (toFineEvent (.free 1 sz)) x) x
      (FineBudget.step (toFineEvent (.free 1 sz)) FineBudget.init)
    unfold SmallStepEq toFineEvent FineBudget.step FineBudget.stepFree
      FineBudget.init finePeak63Bytes finePeak63Count
    dsimp only
    simp only [hg, ↓reduceIte]
    exact ⟨by omega, by omega, trivial, by omega, trivial, by omega⟩

private theorem stepEvents_small_fields :
    ∀ (evs : List AllocEvent), (∀ e ∈ evs, IsSmallEv e) → ∀ (b : FineBudget),
      SmallStepEq (fineCostModel.stepEvents evs b) b
        (fineCostModel.stepEvents evs fineCostModel.init)
  | [], _, b => by
    have hinit : fineCostModel.init = FineBudget.init := rfl
    change SmallStepEq b b fineCostModel.init
    rw [hinit]
    unfold SmallStepEq FineBudget.init
    dsimp only
    exact ⟨by omega, by omega, rfl, rfl, rfl, rfl⟩
  | e :: es, hsmall, b => by
    have he : IsSmallEv e := hsmall e List.mem_cons_self
    have hes : ∀ e' ∈ es, IsSmallEv e' := fun e' hm => hsmall e' (List.mem_cons_of_mem e hm)
    obtain ⟨h1SB, h1GS, h1LB, h1PB, h1LC, h1PC⟩ := step_small_fields he b
    obtain ⟨h2SB, h2GS, h2LB, h2PB, h2LC, h2PC⟩ :=
      stepEvents_small_fields es hes (fineCostModel.step e b)
    obtain ⟨hi2SB, hi2GS, _, _, _, _⟩ :=
      stepEvents_small_fields es hes (fineCostModel.step e fineCostModel.init)
    change SmallStepEq (fineCostModel.stepEvents es (fineCostModel.step e b)) b
      (fineCostModel.stepEvents es (fineCostModel.step e fineCostModel.init))
    exact ⟨by omega, by omega, h2LB.trans h1LB, h2PB.trans h1PB,
      h2LC.trans h1LC, h2PC.trans h1PC⟩

private theorem dom_of_init_le {evs₁ evs₂ : List AllocEvent}
    (hs₁ : ∀ e ∈ evs₁, IsSmallEv e)
    (hs₂ : ∀ e ∈ evs₂, IsSmallEv e)
    (hSB : (fineCostModel.stepEvents evs₁ fineCostModel.init).cumSmallBytes ≤
           (fineCostModel.stepEvents evs₂ fineCostModel.init).cumSmallBytes)
    (hGS : (fineCostModel.stepEvents evs₁ fineCostModel.init).cumSmallGroupsS ≤
           (fineCostModel.stepEvents evs₂ fineCostModel.init).cumSmallGroupsS)
    (b : FineBudget) :
    FineBudgetDom (fineCostModel.stepEvents evs₁ b) (fineCostModel.stepEvents evs₂ b) := by
  obtain ⟨h1SB, h1GS, h1LB, h1PB, h1LC, h1PC⟩ := stepEvents_small_fields evs₁ hs₁ b
  obtain ⟨h2SB, h2GS, h2LB, h2PB, h2LC, h2PC⟩ := stepEvents_small_fields evs₂ hs₂ b
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem fineBudgetDom_free_small_self {sz : Nat} (hsz : sz ≤ 128) (x : FineBudget) :
    FineBudgetDom (fineCostModel.step (.free 1 sz) x) x ∧
      FineBudgetDom x (fineCostModel.step (.free 1 sz) x) := by
  have hg : ¬ Guaranteed63Threshold ≤ sz := by
    have : Guaranteed63Threshold = 135168 := by decide
    omega
  change FineBudgetDom (FineBudget.step (toFineEvent (.free 1 sz)) x) x ∧
    FineBudgetDom x (FineBudget.step (toFineEvent (.free 1 sz)) x)
  unfold FineBudgetDom toFineEvent FineBudget.step FineBudget.stepFree
    finePeak63Bytes finePeak63Count
  dsimp only
  simp only [hg, ↓reduceIte]
  exact ⟨⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by omega, Nat.le_refl _, by omega⟩,
         ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by omega, Nat.le_refl _, by omega⟩⟩

private def m5LoopAFinalCapNat (L N : Nat) : Nat :=
  let c1 := reserveCap L L 1
  if c1 - (L + 1) < N then reserveCap c1 (L + 1) N else c1

private def m5LoopAFullTrace (L N : Nat) : List AllocEvent :=
  let c1 := reserveCap L L 1
  (rustAllocEvents L 1 ++ rustReallocEvents L c1 1 ++
    (if c1 - (L + 1) < N then rustReallocEvents c1 (reserveCap c1 (L + 1) N) 1 else [])) ++
    rustDeallocEvents (m5LoopAFinalCapNat L N) 1

private def checkLoopB (k : Nat) : Bool :=
  let d1 := fineCostModel.stepEvents [.alloc k] fineCostModel.init
  let dm2 := fineCostModel.stepEvents [.alloc 32, .realloc 1 32 64] fineCostModel.init
  decide (d1.cumSmallBytes ≤ dm2.cumSmallBytes ∧ d1.cumSmallGroupsS ≤ dm2.cumSmallGroupsS)

private theorem checkLoopB_true : ∀ k ∈ List.range 65, checkLoopB k = true := by decide

private def checkLoopA (L N : Nat) : Bool :=
  let c1 := reserveCap L L 1
  let c2 := reserveCap c1 (L + 1) N
  let t1 := rustAllocEvents L 1
  let t2 := t1 ++ rustReallocEvents L c1 1
  let t3 := m5LoopAFullTrace L N
  let d1 := fineCostModel.stepEvents t1 fineCostModel.init
  let d2 := fineCostModel.stepEvents t2 fineCostModel.init
  let d3 := fineCostModel.stepEvents t3 fineCostModel.init
  let m1 := fineCostModel.stepEvents [.alloc 32] fineCostModel.init
  let m2 := fineCostModel.stepEvents [.alloc 32, .realloc 1 32 64] fineCostModel.init
  let m3 := fineCostModel.stepEvents evsModel fineCostModel.init
  if L ≤ 32 then
    decide (1 ≤ c1 ∧ c1 ≤ 64 ∧ 1 ≤ c2 ∧ c2 ≤ 128 ∧
      d1.cumSmallBytes ≤ m1.cumSmallBytes ∧ d1.cumSmallGroupsS ≤ m1.cumSmallGroupsS ∧
      d2.cumSmallBytes ≤ m2.cumSmallBytes ∧ d2.cumSmallGroupsS ≤ m2.cumSmallGroupsS ∧
      d3.cumSmallBytes ≤ m3.cumSmallBytes ∧ d3.cumSmallGroupsS ≤ m3.cumSmallGroupsS)
  else
    decide (¬ (c1 - (L + 1) < N) ∧ 1 ≤ c1 ∧ c1 ≤ 128 ∧
      d1.cumSmallBytes ≤ m2.cumSmallBytes ∧ d1.cumSmallGroupsS ≤ m2.cumSmallGroupsS ∧
      d2.cumSmallBytes ≤ m3.cumSmallBytes ∧ d2.cumSmallGroupsS ≤ m3.cumSmallGroupsS ∧
      d3.cumSmallBytes ≤ m3.cumSmallBytes ∧ d3.cumSmallGroupsS ≤ m3.cumSmallGroupsS)

private theorem checkLoopA_true :
    ∀ L ∈ List.range 65, ∀ N ∈ List.range 65,
      1 ≤ L → L + 1 + N ≤ 64 → checkLoopA L N = true := by decide

private theorem wf_alloc {r : Nat} (hr : r ≤ 128) : (AllocEvent.alloc r).withinMaxAlloc :=
  Nat.le_trans hr (by decide)

private theorem wf_realloc1 {old r : Nat} (hr : r ≤ 128) :
    (AllocEvent.realloc 1 old r).withinMaxAlloc :=
  Nat.le_trans hr (by decide)

private theorem wf_free1 (sz : Nat) : (AllocEvent.free 1 sz).withinMaxAlloc := trivial

private theorem rustAlloc1_eq (n : Nat) (hn : 1 ≤ n) :
    rustAllocEvents n 1 = [.alloc n] := by
  unfold rustAllocEvents
  have h1 : (1 : Nat) ≤ 16 := by decide
  simp only [h1, hn, and_self, ↓reduceIte]

private theorem rustRealloc1_eq (old new : Nat) (hnew : 1 ≤ new) :
    rustReallocEvents old new 1 = [.realloc 1 old new] := by
  unfold rustReallocEvents
  have h1 : (1 : Nat) ≤ 16 := by decide
  simp only [h1, hnew, and_self, ↓reduceIte]

private theorem evsModel_small : ∀ e ∈ evsModel, IsSmallEv e := by
  intro e he
  simp only [evsModel, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨32, by decide, rfl⟩
  · exact Or.inr (Or.inl ⟨32, 64, by decide, by decide, rfl⟩)
  · exact Or.inr (Or.inl ⟨64, 128, by decide, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨128, by decide, rfl⟩)

private theorem dom_nil_evsModel (b : FineBudget) :
    FineBudgetDom b (fineCostModel.stepEvents evsModel b) := by
  have h0 : b = fineCostModel.stepEvents [] b := rfl
  rw [h0]
  exact dom_of_init_le (evs₁ := []) (fun _ hm => nomatch hm) evsModel_small (by decide) (by decide) b

private theorem m5LoopBStep_dom_model {lim : BudgetLimits} {nm : List (BitVec 8)}
    (hnm : nm.length ≤ 64) {evs : List AllocEvent} (h : M5LoopBStepEnv nm evs)
    (b : FineBudget) (hM : FitsEvents fineCostModel lim b evsModel) :
    FitsEvents fineCostModel lim b evs ∧
      FineBudgetDom (fineCostModel.stepEvents evs b) (fineCostModel.stepEvents evsModel b) := by
  unfold M5LoopBStepEnv at h
  by_cases hnil : nm = []
  · simp only [hnil, ↓reduceIte] at h
    have heq := writeFileEnv_eq_nil_of_le_64 (Nat.zero_le _) h
    subst heq
    exact ⟨trivial, dom_nil_evsModel b⟩
  · simp only [hnil, ↓reduceIte] at h
    obtain ⟨evsE, evsD, rfl, herr, hd⟩ := h
    obtain ⟨evsA, evsW, rfl, rfl, hw⟩ := herr
    have hweq := writeFileEnv_eq_nil_of_le_64 hnm hw
    subst hweq
    rw [hd, List.append_nil]
    have hpos : 1 ≤ nm.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr hnil)
    have halloc_eq : rustAllocEvents nm.length 1 = [.alloc nm.length] :=
      rustAlloc1_eq nm.length hpos
    have hdealloc_eq : rustDeallocEvents nm.length 1 = [.free 1 nm.length] := rfl
    rw [halloc_eq, hdealloc_eq]
    change FitsEvents fineCostModel lim b [.alloc nm.length, .free 1 nm.length] ∧ _
    have hchk := checkLoopB_true nm.length (List.mem_range.mpr (by omega))
    unfold checkLoopB at hchk
    obtain ⟨hSB, hGS⟩ := of_decide_eq_true hchk
    obtain ⟨hm0, hm1, hm2, _⟩ := hM
    have hs1 : ∀ e ∈ ([.alloc nm.length] : List AllocEvent), IsSmallEv e := by
      intro e he; rw [List.mem_singleton] at he; subst he
      exact Or.inl ⟨nm.length, by omega, rfl⟩
    have hsm2 : ∀ e ∈ ([.alloc 32, .realloc 1 32 64] : List AllocEvent), IsSmallEv e := by
      intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Or.inl ⟨32, by decide, rfl⟩
      · exact Or.inr (Or.inl ⟨32, 64, by decide, by decide, rfl⟩)
    have hdom1 := dom_of_init_le hs1 hsm2 hSB hGS b
    have hf0 : FitsEvent fineCostModel lim b (.alloc nm.length) :=
      fitsEvent_small_of_dom_alloc32 (wf_alloc (by omega)) (fineBudgetDom_refl b)
        (stepReserve_small_le_model_ev (fineBudgetDom_refl b)
          (Or.inl ⟨nm.length, by omega, rfl⟩) (Or.inl rfl))
        hm0
    have hf1 : FitsEvent fineCostModel lim (fineCostModel.step (.alloc nm.length) b)
        (.free 1 nm.length) :=
      fitsEvent_small_of_dom_alloc32 (wf_free1 _) hdom1
        (stepReserve_small_le_model_ev hdom1
          (Or.inr (Or.inr ⟨nm.length, rfl⟩)) (Or.inr (Or.inr rfl)))
        hm2
    have hdom_end :
        FineBudgetDom
          (fineCostModel.stepEvents [.alloc nm.length, .free 1 nm.length] b)
          (fineCostModel.stepEvents evsModel b) := by
      change FineBudgetDom
        (fineCostModel.step (.free 1 nm.length) (fineCostModel.step (.alloc nm.length) b))
        (fineCostModel.stepEvents evsModel b)
      have hdom23 :
          FineBudgetDom
            (fineCostModel.stepEvents [.alloc 32, .realloc 1 32 64] b)
            (fineCostModel.stepEvents evsModel b) :=
        dom_of_init_le hsm2 evsModel_small (by decide) (by decide) b
      exact fineBudgetDom_trans
        (fineBudgetDom_free_small_self (by omega) _).1
        (fineBudgetDom_trans hdom1 hdom23)
    exact ⟨⟨hf0, hf1, trivial⟩, hdom_end⟩

private theorem m5LoopAStep_dom_model {lim : BudgetLimits} {dir nm : List (BitVec 8)}
    (hdir : dir ≠ []) (hp : (pathOf dir nm).length ≤ 64)
    {evs : List AllocEvent} (h : M5LoopAStepEnv dir nm evs)
    (b : FineBudget) (hM : FitsEvents fineCostModel lim b evsModel) :
    FitsEvents fineCostModel lim b evs ∧
      FineBudgetDom (fineCostModel.stepEvents evs b) (fineCostModel.stepEvents evsModel b) := by
  have hplen : (pathOf dir nm).length = dir.length + 1 + nm.length := by
    unfold pathOf
    simp only [hdir, ↓reduceIte, List.length_append]
    have hu : (utf8 "/").length = 1 := by
      simp [utf8, byteArray_toList_eq_data_local]
      decide
    omega
  have hLN : dir.length + 1 + nm.length ≤ 64 := hplen ▸ hp
  have hLpos : 1 ≤ dir.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr hdir)
  obtain ⟨evsErr, evsFree, rfl, ⟨evsBuild, evsWr, rfl, hbuild, hwr⟩, hfree⟩ := h
  have hwr_nil := writeFileEnv_eq_nil_of_le_64 hp hwr
  subst hwr_nil
  rw [hbuild, List.append_nil, hfree]
  have htrace_eq :
      m5LoopABuildPathEvents dir nm ++ rustDeallocEvents (m5LoopAPathCap dir nm) 1 =
        m5LoopAFullTrace dir.length nm.length := rfl
  rw [htrace_eq]
  set L := dir.length
  set N := nm.length
  have hchk := checkLoopA_true L (List.mem_range.mpr (by omega))
    N (List.mem_range.mpr (by omega)) hLpos hLN
  unfold checkLoopA at hchk
  obtain ⟨hm0, hm1, hm2, hm3, _⟩ := hM
  set c1 := reserveCap L L 1
  set c2 := reserveCap c1 (L + 1) N
  have hc1_def : reserveCap L L 1 = c1 := rfl
  have hc2_def : reserveCap c1 (L + 1) N = c2 := rfl
  have hsm1 : ∀ e ∈ ([.alloc 32] : List AllocEvent), IsSmallEv e := by
    intro e he; rw [List.mem_singleton] at he; subst he
    exact Or.inl ⟨32, by decide, rfl⟩
  have hsm2 : ∀ e ∈ ([.alloc 32, .realloc 1 32 64] : List AllocEvent), IsSmallEv e := by
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inl ⟨32, by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨32, 64, by decide, by decide, rfl⟩)
  by_cases hL32 : L ≤ 32
  · simp only [hL32, ↓reduceIte] at hchk
    obtain ⟨hc1_pos, hc1_le, hc2_pos, hc2_le, hSB1, hGS1, hSB2, hGS2, hSB3, hGS3⟩ :=
      of_decide_eq_true hchk
    have ht1_eq : rustAllocEvents L 1 = [.alloc L] := rustAlloc1_eq L hLpos
    have ht2_eq : rustReallocEvents L c1 1 = [.realloc 1 L c1] := rustRealloc1_eq L c1 hc1_pos
    have hs_t1 : ∀ e ∈ rustAllocEvents L 1, IsSmallEv e := by
      rw [ht1_eq]; intro e he; rw [List.mem_singleton] at he; subst he
      exact Or.inl ⟨L, by omega, rfl⟩
    have hs_t2 : ∀ e ∈ rustAllocEvents L 1 ++ rustReallocEvents L c1 1, IsSmallEv e := by
      rw [ht1_eq, ht2_eq]; intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Or.inl ⟨L, by omega, rfl⟩
      · exact Or.inr (Or.inl ⟨L, c1, by omega, by omega, rfl⟩)
    have hdom1 := dom_of_init_le hs_t1 hsm1 hSB1 hGS1 b
    have hdom2 := dom_of_init_le hs_t2 hsm2 hSB2 hGS2 b
    have hf0 : FitsEvent fineCostModel lim b (.alloc L) :=
      fitsEvent_small_of_dom_alloc32 (wf_alloc (by omega)) (fineBudgetDom_refl b)
        (stepReserve_small_le_model_ev (fineBudgetDom_refl b)
          (Or.inl ⟨L, by omega, rfl⟩) (Or.inl rfl))
        hm0
    have hf1 : FitsEvent fineCostModel lim (fineCostModel.step (.alloc L) b) (.realloc 1 L c1) := by
      have hd1 : FineBudgetDom (fineCostModel.step (.alloc L) b) (fineCostModel.step (.alloc 32) b) := by
        rw [ht1_eq] at hdom1
        exact hdom1
      exact fitsEvent_small_of_dom_alloc32 (wf_realloc1 (by omega)) hd1
        (stepReserve_small_le_model_ev hd1
          (Or.inr (Or.inl ⟨L, c1, by omega, rfl⟩)) (Or.inr (Or.inl rfl)))
        hm1
    by_cases hlt : c1 - (L + 1) < N
    · have ht3_eq : rustReallocEvents c1 c2 1 = [.realloc 1 c1 c2] := rustRealloc1_eq c1 c2 hc2_pos
      have heq_full : m5LoopAFullTrace L N =
          [.alloc L, .realloc 1 L c1, .realloc 1 c1 c2, .free 1 c2] := by
        unfold m5LoopAFullTrace m5LoopAFinalCapNat rustDeallocEvents
        dsimp only
        rw [hc1_def, hc2_def]
        simp only [hlt, ↓reduceIte, ht1_eq, ht2_eq, ht3_eq]
        rfl
      have hs_full : ∀ e ∈ m5LoopAFullTrace L N, IsSmallEv e := by
        rw [heq_full]
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨L, by omega, rfl⟩
        · exact Or.inr (Or.inl ⟨L, c1, by omega, by omega, rfl⟩)
        · exact Or.inr (Or.inl ⟨c1, c2, by omega, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨c2, by omega, rfl⟩)
      have hdom_end := dom_of_init_le hs_full evsModel_small hSB3 hGS3 b
      have hd2 : FineBudgetDom
          (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
          (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b)) := by
        rw [ht1_eq, ht2_eq] at hdom2
        exact hdom2
      have hf2 : FitsEvent fineCostModel lim
          (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
          (.realloc 1 c1 c2) :=
        fitsEvent_small_of_dom_alloc32 (wf_realloc1 hc2_le) hd2
          (stepReserve_small_le_model_ev hd2
            (Or.inr (Or.inl ⟨c1, c2, by omega, rfl⟩)) (Or.inr (Or.inr rfl)))
          hm2
      have hd3 : FineBudgetDom
          (fineCostModel.step (.realloc 1 c1 c2)
            (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b)))
          (fineCostModel.step (.realloc 1 64 128)
            (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b))) := by
        have hde :
            FineBudgetDom
              (fineCostModel.step (.free 1 c2)
                (fineCostModel.step (.realloc 1 c1 c2)
                  (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))))
              (fineCostModel.step (.free 1 128)
                (fineCostModel.step (.realloc 1 64 128)
                  (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b)))) := by
          have h := hdom_end
          rw [heq_full] at h
          exact h
        exact fineBudgetDom_trans (fineBudgetDom_free_small_self hc2_le _).2
          (fineBudgetDom_trans hde (fineBudgetDom_free_small_self (by decide) _).1)
      have hf3 : FitsEvent fineCostModel lim
          (fineCostModel.step (.realloc 1 c1 c2)
            (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b)))
          (.free 1 c2) :=
        fitsEvent_small_of_dom_alloc32 (ev₂ := .free 1 128) (wf_free1 _) hd3
          (FineStepBound_mono_meta (req := 0) (align := 16) (fineMaxMetaAreas_mono_dom hd3)) hm3
      rw [heq_full] at hdom_end ⊢
      exact ⟨⟨hf0, hf1, hf2, hf3, trivial⟩, hdom_end⟩
    · have heq_full : m5LoopAFullTrace L N = [.alloc L, .realloc 1 L c1, .free 1 c1] := by
        unfold m5LoopAFullTrace m5LoopAFinalCapNat rustDeallocEvents
        dsimp only
        rw [hc1_def]
        simp only [hlt, ↓reduceIte, ht1_eq, ht2_eq]
        rfl
      have hs_full : ∀ e ∈ m5LoopAFullTrace L N, IsSmallEv e := by
        rw [heq_full]
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact Or.inl ⟨L, by omega, rfl⟩
        · exact Or.inr (Or.inl ⟨L, c1, by omega, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨c1, by omega, rfl⟩)
      have hdom_end := dom_of_init_le hs_full evsModel_small hSB3 hGS3 b
      have hd2 : FineBudgetDom
          (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
          (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b)) := by
        rw [ht1_eq, ht2_eq] at hdom2
        exact hdom2
      have hf2 : FitsEvent fineCostModel lim
          (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
          (.free 1 c1) :=
        fitsEvent_small_of_dom_alloc32 (wf_free1 _) hd2
          (stepReserve_small_le_model_ev hd2
            (Or.inr (Or.inr ⟨c1, rfl⟩)) (Or.inr (Or.inr rfl)))
          hm2
      rw [heq_full] at hdom_end ⊢
      exact ⟨⟨hf0, hf1, hf2, trivial⟩, hdom_end⟩
  · simp only [hL32, ↓reduceIte] at hchk
    obtain ⟨hnlt, hc1_pos, hc1_le, hSB1, hGS1, hSB2, hGS2, hSB3, hGS3⟩ :=
      of_decide_eq_true hchk
    have ht1_eq : rustAllocEvents L 1 = [.alloc L] := rustAlloc1_eq L hLpos
    have ht2_eq : rustReallocEvents L c1 1 = [.realloc 1 L c1] := rustRealloc1_eq L c1 hc1_pos
    have heq_full : m5LoopAFullTrace L N = [.alloc L, .realloc 1 L c1, .free 1 c1] := by
      unfold m5LoopAFullTrace m5LoopAFinalCapNat rustDeallocEvents
      dsimp only
      rw [hc1_def]
      simp only [hnlt, ↓reduceIte, ht1_eq, ht2_eq]
      rfl
    have hs_t1 : ∀ e ∈ rustAllocEvents L 1, IsSmallEv e := by
      rw [ht1_eq]; intro e he; rw [List.mem_singleton] at he; subst he
      exact Or.inl ⟨L, by omega, rfl⟩
    have hs_full : ∀ e ∈ m5LoopAFullTrace L N, IsSmallEv e := by
      rw [heq_full]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl ⟨L, by omega, rfl⟩
      · exact Or.inr (Or.inl ⟨L, c1, by omega, by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨c1, by omega, rfl⟩)
    have hdom1 := dom_of_init_le hs_t1 hsm2 hSB1 hGS1 b
    have hdom_end := dom_of_init_le hs_full evsModel_small hSB3 hGS3 b
    have hf0 : FitsEvent fineCostModel lim b (.alloc L) :=
      fitsEvent_small_of_dom_alloc32 (wf_alloc (by omega)) (fineBudgetDom_refl b)
        (stepReserve_small_le_model_ev (fineBudgetDom_refl b)
          (Or.inl ⟨L, by omega, rfl⟩) (Or.inl rfl))
        hm0
    have hd1 : FineBudgetDom (fineCostModel.step (.alloc L) b)
        (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b)) := by
      rw [ht1_eq] at hdom1
      exact hdom1
    have hf1 : FitsEvent fineCostModel lim (fineCostModel.step (.alloc L) b) (.realloc 1 L c1) :=
      fitsEvent_small_of_dom_alloc32 (wf_realloc1 hc1_le) hd1
        (stepReserve_small_le_model_ev hd1
          (Or.inr (Or.inl ⟨L, c1, by omega, rfl⟩)) (Or.inr (Or.inr rfl)))
        hm2
    have hd2 : FineBudgetDom
        (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
        (fineCostModel.step (.realloc 1 64 128)
          (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b))) := by
      have hde :
          FineBudgetDom
            (fineCostModel.step (.free 1 c1)
              (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b)))
            (fineCostModel.step (.free 1 128)
              (fineCostModel.step (.realloc 1 64 128)
                (fineCostModel.step (.realloc 1 32 64) (fineCostModel.step (.alloc 32) b)))) := by
        have h := hdom_end
        rw [heq_full] at h
        exact h
      exact fineBudgetDom_trans (fineBudgetDom_free_small_self hc1_le _).2
        (fineBudgetDom_trans hde (fineBudgetDom_free_small_self (by decide) _).1)
    have hf2 : FitsEvent fineCostModel lim
        (fineCostModel.step (.realloc 1 L c1) (fineCostModel.step (.alloc L) b))
        (.free 1 c1) :=
      fitsEvent_small_of_dom_alloc32 (ev₂ := .free 1 128) (wf_free1 _) hd2
        (FineStepBound_mono_meta (req := 0) (align := 16) (fineMaxMetaAreas_mono_dom hd2)) hm3
    rw [heq_full] at hdom_end ⊢
    exact ⟨⟨hf0, hf1, hf2, trivial⟩, hdom_end⟩

private def modelDirs (k : Nat) : List (List (BitVec 8) × List (List (BitVec 8))) :=
  List.replicate k (dir32, [nm64])

private theorem modelDirs_zero_nil_in_phase :
    M5PhaseEnv (modelDirs 0) [] :=
  Or.inl rfl

private theorem modelDirs_zero_free_in_phase {ef : List AllocEvent} (hf : FreeOnlyEvs ef) :
    M5PhaseEnv (modelDirs 0) ef :=
  Or.inr ⟨[], ef, rfl, rfl, hf⟩

private theorem evsModel_in_m5PhaseEnv_succ (k : Nat) :
    M5PhaseEnv (modelDirs (k + 1)) evsModel := by
  unfold M5PhaseEnv
  have hrep : modelDirs (k + 1) = (dir32, [nm64]) :: modelDirs k := rfl
  rw [hrep]
  exact Or.inl (Or.inl evsModel_in_m5DirStepEnv)

private theorem m5PhaseEnv_cons_model (k : Nat) {evs_rest : List AllocEvent}
    (hr : M5PhaseEnv (modelDirs k) evs_rest) :
    M5PhaseEnv (modelDirs (k + 1)) (evsModel ++ evs_rest) := by
  unfold M5PhaseEnv at hr ⊢
  have hrep : modelDirs (k + 1) = (dir32, [nm64]) :: modelDirs k := rfl
  rw [hrep]
  rcases hr with hiter | ⟨e1, ef, rfl, hiter, hf⟩
  · exact Or.inl (Or.inr ⟨evsModel, evs_rest, rfl, evsModel_in_m5DirStepEnv, hiter⟩)
  · exact Or.inr ⟨evsModel ++ e1, ef, (List.append_assoc evsModel e1 ef).symm,
      Or.inr ⟨evsModel, e1, rfl, evsModel_in_m5DirStepEnv, hiter⟩, hf⟩

private theorem m5PhaseEnv_prepend_models :
    ∀ (m k : Nat) {evs_rest : List AllocEvent},
      M5PhaseEnv (modelDirs k) evs_rest →
      M5PhaseEnv (modelDirs (m + k)) (List.flatten (List.replicate m evsModel) ++ evs_rest)
  | 0, k, _, hr => by simpa using hr
  | m + 1, k, evs_rest, hr => by
    have ih := m5PhaseEnv_prepend_models m k hr
    have hadd : m + 1 + k = (m + k) + 1 := by omega
    rw [hadd]
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
    exact m5PhaseEnv_cons_model (m + k) ih

private theorem dom_step_replicate_model :
    ∀ (m : Nat) (b : FineBudget),
      FineBudgetDom b (fineCostModel.stepEvents (List.flatten (List.replicate m evsModel)) b)
  | 0, b => fineBudgetDom_refl b
  | m + 1, b => by
    have hd :
        FineBudgetDom b
          (fineCostModel.stepEvents (List.flatten (List.replicate m evsModel))
            (fineCostModel.stepEvents evsModel b)) :=
      fineBudgetDom_trans (dom_nil_evsModel b)
        (dom_step_replicate_model m (fineCostModel.stepEvents evsModel b))
    have hrep : List.flatten (List.replicate (m + 1) evsModel) =
        evsModel ++ List.flatten (List.replicate m evsModel) := by
      simp [List.replicate_succ]
    have happ :
        fineCostModel.stepEvents (List.flatten (List.replicate (m + 1) evsModel)) b =
          fineCostModel.stepEvents (List.flatten (List.replicate m evsModel))
            (fineCostModel.stepEvents evsModel b) :=
      (congrArg (fun xs => fineCostModel.stepEvents xs b) hrep).trans
        (fineCostModel.stepEvents_append evsModel (List.flatten (List.replicate m evsModel)) b)
    exact happ.symm ▸ hd

private theorem fitsEnv_drop_models {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    (m k : Nat) {b : FineBudget}
    (h : FitsEnv fineCostModel lim b (SeqEnv (M5PhaseEnv (modelDirs (m + k))) Tail)) :
    FitsEnv fineCostModel lim b (SeqEnv (M5PhaseEnv (modelDirs k)) Tail) := by
  intro evs hevs
  let pfx := List.flatten (List.replicate m evsModel)
  have hmem : SeqEnv (M5PhaseEnv (modelDirs (m + k))) Tail (pfx ++ evs) := by
    rcases hevs with hm5 | ⟨e1, e2, rfl, hm5, ht⟩
    · exact Or.inl (m5PhaseEnv_prepend_models m k hm5)
    · exact Or.inr ⟨pfx ++ e1, e2, (List.append_assoc pfx e1 e2).symm,
        m5PhaseEnv_prepend_models m k hm5, ht⟩
  have hboth := (fitsEvents_append fineCostModel lim pfx evs b).mp (h (pfx ++ evs) hmem)
  exact fitsEvents_of_fineBudgetDom evs (dom_step_replicate_model m b) hboth.2

private theorem fitsEnv_step_one_model {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    (k : Nat) {b : FineBudget}
    (h : FitsEnv fineCostModel lim b (SeqEnv (M5PhaseEnv (modelDirs (k + 1))) Tail)) :
    FitsEvents fineCostModel lim b evsModel ∧
      FitsEnv fineCostModel lim (fineCostModel.stepEvents evsModel b)
        (SeqEnv (M5PhaseEnv (modelDirs k)) Tail) := by
  have hm0 : FitsEvents fineCostModel lim b evsModel :=
    h evsModel (Or.inl (evsModel_in_m5PhaseEnv_succ k))
  refine ⟨hm0, fun evs hevs => ?_⟩
  have hmem : SeqEnv (M5PhaseEnv (modelDirs (k + 1))) Tail (evsModel ++ evs) := by
    rcases hevs with hm5 | ⟨e1, e2, rfl, hm5, ht⟩
    · exact Or.inl (m5PhaseEnv_cons_model k hm5)
    · exact Or.inr ⟨evsModel ++ e1, e2, (List.append_assoc evsModel e1 e2).symm,
        m5PhaseEnv_cons_model k hm5, ht⟩
  exact ((fitsEvents_append fineCostModel lim evsModel evs b).mp (h (evsModel ++ evs) hmem)).2

private theorem fitsEnv_freeOnly_zero {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    {b : FineBudget}
    (h : FitsEnv fineCostModel lim b (SeqEnv (M5PhaseEnv (modelDirs 0)) Tail))
    {ef : List AllocEvent} (hf : FreeOnlyEvs ef)
    {et : List AllocEvent} (ht : ef = et ∨ ∃ t, et = ef ++ t ∧ Tail t) :
    FitsEvents fineCostModel lim b et := by
  rcases ht with rfl | ⟨t, rfl, htail⟩
  · exact h ef (Or.inl (modelDirs_zero_free_in_phase hf))
  · exact h (ef ++ t) (Or.inr ⟨ef, t, rfl, modelDirs_zero_free_in_phase hf, htail⟩)

private theorem sim_entries {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    (Step : (List (BitVec 8) × List (BitVec 8)) → List AllocEvent → Prop)
    (entries : List (List (BitVec 8) × List (BitVec 8)))
    (hstep : ∀ e ∈ entries, ∀ evs_e b,
      Step e evs_e →
      FitsEvents fineCostModel lim b evsModel →
      FitsEvents fineCostModel lim b evs_e ∧
        FineBudgetDom (fineCostModel.stepEvents evs_e b) (fineCostModel.stepEvents evsModel b)) :
    ∀ (k_rem : Nat) {evs_ent : List AllocEvent} (b : FineBudget),
      IterSeqEnv Step entries evs_ent →
      FitsEnv fineCostModel lim b
        (SeqEnv (M5PhaseEnv (modelDirs (entries.length + k_rem))) Tail) →
      FitsEvents fineCostModel lim b evs_ent ∧
        ∃ b', FineBudgetDom (fineCostModel.stepEvents evs_ent b) b' ∧
          FitsEnv fineCostModel lim b' (SeqEnv (M5PhaseEnv (modelDirs k_rem)) Tail) := by
  induction entries with
  | nil =>
    intro k_rem evs_ent b hiter hfit
    change evs_ent = [] at hiter
    subst hiter
    dsimp only [List.length] at hfit
    rw [Nat.zero_add] at hfit
    exact ⟨trivial, b, fineBudgetDom_refl b, hfit⟩
  | cons e rest ih =>
    intro k_rem evs_ent b hiter hfit
    have hadd' : (e :: rest).length + k_rem = (rest.length + k_rem) + 1 := by
      simp [List.length_cons]; omega
    obtain ⟨hm_evs, hfit_next⟩ := fitsEnv_step_one_model (rest.length + k_rem) (hadd' ▸ hfit)
    rcases hiter with he1 | ⟨e1, e2, rfl, he1, hrest⟩
    · obtain ⟨hfe1, hdom1⟩ := hstep e List.mem_cons_self evs_ent b he1 hm_evs
      have hdrop := fitsEnv_drop_models rest.length k_rem hfit_next
      exact ⟨hfe1, fineCostModel.stepEvents evsModel b, hdom1, hdrop⟩
    · obtain ⟨hfe1, hdom1⟩ := hstep e List.mem_cons_self e1 b he1 hm_evs
      have hfit1 := fitsEnv_of_fineBudgetDom hdom1 hfit_next
      obtain ⟨hfe2, b', hdom2, hfit'⟩ :=
        ih (fun x hx => hstep x (List.mem_cons_of_mem e hx)) k_rem
          (fineCostModel.stepEvents e1 b) hrest hfit1
      have happ : fineCostModel.stepEvents (e1 ++ e2) b =
          fineCostModel.stepEvents e2 (fineCostModel.stepEvents e1 b) :=
        fineCostModel.stepEvents_append e1 e2 b
      exact ⟨(fitsEvents_append fineCostModel lim e1 e2 b).mpr ⟨hfe1, hfe2⟩,
        b', happ.symm ▸ hdom2, hfit'⟩

private theorem fineBudgetDom_stepFree_self (align req : Nat) (b : FineBudget) :
    FineBudgetDom (FineBudget.stepFree align req b) b := by
  unfold FineBudgetDom FineBudget.stepFree
  dsimp only
  split
  · unfold finePeak63Bytes finePeak63Count
    dsimp only
    exact ⟨Nat.le_refl _, Nat.le_refl _, by omega, by omega, by omega, by omega⟩
  · unfold finePeak63Bytes finePeak63Count
    dsimp only
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by omega,
      Nat.le_refl _, by omega⟩

private theorem fineBudgetDom_stepEvents_freeOnly :
    ∀ {ef : List AllocEvent}, FreeOnlyEvs ef → ∀ (b : FineBudget),
      FineBudgetDom (fineCostModel.stepEvents ef b) b
  | [], _, b => fineBudgetDom_refl b
  | e :: ef, hf, b => by
    obtain ⟨al, sz, rfl⟩ := hf e List.mem_cons_self
    change FineBudgetDom (fineCostModel.stepEvents ef (FineBudget.stepFree al sz b)) b
    exact fineBudgetDom_trans
      (fineBudgetDom_stepEvents_freeOnly (fun x hx => hf x (List.mem_cons_of_mem _ hx)) _)
      (fineBudgetDom_stepFree_self al sz b)

private theorem sim_seq_entries_free {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    (Step : (List (BitVec 8) × List (BitVec 8)) → List AllocEvent → Prop)
    (entries : List (List (BitVec 8) × List (BitVec 8)))
    (hstep : ∀ e ∈ entries, ∀ evs_e b,
      Step e evs_e →
      FitsEvents fineCostModel lim b evsModel →
      FitsEvents fineCostModel lim b evs_e ∧
        FineBudgetDom (fineCostModel.stepEvents evs_e b) (fineCostModel.stepEvents evsModel b))
    (k_rem : Nat) {evs_d : List AllocEvent} (b : FineBudget)
    (hd : SeqEnv (IterSeqEnv Step entries) FreeOnlyEvs evs_d)
    (hfit : FitsEnv fineCostModel lim b
      (SeqEnv (M5PhaseEnv (modelDirs (entries.length + k_rem))) Tail)) :
    FitsEvents fineCostModel lim b evs_d ∧
      FitsEnv fineCostModel lim (fineCostModel.stepEvents evs_d b)
        (SeqEnv (M5PhaseEnv (modelDirs k_rem)) Tail) := by
  rcases hd with hiter | ⟨e_it, ef, rfl, hiter, hf⟩
  · obtain ⟨hfe, b', hdom, hfit'⟩ := sim_entries Step entries hstep k_rem b hiter hfit
    exact ⟨hfe, fitsEnv_of_fineBudgetDom hdom hfit'⟩
  · obtain ⟨hfe, b', hdom, hfit'⟩ := sim_entries Step entries hstep k_rem b hiter hfit
    have hfit_b1 := fitsEnv_of_fineBudgetDom hdom hfit'
    have hfit_b0 : FitsEnv fineCostModel lim (fineCostModel.stepEvents e_it b)
        (SeqEnv (M5PhaseEnv (modelDirs 0)) Tail) :=
      fitsEnv_drop_models k_rem 0 hfit_b1
    have hfe_f : FitsEvents fineCostModel lim (fineCostModel.stepEvents e_it b) ef :=
      fitsEnv_freeOnly_zero hfit_b0 hf (Or.inl rfl)
    have happ : fineCostModel.stepEvents (e_it ++ ef) b =
        fineCostModel.stepEvents ef (fineCostModel.stepEvents e_it b) :=
      fineCostModel.stepEvents_append e_it ef b
    have hdom_all : FineBudgetDom (fineCostModel.stepEvents (e_it ++ ef) b) b' :=
      happ.symm ▸ fineBudgetDom_trans (fineBudgetDom_stepEvents_freeOnly hf _) hdom
    exact ⟨(fitsEvents_append fineCostModel lim e_it ef b).mpr ⟨hfe, hfe_f⟩,
      fitsEnv_of_fineBudgetDom hdom_all hfit'⟩

private theorem sim_dir {lim : BudgetLimits} {Tail : List AllocEvent → Prop}
    (d : DirGhost)
    (hp : ∀ e ∈ d.changed, (pathOf d.path e.1).length ≤ 64)
    (k_rem : Nat) {evs_d : List AllocEvent} (b : FineBudget)
    (hd : M5DirOkEnv d evs_d)
    (hfit : FitsEnv fineCostModel lim b
      (SeqEnv (M5PhaseEnv (modelDirs (d.changed.length + k_rem))) Tail)) :
    FitsEvents fineCostModel lim b evs_d ∧
      FitsEnv fineCostModel lim (fineCostModel.stepEvents evs_d b)
        (SeqEnv (M5PhaseEnv (modelDirs k_rem)) Tail) := by
  unfold M5DirOkEnv at hd
  by_cases hpath : d.path = []
  · simp only [hpath, ↓reduceIte] at hd
    unfold M5LoopBRestOkEnv at hd
    refine sim_seq_entries_free (fun e => M5LoopBStepEnv e.1) d.changed ?_ k_rem b hd hfit
    intro e he evs_e b0 hs hm
    have hlen : e.1.length ≤ 64 := by
      have hpe := hp e he
      simpa [pathOf, hpath] using hpe
    exact m5LoopBStep_dom_model hlen hs b0 hm
  · simp only [hpath, ↓reduceIte] at hd
    unfold M5LoopARestOkEnv at hd
    refine sim_seq_entries_free (fun e => M5LoopAStepEnv d.path e.1) d.changed ?_ k_rem b hd hfit
    intro e he evs_e b0 hs hm
    exact m5LoopAStep_dom_model hpath (hp e he) hs b0 hm

private theorem sim_dirs {lim : BudgetLimits} {Tail : List AllocEvent → Prop} :
    ∀ (ds : List DirGhost),
      (∀ d ∈ ds, ∀ e ∈ d.changed, (pathOf d.path e.1).length ≤ 64) →
      ∀ {evs_ds : List AllocEvent} (b : FineBudget),
        M5DirsOkEnv ds evs_ds →
        FitsEnv fineCostModel lim b
          (SeqEnv (M5PhaseEnv (modelDirs ((ds.map (fun d => d.changed.length)).sum))) Tail) →
        FitsEvents fineCostModel lim b evs_ds ∧
          FitsEnv fineCostModel lim (fineCostModel.stepEvents evs_ds b)
            (SeqEnv (M5PhaseEnv (modelDirs 0)) Tail)
  | [], _, evs_ds, b, hds, hfit => by
    change evs_ds = [] at hds
    subst hds
    exact ⟨trivial, hfit⟩
  | d :: ds', hp, evs_ds, b, hds, hfit => by
    simp only [List.map_cons, List.sum_cons] at hfit
    rcases hds with hd1 | ⟨e1, e2, rfl, hd1, hrest⟩
    · obtain ⟨hfe1, hfit1⟩ :=
        sim_dir d (hp d List.mem_cons_self) ((ds'.map (fun x => x.changed.length)).sum) b hd1 hfit
      have hdrop :=
        fitsEnv_drop_models ((ds'.map (fun x => x.changed.length)).sum) 0 hfit1
      exact ⟨hfe1, hdrop⟩
    · obtain ⟨hfe1, hfit1⟩ :=
        sim_dir d (hp d List.mem_cons_self) ((ds'.map (fun x => x.changed.length)).sum) b hd1 hfit
      obtain ⟨hfe2, hfit2⟩ :=
        sim_dirs ds' (fun x hx => hp x (List.mem_cons_of_mem d hx))
          (fineCostModel.stepEvents e1 b) hrest hfit1
      have happ : fineCostModel.stepEvents (e1 ++ e2) b =
          fineCostModel.stepEvents e2 (fineCostModel.stepEvents e1 b) :=
        fineCostModel.stepEvents_append e1 e2 b
      exact ⟨(fitsEvents_append fineCostModel lim e1 e2 b).mpr ⟨hfe1, hfe2⟩,
        happ.symm ▸ hfit2⟩

private theorem flatMap_writes_length :
    ∀ (ds : List DirGhost),
      (ds.flatMap DirGhost.writes).length = (ds.map (fun d => d.changed.length)).sum
  | [] => rfl
  | d :: ds => by
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      DirGhost.writes, List.length_map, flatMap_writes_length ds]

private theorem modelDirs_sum (k : Nat) :
    ((modelDirs k).map (fun dn => dn.2.length)).sum = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hcons : modelDirs (k + 1) = (dir32, [nm64]) :: modelDirs k := rfl
    rw [hcons, List.map_cons, List.sum_cons, ih]
    dsimp only [List.length]
    omega

private theorem modelDirs_bounds (k : Nat) :
    ∀ dn ∈ modelDirs k,
      dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes := by
  intro dn hdn
  unfold modelDirs at hdn
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hdn
  refine ⟨by decide, fun nm hnm => ?_⟩
  rw [List.mem_singleton] at hnm
  subst hnm
  decide

private theorem m5Env_m6Env_fitsEnv_of_modelDirs {lim : BudgetLimits}
    {sg : StoresGhost} {ok : Bool} {st4 : FineBudget}
    (hp : ∀ d ∈ storesDirs sg, ∀ e ∈ d.changed, (pathOf d.path e.1).length ≤ 64)
    (hfit : FitsEnv fineCostModel lim st4
      (SeqEnv (M5PhaseEnv (modelDirs (((storesDirs sg).map (fun d => d.changed.length)).sum)))
        (M6Env ok))) :
    FitsEnv fineCostModel lim st4 (SeqEnv (M5Env sg) (M6Env ok)) := by
  intro evs56 hevs
  rcases hevs with hm5 | ⟨em5, em6, rfl, hm5, hm6⟩
  · rcases hm5 with hdirs | ⟨ed, ef, rfl, hdirs, hf⟩
    · exact (sim_dirs (storesDirs sg) hp st4 hdirs hfit).1
    · obtain ⟨hfe_d, hfit_d⟩ := sim_dirs (storesDirs sg) hp st4 hdirs hfit
      have hfe_f := fitsEnv_freeOnly_zero hfit_d hf (Or.inl rfl)
      exact (fitsEvents_append fineCostModel lim ed ef st4).mpr ⟨hfe_d, hfe_f⟩
  · rcases hm5 with hdirs | ⟨ed, ef, rfl, hdirs, hf⟩
    · obtain ⟨hfe_d, hfit_d⟩ := sim_dirs (storesDirs sg) hp st4 hdirs hfit
      have hfe_m6 : FitsEvents fineCostModel lim (fineCostModel.stepEvents em5 st4) em6 :=
        hfit_d em6 (Or.inr ⟨[], em6, rfl, modelDirs_zero_nil_in_phase, hm6⟩)
      exact (fitsEvents_append fineCostModel lim em5 em6 st4).mpr ⟨hfe_d, hfe_m6⟩
    · obtain ⟨hfe_d, hfit_d⟩ := sim_dirs (storesDirs sg) hp st4 hdirs hfit
      have hfe_f := fitsEnv_freeOnly_zero hfit_d hf (Or.inl rfl)
      have hfit_m6_b0 : FitsEnv fineCostModel lim (fineCostModel.stepEvents ed st4) (M6Env ok) :=
        fun x hx => hfit_d x (Or.inr ⟨[], x, rfl, modelDirs_zero_nil_in_phase, hx⟩)
      have happ : fineCostModel.stepEvents (ed ++ ef) st4 =
          fineCostModel.stepEvents ef (fineCostModel.stepEvents ed st4) :=
        fineCostModel.stepEvents_append ed ef st4
      have hfit_m6_bf :
          FitsEnv fineCostModel lim (fineCostModel.stepEvents (ed ++ ef) st4) (M6Env ok) :=
        happ.symm ▸ fitsEnv_of_fineBudgetDom (fineBudgetDom_stepEvents_freeOnly hf _) hfit_m6_b0
      exact (fitsEvents_append fineCostModel lim (ed ++ ef) em6 st4).mpr
        ⟨(fitsEvents_append fineCostModel lim ed ef st4).mpr ⟨hfe_d, hfe_f⟩, hfit_m6_bf em6 hm6⟩

/-! ## 7. `MainEntryBudgetFitsCapOf` and `MainEntryBudgetFitsCap` Discharge Theorems -/

private theorem dom_seqEnv_assoc_left {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E₁ (SeqEnv E₂ E₃) evs) :
    SeqEnv (SeqEnv E₁ E₂) E₃ evs := by
  rcases h with h1 | ⟨evs₁, evs₂₃, rfl, h1, h23⟩
  · exact Or.inl (Or.inl h1)
  · rcases h23 with h2 | ⟨evs₂, evs₃, rfl, h2, h3⟩
    · exact Or.inl (Or.inr ⟨evs₁, evs₂₃, rfl, h1, h2⟩)
    · exact Or.inr ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
        Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩

private def domSt0 (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st0 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st0 (SeqEnv (CliMainBoundedSetupEnv i.argv.length) FreeOnlyEvs) ∧
  (Dom i → FitsEnv fineCostModel lim st0 (RealCliMainBinaryEnvOf E i))

private def domSt1 (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (st1 : FineBudget) : Prop :=
  FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs) ∧
  (Dom i → FitsEnv fineCostModel lim st1 (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i)))

private def domSt2 (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st2 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv FreeOnlyEvs) ∧
  (Dom i → FitsEnv fineCostModel lim st2 (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i)))

private def domSt3 (Dom : Inputs → Prop) (E : RunCall → CliRunCalleeEnvs) (lim : BudgetLimits)
    (i : Inputs) (c : CallV) (st3 : FineBudget) : Prop :=
  parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
  FitsEnv fineCostModel lim st3 FreeOnlyEvs ∧
  (Dom i → FitsEnv fineCostModel lim st3 (PostSetupTailEnv E i))

private theorem domSt0_init_of_fitsEnv {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits}
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    {i : Inputs} (hok : CliInputsOk i) :
    domSt0 Dom E lim i fineCostModel.init :=
  ⟨hEarly i.argv.length (argvFits_length_le hok.2), hMain i⟩

private theorem domSt01_of_st0 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st0 : FineBudget}
    (hst0 : domSt0 Dom E lim i st0) :
    FitsEvents fineCostModel lim st0 (rustAllocEvents (16 * i.argv.length) 8) ∧
      domSt1 Dom E lim i
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) st0) := by
  have hm1 : M1PhaseEnv i.argv.length (rustAllocEvents (16 * i.argv.length) 8) := Or.inr rfl
  have hEarlySeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) FreeOnlyEvs)) :=
    fun evs h => hst0.1 evs
      (seqEnv_mono (fun _ => Or.inr) (fun _ hf => hf) (dom_seqEnv_assoc_left h))
  obtain ⟨hfits₁, hEarly₁⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm1
  refine ⟨hfits₁, hEarly₁, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st0
      (SeqEnv (M1PhaseEnv i.argv.length)
        (SeqEnv (PostM1SetupEnv i.argv.length) (PostSetupTailEnv E i))) :=
    fun evs h => hst0.2 hi evs
      (seqEnv_mono (fun _ => Or.inr) (fun _ ht => ht) (dom_seqEnv_assoc_left h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm1).2

private theorem fitsEnv_m2EarlyExit_of_domSt1 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {st1 : FineBudget}
    (hst1 : domSt1 Dom E lim i st1) :
    FitsEnv fineCostModel lim st1 (SeqEnv (M2PhaseEnv i.argv.length) FreeOnlyEvs) :=
  fun evs h => hst1.1 evs
    (seqEnv_mono (fun _ => postM1SetupEnv_of_m2Phase) (fun _ hf => hf) h)

private theorem fitsEvents_and_domSt2_of_domSt1 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st1 : FineBudget}
    (hst1 : domSt1 Dom E lim i st1)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    {evs₂ : List AllocEvent} (hm2 : M2PhaseEnv i.argv.length evs₂) :
    FitsEvents fineCostModel lim st1 evs₂ ∧
      domSt2 Dom E lim i c (fineCostModel.stepEvents evs₂ st1) := by
  have hEarlySeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length) (SeqEnv M3BoundedSetupEnv FreeOnlyEvs)) :=
    fun evs h => hst1.1 evs
      (seqEnv_mono (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ hf => hf)
        (dom_seqEnv_assoc_left h))
  obtain ⟨hfits₂, hEarly₂⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hEarlySeq hm2
  refine ⟨hfits₂, hparse, hEarly₂, fun hi => ?_⟩
  have hMainSeq : FitsEnv fineCostModel lim st1
      (SeqEnv (M2PhaseEnv i.argv.length)
        (SeqEnv M3BoundedSetupEnv (PostSetupTailEnv E i))) :=
    fun evs h => hst1.2 hi evs
      (seqEnv_mono (fun _ => postM1SetupEnv_of_seq_m2Phase_m3) (fun _ ht => ht)
        (dom_seqEnv_assoc_left h))
  exact (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hMainSeq hm2).2

private theorem fitsEvents_and_domSt3_of_domSt2 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st2 : FineBudget}
    (hst2 : domSt2 Dom E lim i c st2)
    {evs₃ : List AllocEvent} (hm3 : M3BoundedSetupEnv evs₃) :
    FitsEvents fineCostModel lim st2 evs₃ ∧
      domSt3 Dom E lim i c (fineCostModel.stepEvents evs₃ st2) := by
  obtain ⟨hfits₃, hFree₃⟩ := fitsEvents_and_fitsEnv_stepEvents_of_seqEnv hst2.2.1 hm3
  exact ⟨hfits₃, hst2.1, hFree₃, fun hi =>
    (fitsEvents_and_fitsEnv_stepEvents_of_seqEnv (hst2.2.2 hi) hm3).2⟩

private theorem fitsEnv_run_and_st4_of_domSt3 {Dom : Inputs → Prop} {E : RunCall → CliRunCalleeEnvs}
    {lim : BudgetLimits} {i : Inputs} {c : CallV} {st3 : FineBudget}
    (hst3 : domSt3 Dom E lim i c st3)
    (hi : Dom i)
    (hstdin : i.stdin.length ≤ msgCapBytes)
    (rc : RunCall) (hrc_i : rc.i = i) (hrc_c : rc.c = c) :
    FitsEnv fineCostModel lim st3 (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) ∧
      ∀ evs₄ : List AllocEvent,
        CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc evs₄ →
        FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs ∧
          ∀ g : StoresGhost, mainSt4 lim i c g (fineCostModel.stepEvents evs₄ st3) := by
  have hTail := hst3.2.2 hi
  have hparse_rc : parseArgs uuidTryParse (rc.i.argv.map bytesOfString) = some rc.c := by
    rw [hrc_i, hrc_c]; exact hst3.1
  have hstdin_rc : rc.i.stdin.length ≤ msgCapBytes := by
    rw [hrc_i]; exact hstdin
  let w0 : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := []
      dirs_sum_le := Nat.zero_le _
      dirs_bounds := fun _ hm => nomatch hm
      ok := false }
  have hRunFits : FitsEnv fineCostModel lim st3
      (CliRunBinaryEnv cliIo.rd (E rc) sessionCapBytes rc) :=
    fun evs hrun => hTail evs (Or.inr ⟨w0, hrc_i, Or.inl hrun⟩)
  refine ⟨hRunFits, fun evs₄ hrun₄ => ?_⟩
  have hFree₄ : FitsEnv fineCostModel lim (fineCostModel.stepEvents evs₄ st3) FreeOnlyEvs := by
    intro evs_f hf
    have hm5 : M5PhaseEnv [] evs_f := Or.inr ⟨[], evs_f, rfl, rfl, hf⟩
    exact ((fitsEvents_append fineCostModel lim evs₄ evs_f st3).mp
      (hTail (evs₄ ++ evs_f)
        (Or.inr ⟨w0, hrc_i, Or.inr ⟨evs₄, evs_f, rfl, hrun₄, Or.inl hm5⟩⟩))).2
  refine ⟨hFree₄, fun _g => ⟨hst3.1, hstdin, hFree₄, fun dirs ok hsum hbounds => ?_⟩⟩
  let w : ValidPostSetupWitness i :=
    { g := rc
      g_i := hrc_i
      parse_ok := hparse_rc
      stdin_le := hstdin_rc
      dirs := dirs
      dirs_sum_le := hsum
      dirs_bounds := hbounds
      ok := ok }
  intro evs₅₆ hm56
  exact ((fitsEvents_append fineCostModel lim evs₄ evs₅₆ st3).mp
    (hTail (evs₄ ++ evs₅₆)
      (Or.inr ⟨w, hrc_i, Or.inr ⟨evs₄, evs₅₆, rfl, hrun₄, hm56⟩⟩))).2

/-- Arbitrary-domain `(Dom, S)` and `ReadEnv`-parametric whole-`main` `FitsEnv` to
`MainEntryBudgetFitsCapOf` bridge. -/
theorem mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv
    {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {S : RunSem}
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hStdinDom : ∀ (i : Inputs) (c : CallV), Dom i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      (inputOf i c).length ≤ stdinCapBytes →
      i.stdin.length ≤ msgCapBytes)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      Dom i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hRunSub : ∀ g : RunCall, Dom g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel S g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse RunEnv
      (domScopedRun Dom (runRel S)) := by
  intro i hok
  have hst0 := domSt0_init_of_fitsEnv hEarly hMain hok
  refine ⟨fun _hne => (domSt01_of_st0 hst0).1, fun _hne => ?_⟩
  have hst1 := (domSt01_of_st0 hst0).2
  refine ⟨fun evs hm2pre =>
    fitsEnv_m2EarlyExit_of_domSt1 hst1 evs (Or.inl (m2PreDeallocEnv_imp_m2PhaseEnv hok hm2pre)),
    fun vcap evs_c c hc _hv hp => ?_⟩
  let evs_m2 :=
    evs_c ++
      (m2DispatchEvents uuidTryParse (i.argv.map bytesOfString) ++
        rustDeallocEvents (vcap.toNat * 16) 8)
  have hm2 : M2PhaseEnv i.argv.length evs_m2 :=
    Or.inr ⟨evs_c, _, rfl, Or.inl hc,
      seqEnv_append_freeOnly_tail bundleOptBoundedEnv_nil
        (m2DispatchEvents_in_addr_bundle hok)
        (freeOnlyEvs_rustDealloc (vcap.toNat * 16) 8)⟩
  have hstep_m2 :
      fineCostModel.stepEvents evs_m2
        (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8) fineCostModel.init) =
      fineCostModel.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
        (fineCostModel.stepEvents (m2DispatchEvents uuidTryParse (i.argv.map bytesOfString))
          (fineCostModel.stepEvents evs_c
            (fineCostModel.stepEvents (rustAllocEvents (16 * i.argv.length) 8)
              fineCostModel.init))) := by
    simp only [evs_m2, fineCostModel.stepEvents_append]
  have hst2 := hstep_m2 ▸ (fitsEvents_and_domSt2_of_domSt1 hst1 hp hm2).2
  refine ⟨fun evs hm3 =>
    hst2.2.1 evs (Or.inl (m3EnvReadOf_imp_m3BoundedSetupEnv hReadSub i c hm3)),
    fun evs_m3 hm3 => ?_⟩
  have hst3 := (fitsEvents_and_domSt3_of_domSt2 hst2 (m3EnvReadOf_imp_m3BoundedSetupEnv hReadSub i c hm3)).2
  refine ⟨hst3.2.1, fun hin a resP callP storesP inpP coinsP hrun => ?_⟩
  rcases hrun with ⟨hi, hrel⟩
  have hstdin := hStdinDom i c hi hp hin
  let g : RunCall :=
    { i := i, c := c, a := a,
      res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
  obtain ⟨hRunBinFits, hAfterRun⟩ := fitsEnv_run_and_st4_of_domSt3 hst3 hi hstdin g rfl rfl
  refine ⟨fun evs hr => hRunBinFits evs (hRunSub g hi hp hin hrel evs hr), fun evs_r hr => ?_⟩
  obtain ⟨hFree4, hst4Of⟩ := hAfterRun evs_r (hRunSub g hi hp hin hrel evs_r hr)
  refine ⟨hFree4, fun sg out ha_eq hpw ok => ?_⟩
  have ha_ans : runAns S i = some (some (namedWrites sg.writes, out)) :=
    hrel.2.2.2.2.2.symm.trans ha_eq
  obtain ⟨hlen_nw, hlen_paths⟩ := hNwDom i (namedWrites sg.writes) out hi ha_ans
  have hasc : ∀ pw ∈ sg.writes, ∀ bt ∈ pw.1, bt.toNat < 128 :=
    fun pw hmem => (hpw pw hmem).1.2.1.1
  have hnw_eq : namedWrites sg.writes = sg.writes.map (fun w => (pathStr w.1, w.2)) :=
    namedWrites_ascii sg.writes hasc
  have hwr_len : sg.writes.length ≤ 4 := by
    have hmap_len : (namedWrites sg.writes).length = sg.writes.length := by
      rw [hnw_eq, List.length_map]
    omega
  have hsum_dirs :
      ((storesDirs sg).map (fun d => d.changed.length)).sum ≤ cliMaxDirtyEntries := by
    rw [← flatMap_writes_length (storesDirs sg), storesDirs_writes sg]
    have h4 : cliMaxDirtyEntries = 4 := rfl
    omega
  have hp_dirs : ∀ d ∈ storesDirs sg, ∀ e ∈ d.changed, (pathOf d.path e.1).length ≤ 64 := by
    intro d hd e he
    have hmem_wr : (pathOf d.path e.1, e.2) ∈ sg.writes := by
      rw [← storesDirs_writes sg]
      exact List.mem_flatMap.mpr ⟨d, hd, List.mem_map.mpr ⟨e, he, rfl⟩⟩
    have hmem_nw : (pathStr (pathOf d.path e.1), e.2) ∈ namedWrites sg.writes := by
      rw [hnw_eq]
      exact List.mem_map_of_mem hmem_wr
    have hlen_str := hlen_paths _ hmem_nw
    rwa [pathStr_length_of_ascii (hasc _ hmem_wr)] at hlen_str
  let k := ((storesDirs sg).map (fun d => d.changed.length)).sum
  have hm_sum : ((modelDirs k).map (fun dn => dn.2.length)).sum ≤ cliMaxDirtyEntries := by
    rw [modelDirs_sum k]
    exact hsum_dirs
  exact m5Env_m6Env_fitsEnv_of_modelDirs hp_dirs
    ((hst4Of sg).2.2.2 (modelDirs k) ok hm_sum (modelDirs_bounds k))

/-- `cliBudgetLimits` specialization of `mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv`. -/
theorem mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {S : RunSem}
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hStdinDom : ∀ (i : Inputs) (c : CallV), Dom i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      (inputOf i c).length ≤ stdinCapBytes →
      i.stdin.length ≤ msgCapBytes)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      Dom i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hRunSub : ∀ g : RunCall, Dom g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel S g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (domScopedRun Dom (runRel S)) :=
  mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv
    hReadSub cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 hMain hStdinDom hNwDom hRunSub

/-- `ReadFileRuleEnv cliIo.rd` (`MainEntryBudgetFitsCap`) specialization of
`mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv`. -/
theorem mainEntryBudgetFitsCap_domScopedRun_of_fitsEnv
    {lim : BudgetLimits}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {S : RunSem}
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hStdinDom : ∀ (i : Inputs) (c : CallV), Dom i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      (inputOf i c).length ≤ stdinCapBytes →
      i.stdin.length ≤ msgCapBytes)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      Dom i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hRunSub : ∀ g : RunCall, Dom g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel S g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse RunEnv
      (domScopedRun Dom (runRel S)) :=
  mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv
    (fun files path _ hc => boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hc)
    hEarly hMain hStdinDom hNwDom hRunSub

/-- `cliBudgetLimits` and `ReadFileRuleEnv cliIo.rd` specialization of `mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv`. -/
theorem mainEntryBudgetFitsCap_domScopedRun_cliBudgetLimits_of_kitEnvFits
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {Dom : Inputs → Prop} {S : RunSem}
    (hMain : ∀ i : Inputs, Dom i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hStdinDom : ∀ (i : Inputs) (c : CallV), Dom i →
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some c →
      (inputOf i c).length ≤ stdinCapBytes →
      i.stdin.length ≤ msgCapBytes)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      Dom i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hRunSub : ∀ g : RunCall, Dom g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel S g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCap fineCostModel cliBudgetLimits fineCostModel.init cliIo uuidTryParse
      RunEnv (domScopedRun Dom (runRel S)) :=
  mainEntryBudgetFitsCap_domScopedRun_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 hMain hStdinDom hNwDom hRunSub

/-- `ReadEnv`-parameterized whole-`main` `FitsEnv` to `MainEntryBudgetFitsCapOf` bridge covering
both `ReadFileRuleEnv cliIo.rd` and `ReadFileRuleEnvFixed cliIo.rd`. -/
theorem mainEntryBudgetFitsCapOf_of_fitsEnv
    {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hRunSub : ∀ g : RunCall, CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel (cliRunSemD2c_placed X W) g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel lim fineCostModel.init cliIo ReadEnv uuidTryParse RunEnv
      (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCapOf_domScopedRun_of_fitsEnv
    hReadSub hEarly hMain
    (fun _ _ hi hp hin => stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi hp hin)
    (fun _ _ _ hi ha => pqRunAns_namedWrites_bounds hi ha)
    hRunSub

/-- `cliBudgetLimits` specialization of `mainEntryBudgetFitsCapOf_of_fitsEnv`. -/
theorem mainEntryBudgetFitsCapOf_cliBudgetLimits_of_kitEnvFits
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hReadSub : ∀ (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent),
      ReadEnv files path evs → BoundedReadFileEnv evs)
    (hMain : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hRunSub : ∀ g : RunCall, CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel (cliRunSemD2c_placed X W) g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
      uuidTryParse RunEnv (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCapOf_of_fitsEnv
    hReadSub cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 hMain hRunSub

/-- Whole-`main` `FitsEnv` to `MainEntryBudgetFitsCap` bridge for any callee-envelope family
`E : RunCall → CliRunCalleeEnvs` and any `RunEnv` included in `CliRunBinaryEnv` on
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem mainEntryBudgetFitsCap_of_fitsEnv
    {lim : BudgetLimits}
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hEarly : ∀ argvLen : Nat, argvLen ≤ 1820 →
      FitsEnv fineCostModel lim fineCostModel.init
        (SeqEnv (CliMainBoundedSetupEnv argvLen) FreeOnlyEvs))
    (hMain : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hRunSub : ∀ g : RunCall, CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel (cliRunSemD2c_placed X W) g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse RunEnv
      (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCapOf_of_fitsEnv
    (fun files path _ hc => boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hc)
    hEarly hMain hRunSub

/-- `cliBudgetLimits` specialization of `mainEntryBudgetFitsCap_of_fitsEnv`. -/
theorem mainEntryBudgetFitsCap_cliBudgetLimits_of_kitEnvFits
    {E : RunCall → CliRunCalleeEnvs}
    {RunEnv : RunCall → List AllocEvent → Prop}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hMain : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E i))
    (hRunSub : ∀ g : RunCall, CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      runRel (cliRunSemD2c_placed X W) g.i g.a →
      ∀ evs : List AllocEvent, RunEnv g evs →
        CliRunBinaryEnv cliIo.rd (E g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCap fineCostModel cliBudgetLimits fineCostModel.init cliIo uuidTryParse
      RunEnv (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCap_of_fitsEnv
    cliMainSetupEarlyExit_fitsEnv_cliBudgetLimits_le1820 hMain hRunSub

/-- `< 90%` (`cliRealNinetyPctOneGiB ≤ lim.physCap`) `MainEntryBudgetFitsCap` at `mkExistentialRealCalleeEnvs`. -/
theorem mainEntryBudgetFitsCap_of_realMainEnvFits_90pct [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap90 : cliRealNinetyPctOneGiB ≤ lim.physCap)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      (fun g =>
        CliRunBinaryEnv cliIo.rd
          (mkExistentialRealCalleeEnvs img (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩ g)
          sessionCapBytes g)
      (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCap_of_fitsEnv
    (fun _ hargv => cliMainSetupEarlyExit_90pct_fitsEnv_le1820 henf hsb hsc hcap90 hargv)
    (realCliMainBinaryEnvOf_90pct_fitsEnv_concrete henf hsb hsc hcap90 img
      (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩)
    (fun _ _ _ _ _ _ hr => hr)

/-- `≤ 1 GiB` (`cliOneGiB ≤ lim.physCap`) `MainEntryBudgetFitsCap` at `mkExistentialRealCalleeEnvs`. -/
theorem mainEntryBudgetFitsCap_of_realMainEnvFits_1GiB [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    MainEntryBudgetFitsCap fineCostModel lim fineCostModel.init cliIo uuidTryParse
      (fun g =>
        CliRunBinaryEnv cliIo.rd
          (mkExistentialRealCalleeEnvs img (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩ g)
          sessionCapBytes g)
      (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCap_of_fitsEnv
    (fun _ hargv =>
      cliMainSetupEarlyExit_90pct_fitsEnv_le1820 henf hsb hsc
        (Nat.le_trans (by unfold cliRealNinetyPctOneGiB cliOneGiB; decide) hcap1G) hargv)
    (realCliMainBinaryEnvOf_fitsEnv_concrete henf hsb hsc hcap1G img
      (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩)
    (fun _ _ _ _ _ _ hr => hr)

/-- `cliBudgetLimits` (`1 GiB`) `MainEntryBudgetFitsCap` at `mkExistentialRealCalleeEnvs`. -/
theorem mainEntryBudgetFitsCap_of_realMainEnvFits_cliBudgetLimits [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    MainEntryBudgetFitsCap fineCostModel cliBudgetLimits fineCostModel.init cliIo uuidTryParse
      (fun g =>
        CliRunBinaryEnv cliIo.rd
          (mkExistentialRealCalleeEnvs img (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩ g)
          sessionCapBytes g)
      (pqScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) :=
  mainEntryBudgetFitsCap_cliBudgetLimits_of_kitEnvFits
    (realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_concrete img
      (cliRunSemD2c_placed X W) ⟨W.C, W.Q⟩)
    (fun _ _ _ _ _ _ hr => hr)

end LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal

