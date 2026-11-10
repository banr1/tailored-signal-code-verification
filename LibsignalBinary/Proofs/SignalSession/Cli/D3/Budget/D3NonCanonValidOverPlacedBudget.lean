/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Pksm

/-!
# Budget-Threaded `validOver` (`DecPkOkOverV4`) Slot, Block-`579` `run`, and `mainSpecTightPlacedAt` Lift

Defines the non-matching session-overwrite semantics (`cliRunSemOverV4`, `pqD3ScopedRun`), proves
model correspondence (`runRel_pqRecv_validOver`, `runRel_pqRecv_canonicalNoMatch`), and lifts the
budget-threaded `DecPkOkOverV4` poll contracts to block `520` (`decrypt_prekey`), block `579`
(`runSpecTightPlaced`), and block `617` (`mainSpecTightPlacedAt`), including `LibsignalFrozen` /
`[LibsignalFullPlacement]` and `SpqrV1PlacedSeamsOfEnv` variants.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession (GhostState PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi
  (PreKeySignalMessage ProtoPreKeySignalMessage SessionRecord)
open CryptoGames.LibsignalSessionApi.Prost (bytesField key uint32Field varint)
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalPlacement blkPl_111 lsProg_51
   lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (stageP1ProgPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives
   aesDecHookMallocng djbKey kyberKey wirePrekey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks Inputs OutcomeMatchesModelExceptPath PqParty
   PqSessionMatches PqxdhPartyInSpecDomain cliExternsPlaced lsReadFileSym observe partyAddress
   pqRecvInputs pqRecvPrekeyModel sessionFile)
open CryptoVerification.SignalSession.Cli
  (CommitOk MainResult RunAnswer cliStaticsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunNeeds
   cliWrOk domainArgv_pqRecv mProgPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunHsOk RunNeeds RunSem dpPollNeed mkSlot runAns runFiles runProgPlaced runRel)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (cliDecryptPrekeyNeed dpWrapFrame pkToE? pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (pkToE?_pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse pksmParse_bytes)
open CryptoVerification.SignalSession.Cli.RunRefine (argsOf argsOf_bytes runBounds_pqRecv)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ runEncOk_pqRecv scopeIn
   scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
  (PromoteOverEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
  (pqxdhLogClosurePlacedSpec)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (D3NoMatchSessionFile DecPkOkOverV4 commitOk_pqRecvPrekey_decPkOverDef decPkOkOverV4_pqRecv
   decPkOverDef observedExcept_and_noMatchSessionFile_runAns_canonical
   observedExcept_and_noMatchSessionFile_runAns_decPkOverDef)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (cliRunSemF3 runFilesOk_pqRecv_cli_f3 runHsOk_pqRecvPrekey_body_f3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
  (DecPkD3ValidOverCliEnv DecPkD3ValidOverEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget
  (StageP4Prev1VRegsAtPlacedStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
  (decPk_d3_validOver_poll_at_full_placedBudget decPk_d3_validOver_poll_full_placedBudget
   decPk_d3_validOver_poll_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
  (StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt StageP2OverQpanCliD3FrozenPlacedBudgetStmt
   StageP2OverQpanCliD3PlacedBudgetStmt StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt
   StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt StageP2PathCOverQpanCliD3PlacedBudgetStmt
   decPk_d3_validOver_stage2_at_full_placedBudget decPk_d3_validOver_stage2_full_placedBudget
   decPk_d3_validOver_stage2_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
  (StageP3Prev1D3FrozenPlacedStmt StageP3Prev1D3PlacedStmt over_tryDecrypt_cli_placed_ok_at
   stageP3_prev1_d3_full_placed_ok stageP3_prev1_d3_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmEnvs RunArmsFrozenPlaced RunArmsPlaced RunEnv run_ok_frozen_placed_at_block
   run_ok_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
  (CliStageP4Prev1Envs StageP4Prev1VRegsPlacedStmt cliPollStageP4Prev1Envs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
  (overPollTryDecryptPlacedSpecTPTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlacedBudget
  (stageP4Prev1_placed_inst stageP4Prev1_vregs_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
  (cliDecryptPrekey_ok_state_frozen_placed_at_block cliDecryptPrekey_ok_state_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (decPkSlotSpecFrozenPlaced decPkSlotSpecPlaced dpSlotPollKStatePlaced
   dpSlot_ok_state_frozen_placed dpSlot_ok_state_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (ReadFileRuleEnv mainSpecTightPlacedAt readFileSpecPlaced runSpecPlaced
   sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Pure Non-Matching Overwrite Semantics (`cliRunSemOverV4`, `validOver`, `canonicalNoMatch`) -/

/-- `RunSem` instantiated with `decPkOverDef`, `DecPkOkOverV4`, and `Pksm.pksmParse`. -/
noncomputable def cliRunSemOverV4 (X : UnreachedPqxdhPrimitives) (W : CliHooks) : RunSem :=
  cliRunSemF3 X W (decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn) pksmParse

/-- Restricts `Run₀ : Inputs → RunAnswer → Prop` to `CliPqOrD3RecvDom WP`. -/
def pqD3ScopedRun (WP : PEParams) (Run₀ : Inputs → RunAnswer → Prop)
    (i : Inputs) (a : RunAnswer) : Prop :=
  CliPqOrD3RecvDom WP i ∧ Run₀ i a

private theorem varint_length_le_5 {n : Nat} (hn : n < 2 ^ 32) :
    (varint n).length ≤ 5 := by
  unfold varint; split
  · simp
  · dsimp only [List.length_cons]; unfold varint; split
    · simp
    · dsimp only [List.length_cons]; unfold varint; split
      · simp
      · dsimp only [List.length_cons]; unfold varint; split
        · simp
        · dsimp only [List.length_cons]; unfold varint
          have h5 : n / 128 / 128 / 128 / 128 < 128 := by omega
          simp [h5]

private theorem key_length_le_5 {tag wt : Nat} (h : 8 * tag + wt < 2 ^ 32) :
    (key tag wt).length ≤ 5 :=
  varint_length_le_5 h

private theorem uint32Field_length_le_10 {tag : Nat} (ht : 8 * tag < 2 ^ 32)
    (ov : Option (BitVec 32)) :
    (uint32Field tag ov).length ≤ 10 := by
  cases ov with
  | none => simp [uint32Field]
  | some v =>
    simp only [uint32Field, List.length_append]
    have h1 := key_length_le_5 (wt := 0) (by omega)
    have h2 := varint_length_le_5 v.isLt
    omega

private theorem bytesField_some_length_le {tag : Nat} {bs : List (BitVec 8)}
    (ht : 8 * tag + 2 < 2 ^ 32) (hbs : bs.length < 2 ^ 32) :
    (bytesField tag (some bs)).length ≤ bs.length + 10 := by
  simp only [bytesField, List.length_append]
  have h1 := key_length_le_5 ht
  have h2 := varint_length_le_5 hbs
  omega

private theorem preKeyMsgE_bytes_lt_2_32_local {m : PreKeyMessageFields}
    (hm : m.inner.length + 2048 < 2 ^ 32) :
    m.bytes.length < 2 ^ 32 := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  have h1 := uint32Field_length_le_10 (tag := 1) (by decide) m.opkId
  have h2 := bytesField_some_length_le (tag := 2) (bs := djbKey m.baseKey) (by decide)
    (by simp [djbKey])
  have h3 := bytesField_some_length_le (tag := 3) (bs := djbKey m.idPub) (by decide)
    (by simp [djbKey])
  have h4 := bytesField_some_length_le (tag := 4) (bs := m.inner) (by decide) (by omega)
  have h5 := uint32Field_length_le_10 (tag := 5) (by decide) (some m.regId)
  have h6 := uint32Field_length_le_10 (tag := 6) (by decide) (some m.spkId)
  have h7 := uint32Field_length_le_10 (tag := 7) (by decide) (some m.kpkId)
  have h8 := bytesField_some_length_le (tag := 8) (bs := kyberKey m.kyberCt) (by decide)
    (by simp [kyberKey])
  have hdjb1 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hdjb2 : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  omega

/-- Establishes `pqD3ScopedRun`, `OutcomeMatchesModelExceptPath`, `D3NoMatchSessionFile`, and
`CommitOk` at `cliRunSemOverV4 X W` for any `body` with `body.length < 2 ^ 32`,
`pksmParse body = some pm`, `pkToE? pm = some m`, `m.inner.length + 2048 < 2 ^ 32`, and
`¬ PqSessionMatches x g m`. -/
theorem runRel_pqRecv_validOver (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
    (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hbody : body.length < 2 ^ 32)
    (hparse : pksmParse body = some pm)
    (hpk : pkToE? pm = some m)
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: body) rc
    let a := runAns (cliRunSemOverV4 X W) inp
    pqD3ScopedRun WP (runRel (cliRunSemOverV4 X W)) inp a ∧
      (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
         (pqRecvPrekeyModel X WP { st with session := none } m rc)
         (observe inp.files a) ∧
       D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
      CommitOk inp (MainResult.ofAnswer a) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S : RunSem := cliRunSemOverV4 X W
  have hlen : (wirePrekey :: body).length ≤ 2 ^ 32 := Nat.succ_le_of_lt hbody
  have hhs : RunHsOk S (pqRecvInputs WP st (wirePrekey :: body) rc) :=
    runHsOk_pqRecvPrekey_body_f3 (S := S) WP st body rc fun pm' hpm' => by
      change pksmParse body = some pm' at hpm'
      cases Option.some.inj (hpm'.symm.trans hparse)
      exact decPkOkOverV4_pqRecv WP st x g body pm m rc hwf hsess hnomatch hparse hpk hm
  refine ⟨⟨Or.inr ⟨st, wirePrekey :: body, rc, hwf, rfl⟩,
      domainArgv_pqRecv WP st (wirePrekey :: body) rc,
      runBounds_pqRecv WP st (wirePrekey :: body) rc hlen,
      runFilesOk_pqRecv_cli_f3 (S := S) rfl WP st (wirePrekey :: body) rc hwf,
      runEncOk_pqRecv S WP st (wirePrekey :: body) rc,
      hhs, rfl⟩,
    observedExcept_and_noMatchSessionFile_runAns_decPkOverDef (S := S) rfl (fun _ => rfl)
      hwf hsess hparse hpk hnomatch,
    commitOk_pqRecvPrekey_decPkOverDef (S := S) (X := X) (W := WP) (Scope := scopeIn)
      rfl st body rc⟩

/-- Establishes `pqD3ScopedRun`, `OutcomeMatchesModelExceptPath`, `D3NoMatchSessionFile`, and
`CommitOk` at `cliRunSemOverV4 X W` for canonical `m.bytes` with `m.inner.length + 2048 < 2 ^ 32`
and `¬ PqSessionMatches x g m`. -/
theorem runRel_pqRecv_canonicalNoMatch (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (st : PqParty) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st) (hsess : st.session = some (x, g))
    (hm : m.inner.length + 2048 < 2 ^ 32)
    (hnomatch : ¬ PqSessionMatches x g m) :
    let WP : PEParams := ⟨W.C, W.Q⟩
    let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
    let a := runAns (cliRunSemOverV4 X W) inp
    pqD3ScopedRun WP (runRel (cliRunSemOverV4 X W)) inp a ∧
      (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
         (pqRecvPrekeyModel X WP { st with session := none } m rc)
         (observe inp.files a) ∧
       D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
      CommitOk inp (MainResult.ofAnswer a) := by
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  let S : RunSem := cliRunSemOverV4 X W
  have hlen : (wirePrekey :: m.bytes).length ≤ 2 ^ 32 :=
    Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32_local hm)
  have hhs : RunHsOk S (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) :=
    runHsOk_pqRecvPrekey_body_f3 (S := S) WP st m.bytes rc fun pm' hpm' => by
      change pksmParse m.bytes = some pm' at hpm'
      have hb := pksmParse_bytes (argsOf m) hm
      rw [argsOf_bytes] at hb
      have hinner : (argsOf m).inner = m.inner := rfl
      cases hi : SignalMessage.tryFrom protoSignalCodec m.inner with
      | error _ =>
        rw [hb, hinner, hi] at hpm'
        cases hpm'
      | ok inner =>
        have hparse : pksmParse m.bytes = some (pmOfE m inner) := by rw [hb, hinner, hi]; rfl
        cases Option.some.inj (hpm'.symm.trans hparse)
        exact decPkOkOverV4_pqRecv WP st x g m.bytes (pmOfE m inner) m rc hwf hsess hnomatch
          hparse (pkToE?_pmOfE m inner hi) hm
  refine ⟨⟨Or.inr ⟨st, wirePrekey :: m.bytes, rc, hwf, rfl⟩,
      domainArgv_pqRecv WP st (wirePrekey :: m.bytes) rc,
      runBounds_pqRecv WP st (wirePrekey :: m.bytes) rc hlen,
      runFilesOk_pqRecv_cli_f3 (S := S) rfl WP st (wirePrekey :: m.bytes) rc hwf,
      runEncOk_pqRecv S WP st (wirePrekey :: m.bytes) rc,
      hhs, rfl⟩,
    observedExcept_and_noMatchSessionFile_runAns_canonical (S := S) rfl (fun _ => rfl)
      hwf hsess hm hnomatch,
    commitOk_pqRecvPrekey_decPkOverDef (S := S) (X := X) (W := WP) (Scope := scopeIn)
      rfl st m.bytes rc⟩

/-! ## 2. Block-`520` Slot Theorems (`decPkValidOverSlotOk_cli_placedBudget`) -/

/-- Caller-block (`i < 619`) budget-threaded `decPkSlotSpecPlaced` reduction for D3 `validOver`
(`DecPkOkOverV4`) at `lsmpl.base 520` over 2-argument `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliDecryptPrekey_slot_validOver_placedBudget_at_block [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3PlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3PlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hpoll := decPk_d3_validOver_poll_placedBudget hDropNz hP2O hP3O hP4O
    mmpl gh W X B S Scope hTry hevs_sub
  exact dpSlot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hG hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64 hi)

/-- Pointwise `(mkSlot (decPkSlotSpecPlaced ...) needs.decryptPrekey).OkPlaced` wrapper on any
caller block `i < 619`. -/
theorem cliDecryptPrekey_slotOk_validOver_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3PlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3PlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_validOver_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hG hh hRead hDeser hP2O hP3O hP4O hTry hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

/-- Parametric block-`520` slot contract
`(slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced` on
`lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))` for any `S.decPkOk` implying
`DecPkOkOverV4`. -/
theorem decPkValidOverSlotOk_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3PlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3PlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_validOver_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn needs
    h547 hG hh hRead hDeser hP2O hP3O hP4O hTry
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

/-- Concrete CLI specialization of `decPkValidOverSlotOk_placedBudget` at `DecPkD3ValidOverCliEnv`,
discharging Stage P4 (`stageP4Prev1_vregs_placed_inst`), block `507` `tryDecrypt`
(`over_tryDecrypt_cli_placed_ok_at`), Stage P3 (`stageP3_prev1_d3_placed_ok`), and Stage P2
(`decPk_d3_validOver_stage2_placedBudget`). -/
theorem decPkValidOverSlotOk_cli_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3PlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      CliGhostAllocHooks M A lim gh' →
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  exact decPkValidOverSlotOk_placedBudget mmpl gh W X h547 hG hh
    (hEq ▸ hReadAll mmpl gh W cliRunBudgets)
    hDeser
    (decPk_d3_validOver_stage2_placedBudget A lim hPathC hRaw hGrow)
    (stageP3_prev1_d3_placed_ok hLog519)
    (stageP4Prev1_vregs_placed_inst A lim (ReadFileRuleEnv cliIo.rd) h547 hReadAll)
    (over_tryDecrypt_cli_placed_ok_at mmpl gh W 0#64 hG hAesDec hSpqr)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-! ## 3. Block-`579` `runSpecTightPlaced` & Block-`617` `mainSpecTightPlacedAt` Lift -/

/-- Contravariant weakening of `Run` inside `HopsPlacedBudget.runSpecTightPlaced`. -/
theorem subroutine_ok_runSpecTightPlaced_mono_run [LibsignalPlacement]
    {P : Program} {e : BitVec 64} {M : AllocCostModel} {CodeOk : Memory → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RunCall → List AllocEvent → Prop} {uuidParse : UuidParser}
    {Run₁ Run₂ : Inputs → RunAnswer → Prop}
    {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (himp : ∀ i a, Run₁ i a → Run₂ i a)
    (h : subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim Env uuidParse Run₂ wrOk resStack)) :
    subroutine_ok P e
      (runSpecTightPlaced CodeOk A lim Env uuidParse Run₁ wrOk resStack) := by
  refine subroutine_ok_mono h
    (fun ⟨g, st⟩ R s0 hp => ?_)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => he)
    (fun _ _ _ _ ho => ho)
  simp only [runSpecTightPlaced, runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, himp g.i g.a hp.1.2.1, hp.1.2.2⟩, hp.2⟩

/-- Lifts `decPkValidOverSlotOk_cli_placedBudget` onto `mProgPlaced` at `lsmpl.base 579` over
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem hrun_cli_validOver_tight_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3PlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      CliGhostAllocHooks M A lim gh' →
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs) uuidTryParse
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) cliWrOk cliResStack) := by
  have hslot := decPkValidOverSlotOk_cli_placedBudget mmpl gh W X h547 hG hh hReadAll hDeser
    hPathC hRaw hGrow hLog519 hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun := run_ok_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hh (hcFromSlot hslot) hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

/-- Lifts `decPkValidOverSlotOk_cli_placedBudget` onto `SpecsPlacedBudget.mainSpecTightPlacedAt`
(block `617`) over `pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))`. -/
theorem main_ok_cli_validOver_tight_placed_at [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3PlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      CliGhostAllocHooks M A lim gh' →
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfPlaced A lim sEnvs (cliRunSemOverV4 X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalCodeRoLoaded lsmpl) A lim st cliMainStk cliStaticsPlaced
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :=
  hMainLift
    (decPkValidOverSlotOk_cli_placedBudget mmpl gh W X h547 hG hh hReadAll hDeser
      hPathC hRaw hGrow hLog519 hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs needs
      hsEnv rfl rfl (fun _ _ _ _ h => h) hneed)

/-! ## 4. Re-exports from `D3NonCanonValidOverEnvPlacedBudget` -/

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget (
  DecPkD3ValidOverCliEnv
  ValidOverRealSlotEnv
  decPkD3ValidOverEnv_mem_w4RecvPrekeyRealEnv
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_validOver_d3
  mainSt0Dom_init_cliBudgetLimits_validOver_d3
)

/-! ## 5. `LibsignalFrozen` / `[LibsignalFullPlacement]` Variants -/

/-- `ReadEnv`-parametric D3 `validOver` (`DecPkOkOverV4`) `decrypt_prekey` slot allocation envelope
(definitionally equal `rfl` to `DecPkD3ValidOverCliEnv` at `ReadEnv := ReadFileRuleEnv cliIo.rd`,
and directly instantiable at `ReadFileRuleEnvFixed cliIo.rd`). -/
def DecPkD3ValidOverOfReadEnv [LibsignalPlacement]
    (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3ValidOverEnv A W X B
    ReadEnv
    SessDeserializeCancelEnv
    P2OverErrEnv P2OverOkEnv
    (fun W' => TryDecryptCliEnv W'.C (spqrV1 W'.C.F W'.Q.K))
    (fun B' F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1Envs A B' F0 peer pid kpkId spkId kbk ReadEnv)
    g evs

/-- Caller-block (`i < 619`) Frozen (`decPkSlotSpecFrozenPlaced`) reduction for D3 `validOver`
(`DecPkOkOverV4`) at `lsmpl.base 520` under `[LibsignalFullPlacement]`. -/
theorem cliDecryptPrekey_slot_validOver_full_placedBudget_at_block
    [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenPlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hpoll := decPk_d3_validOver_poll_full_placedBudget hDropNz hP2O hP3O hP4O
    mmpl gh W X B S Scope hTry hevs_sub
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hG hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64 hi)

/-- Pointwise `(mkSlot (decPkSlotSpecFrozenPlaced ...) needs.decryptPrekey).OkPlaced` wrapper on
any caller block `i < 619` under `[LibsignalFullPlacement]`. -/
theorem cliDecryptPrekey_slotOk_validOver_full_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenPlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_validOver_full_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hG hh hRead hDeser hP2O hP3O hP4O hTry hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

/-- Parametric frozen block-`520` slot contract
`(slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced` under
`[LibsignalFullPlacement]`. -/
theorem decPkValidOverSlotOk_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenPlacedBudgetStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_validOver_full_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn needs
    h547 hG hh hRead hDeser hP2O hP3O hP4O hTry
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

/-- `ReadEnv`-parametric frozen CLI block-`520` slot theorem discharging Stage P3 via
`stageP3_prev1_d3_full_placed_ok`, Stage P4 via `stageP4Prev1_vregs_placed_inst`, and block `507`
`tryDecrypt` via `over_tryDecrypt_cli_placed_ok_at`. -/
theorem decPkValidOverSlotOk_full_of_readEnv_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  exact decPkValidOverSlotOk_full_placedBudget mmpl gh W X h547 hG hh
    (hEq ▸ hReadAll mmpl gh W cliRunBudgets)
    hDeser
    (decPk_d3_validOver_stage2_full_placedBudget A lim hPathC hRaw hGrow)
    stageP3_prev1_d3_full_placed_ok
    (stageP4Prev1_vregs_placed_inst A lim ReadEnv h547 hReadAll)
    (over_tryDecrypt_cli_placed_ok_at mmpl gh W 0#64 hG hAesDec hSpqr)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Specialization of `decPkValidOverSlotOk_full_of_readEnv_placedBudget` to `ReadFileRuleEnv cliIo.rd`. -/
theorem decPkValidOverSlotOk_cli_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkValidOverSlotOk_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hReadAll hDeser
    hPathC hRaw hGrow hAesDec hSpqr S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Lifts `decPkValidOverSlotOk_full_of_readEnv_placedBudget` onto `mProgPlaced` at
`lsmpl.base 579` over `runSpecTightPlaced (LibsignalFrozen lsmpl) ...`. -/
theorem hrun_cli_validOver_tight_full_of_readEnv_placed
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
        cliWrOk cliResStack) := by
  have hslot := decPkValidOverSlotOk_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hReadAll
    hDeser hPathC hRaw hGrow hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun := run_ok_frozen_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hh (hcFromSlot hslot) hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

/-- Specialization of `hrun_cli_validOver_tight_full_of_readEnv_placed` to `ReadFileRuleEnv cliIo.rd`. -/
theorem hrun_cli_validOver_tight_full_placed [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
        cliWrOk cliResStack) :=
  hrun_cli_validOver_tight_full_of_readEnv_placed A lim mmpl gh W X h547 hG hh hReadAll hDeser
    hPathC hRaw hGrow hAesDec hSpqr hsEnv harms hcFromSlot hpksm

/-- `ReadEnv`-parametric block-`617` frozen `mainSpecTightPlacedAt` corollary for `validOver`. -/
theorem main_ok_cli_validOver_tight_full_of_readEnv_placed_at
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
          cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
        cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :=
  hMainLift
    (decPkValidOverSlotOk_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hReadAll hDeser
      hPathC hRaw hGrow hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs needs
      hsEnv rfl rfl (fun _ _ _ _ h => h) hneed)

/-- Concrete CLI block-`617` frozen `mainSpecTightPlacedAt` corollary for `validOver`. -/
theorem main_ok_cli_validOver_tight_full_placed_at
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadAll : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks)
      (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenPlacedBudgetStmt A lim PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh' (cliExternsPlaced mmpl' W')))
    (hGrow : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_51 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 621)
        (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
          cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
        cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :=
  main_ok_cli_validOver_tight_full_of_readEnv_placed_at A lim st mmpl gh W X h547 hG hh hReadAll
    hDeser hPathC hRaw hGrow hAesDec hSpqr hsEnv hneed hMainLift

/-! ## 6. Pointwise `(X, mmpl, gh, W)` Frozen (`withLsFrozen` / `[LibsignalFullPlacement]`) Twins -/

/-- Pointwise `(X, mmpl, gh, W)` caller-block (`i < 619`) Frozen (`decPkSlotSpecFrozenPlaced`)
reduction for D3 `validOver` (`DecPkOkOverV4`) at `lsmpl.base 520` consuming
`StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt` and `StageP4Prev1VRegsAtPlacedStmt`. -/
theorem cliDecryptPrekey_slot_validOver_at_full_placedBudget_at_block
    [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : dpPollProgPlaced H =
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hpoll := decPk_d3_validOver_poll_at_full_placedBudget hDropNz mmpl gh W X hP2O hP3O hP4O
    B S Scope hTry hevs_sub
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact hpoll hG hh (hEq ▸ hRead) (hEq ▸ hDeser) hinjK hsub hS hok stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64 hi)

/-- Pointwise `(X, mmpl, gh, W)` `(mkSlot (decPkSlotSpecFrozenPlaced ...) needs.decryptPrekey).OkPlaced`
wrapper on any caller block `i < 619` under `[LibsignalFullPlacement]`. -/
theorem cliDecryptPrekey_slotOk_validOver_at_full_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (needs : RunNeeds)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkOverV4 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed B) :
    (mkSlot (decPkSlotSpecFrozenPlaced A lim DecPkEnv S) needs.decryptPrekey).OkPlaced
      prog (lsmpl.base 520) :=
  fun stk h1 h2 =>
    cliDecryptPrekey_slot_validOver_at_full_placedBudget_at_block A lim B mmpl gh W hi X S Scope
      hDropNz hG hh hRead hDeser hP2O hP3O hP4O hTry hinjK hsub hS hok hevs_sub
      stk (hneed ▸ h1) h2

/-- Pointwise `(X, mmpl, gh, W)` parametric frozen block-`520` slot contract
`(slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced`. -/
theorem decPkValidOverSlotOk_at_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3FrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (hTry : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  cliDecryptPrekey_slotOk_validOver_at_full_placedBudget
    (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn needs
    h547 hG hh hRead hDeser hP2O hP3O hP4O hTry
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv hneed

/-- Pointwise `(X, mmpl, gh, W)` `ReadEnv`-parametric frozen CLI block-`520` slot theorem for
`validOver`. -/
theorem decPkValidOverSlotOk_at_full_of_readEnv_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  exact decPkValidOverSlotOk_at_full_placedBudget mmpl gh W X h547 hG hh
    (hEq ▸ hRead cliRunBudgets)
    hDeser
    (decPk_d3_validOver_stage2_at_full_placedBudget A lim X mmpl gh W hPathC hRaw hGrow)
    stageP3_prev1_d3_full_placed_ok
    (fun B F0 peer pid kpkId spkId kbk st_b hh_p4 =>
      stageP4Prev1_placed_inst h547 mmpl gh W B F0 peer pid kpkId spkId kbk hh_p4 (hRead B) st_b)
    (over_tryDecrypt_cli_placed_ok_at mmpl gh W 0#64 hG hAesDec hSpqr)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Specialization of `decPkValidOverSlotOk_at_full_of_readEnv_placedBudget` to `ReadFileRuleEnv cliIo.rd`. -/
theorem decPkValidOverSlotOk_cli_at_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkValidOverSlotOk_at_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hRead hDeser
    hPathC hRaw hGrow hAesDec hSpqr S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- Pointwise `(X, mmpl, gh, W)` `ReadEnv`-parametric block-`579` frozen `runSpecTightPlaced` lift. -/
theorem hrun_cli_validOver_tight_at_full_of_readEnv_placed
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
        cliWrOk cliResStack) := by
  have hslot := decPkValidOverSlotOk_at_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hRead
    hDeser hPathC hRaw hGrow hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun := run_ok_frozen_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hh (hcFromSlot hslot) hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

/-- Pointwise `(X, mmpl, gh, W)` concrete CLI block-`579` frozen `runSpecTightPlaced` lift. -/
theorem hrun_cli_validOver_tight_at_full_placed [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
        cliWrOk cliResStack) :=
  hrun_cli_validOver_tight_at_full_of_readEnv_placed A lim mmpl gh W X h547 hG hh hRead hDeser
    hPathC hRaw hGrow hAesDec hSpqr hsEnv harms hcFromSlot hpksm

/-- Pointwise `(X, mmpl, gh, W)` `ReadEnv`-parametric block-`617` frozen `mainSpecTightPlacedAt` corollary. -/
theorem main_ok_cli_validOver_tight_at_full_of_readEnv_placed_at
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
          cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
        cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :=
  hMainLift
    (decPkValidOverSlotOk_at_full_of_readEnv_placedBudget mmpl gh W X h547 hG hh hRead hDeser
      hPathC hRaw hGrow hAesDec hSpqr (cliRunSemOverV4 X W) sEnvs needs
      hsEnv rfl rfl (fun _ _ _ _ h => h) hneed)

/-- Pointwise `(X, mmpl, gh, W)` concrete CLI block-`617` frozen `mainSpecTightPlacedAt` corollary. -/
theorem main_ok_cli_validOver_tight_at_full_placed_at
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile (ReadFileRuleEnv cliIo.rd)))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverCliEnv A.repAlloc W X cliRunBudgets P2OverErrEnv P2OverOkEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hMainLift :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
        (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
          cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 617)
      (mainSpecTightPlacedAt (LibsignalFrozen lsmpl) A lim st cliMainStk
        cliStaticsPlaced (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :=
  main_ok_cli_validOver_tight_at_full_of_readEnv_placed_at A lim st mmpl gh W X h547 hG hh hRead
    hDeser hPathC hRaw hGrow hAesDec hSpqr hsEnv hneed hMainLift

/-- `SpqrV1PlacedSeamsOfEnv` variant of `decPkValidOverSlotOk_at_full_of_readEnv_placedBudget`. -/
theorem decPkValidOverSlotOk_at_full_of_readEnv_ofEnv_placedBudget
    [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr :
      LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.SpqrV1PlacedSeamsOfEnv
        M A lim mmpl gh W InitEnv (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget.TryDecryptCliEnvOf
        W.C (spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv RecvBytesEnv
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv a evs →
      tdEnv W a evs)
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv SessDeserializeCancelEnv
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B' F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1Envs A.repAlloc B' F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkOverDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkOverV4 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [dpPollProgPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced, stageP1ProgPlaced]
    rw [hpan]
  exact decPkValidOverSlotOk_at_full_placedBudget mmpl gh W X h547 hG hh
    (hEq ▸ hRead cliRunBudgets)
    hDeser
    (decPk_d3_validOver_stage2_at_full_placedBudget A lim X mmpl gh W hPathC hRaw hGrow)
    stageP3_prev1_d3_full_placed_ok
    (fun B F0 peer pid kpkId spkId kbk st_b hh_p4 =>
      stageP4Prev1_placed_inst h547 mmpl gh W B F0 peer pid kpkId spkId kbk hh_p4 (hRead B) st_b)
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue.over_tryDecrypt_cli_of_tdEnv_placed_ok_at
      mmpl gh W 0#64 hG hAesDec hSpqr hRecv_ne htd)
    S sEnvs needs hsEnv hfiles hdecPk hdecPkOk hneed

/-- `SpqrV1PlacedSeamsOfEnv` variant of `hrun_cli_validOver_tight_at_full_of_readEnv_placed`. -/
theorem hrun_cli_validOver_tight_at_full_of_readEnv_ofEnv_placed
    [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitEnv : CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CryptoVerification.LibsignalTripleRatchet.SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr :
      LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.SpqrV1PlacedSeamsOfEnv
        M A lim mmpl gh W InitEnv (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget.TryDecryptCliEnvOf
        W.C (spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv RecvBytesEnv
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv SessDeserializeCancelEnv
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B' F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1Envs A.repAlloc B' F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      sEnvs.decryptPrekey g evs)
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) cliResStack)
    (hcFromSlot :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) →
      RunCalleesPlaced A lim cEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets
        (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))))
    (hpksm : subroutine_ok (runProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom (cliRunSemOverV4 X W))) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))
        cliWrOk cliResStack) := by
  have hslot := decPkValidOverSlotOk_at_full_of_readEnv_ofEnv_placedBudget mmpl gh W X h547 hG hh
    hRead hDeser hPathC hRaw hGrow hAesDec hSpqr hRecv_ne htd (cliRunSemOverV4 X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl
  have hrun := run_ok_frozen_placed_at_block
    (callerProg := mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 617)
    harms hh (hcFromSlot hslot) hpksm
    (runNeed_cli_le_resStack_placed A lim sEnvs (by decide)) (by decide) (by decide)
  exact subroutine_ok_runSpecTightPlaced_mono_run (fun _ _ hr => hr.2) hrun

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
