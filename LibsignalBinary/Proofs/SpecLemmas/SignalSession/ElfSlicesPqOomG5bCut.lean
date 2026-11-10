/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib.Hoare.SubroutineOk

/-!
# Outer Block-`579` Composition for D3 Untyped `recv`

**Checked by Lean.**

Assembles `runSpecTightPlaced (LibsignalFrozen lsmpl)` on Block `579` for `cliRunSemD3 W` with
`DecPkD3UntypedEnvOf` and `PksmTryFromEnv`:
- `g5ba_encSlotSpecPlaced_d2c_eq_d3` and `g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3` transport
  outer `mkSlot` `OkPlaced` contracts from `cliRunSemD2c_placed X W` to `cliRunSemD3 W` without
  unfolding `EncEnv` or `DecSigEnv`.
- `g5b_hrun_of_slotEnvs_of_pub`, `g5b_hrun_of_slots`, and `g5b_hrun_of_slots_gen` compose the
  Block-`579` contract over `ElfSlicesPqOomG5bPub`.
- `g5ba_cliDecryptSignalSlotEnv_stateGuarded_eq_of_peerTight640` and
  `g5b_hrun_of_slots_ofSendDecSigGuarded*` lift `TopStateTight`-guarded inner `decryptSignal`
  contracts to the `PeerSpqrStateTight640`-guarded outer slot.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost mkSlot runRel unixEpoch)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (encodeInjOn_deserializeScopeP_Q loadRec scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
   realCliInitBinarySlotEnvFixed
   w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (PksmSlotOkPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliInitSlotOkPlaced CliPubCalleesFrozenPlaced CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunEnv run_ok_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf
   encSlotSpecPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
  (subsetA4PksmTryFromPlaced_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (cliPksmTryFrom_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slotOk_full_placed decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
  (W1InnerPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
  (cliEncrypt_slotOk_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
  (hc_kemDeserialize_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
  (g5bp_binaryKitRunSlotEnvsOfSend g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded
   g5bp_cliPubCallees_exact_frozen_ok g5bp_cliPubCallees_of_sendEnv_decSigGuarded_frozen_ok
   g5bp_cliPubCallees_of_sendEnv_frozen_ok g5bp_slotEnvsOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_w1_inner hole3_w2_inner hole3_w3_init libsignalFullPlacementOf)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-! ## `sendEnv`-Parametric `RunSlotEnvs` Bundles and `RunSem` Transport -/

/-- `sendEnv`-parametric binary-kit `RunSlotEnvs` bundle (`encrypt` at `sendEnv`,
`decryptSignal` at `W2RealTdEnv W.C.F W.Q.K`). -/
noncomputable abbrev g5ba_binaryKitRunSlotEnvsOf [LibsignalPlacement] {M : AllocCostModel}
    (sendEnv : SpqrSendBudgetEnv)
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  g5bp_binaryKitRunSlotEnvsOfSend W A B sendEnv InitEnv DecPkEnv

/-- `sendEnv`- and `maxOps`-parametric binary-kit `RunSlotEnvs` bundle (`encrypt` unguarded at
`sendEnv`, `decryptSignal` guarded by `PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val` at
`TryDecryptCliLinkedEnvOf maxOps W.C W.Q.K`). -/
noncomputable abbrev g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded [LibsignalPlacement]
    {M : AllocCostModel}
    (sendEnv : SpqrSendBudgetEnv) (maxOps : Nat := 109)
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  g5bp_binaryKitRunSlotEnvsOfSendDecSigGuarded W A B sendEnv maxOps InitEnv DecPkEnv

private theorem g5ba_runProofs_encDef_eq_agree (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    CryptoVerification.SignalSession.Cli.RunProofs.encDef P Scope =
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.cliFinal F calls =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliFinal
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.cliStep F =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer
        (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer) =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer) := by
    intro F peer
    have hKey :
        CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer := by
      unfold CryptoVerification.SignalSession.Cli.RunProofs.encKey
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey
      rcases loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer with _ | _ <;>
      rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.encDef
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef
  rw [hAns F peer]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
      (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer))
    ptext peer me unixEpoch coins = rc
  rcases rc with ⟨err | _, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

/-- `encSlotSpecPlaced` agrees across `cliRunSemD2c_placed X W` and `cliRunSemD3 W` for any
`EncEnv` without unfolding `EncEnv`. -/
theorem g5ba_encSlotSpecPlaced_d2c_eq_d3 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W) =
      encSlotSpecPlaced A lim EncEnv (cliRunSemD3 W) := by
  funext stk
  have henc : (cliRunSemD2c_placed X W).encrypt = (cliRunSemD3 W).encrypt :=
    g5ba_runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn
  have hfiles : (cliRunSemD2c_placed X W).filesOk = (cliRunSemD3 W).filesOk := rfl
  have hencOk : (cliRunSemD2c_placed X W).encOk = (cliRunSemD3 W).encOk := rfl
  unfold encSlotSpecPlaced
  rw [hfiles, hencOk, henc]

/-- `decSigSlotSpecFrozenPlaced` agrees across `cliRunSemD2c_placed X W` and `cliRunSemD3 W`
for any `DecSigEnv` without unfolding `DecSigEnv`. -/
theorem g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W) =
      decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD3 W) := by
  funext stk
  have hdec : (cliRunSemD2c_placed X W).decryptSignal = (cliRunSemD3 W).decryptSignal :=
    (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
  have hfiles : (cliRunSemD2c_placed X W).filesOk = (cliRunSemD3 W).filesOk := rfl
  unfold decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf decSigSlotSpecBasePlaced
  rw [hfiles, hdec]

/-! ## Block-`111` `PksmSlotOkPlacedAt` at `PksmTryFromEnv` -/

/-- Block-`111` `PreKeySignalMessage::try_from` slot witness at `PksmTryFromEnv`. -/
theorem g5ba_pksmSlotOk_tryFrom [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    PksmSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) A lim PksmTryFromEnv :=
  fun _ hS =>
    cliPksmTryFrom_placed_at_block
      (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      (subsetA4PksmTryFromPlaced_cli mmpl gh W hG)
      (fun b => congrFun hS b)

/-! ## Outer Block-`579` Assemblers -/

/-- Slot-body-parametric outer Block-`579` `runSpecTightPlaced (LibsignalFrozen lsmpl)`
composition for `cliRunSemD3 W` over arbitrary `EncEnv` and `DecSigEnv`. -/
theorem g5b_hrun_of_slotEnvs_of_pub [LibsignalFullPlacement]
    (EncEnv : EncGhost → List AllocEvent → Prop)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hpub : CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (g5bp_slotEnvsOf EncEnv DecSigEnv
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (g5bp_slotEnvsOf EncEnv DecSigEnv
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        PksmTryFromEnv)
      W)
    (hW1Slot : (mkSlot
      (encSlotSpecPlaced A lim EncEnv (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hW2Slot : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim DecSigEnv (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W)
      defaultExtrasF3 W)
    (hSlot520 :
      (slotsOfSigPkFrozenPlaced A lim
        (g5bp_slotEnvsOf EncEnv DecSigEnv
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (g5bp_slotEnvsOf EncEnv DecSigEnv
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv
          (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let S := cliRunSemD3 W
  let DecPkEnv := DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
    (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv
  let sEnvs := g5bp_slotEnvsOf EncEnv DecSigEnv (realCliInitBinarySlotEnvFixed W) DecPkEnv
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed)
  have hh := hHooks.runHooks
  have hW1 : (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).encrypt.OkPlaced
      (lsProg_579 H) (lsmpl.base 464) := by
    change (mkSlot (encSlotSpecPlaced A lim EncEnv S)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 H) (lsmpl.base 464)
    rw [← g5ba_encSlotSpecPlaced_d2c_eq_d3 A lim EncEnv X W]
    exact hW1Slot
  have hW2 : (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptSignal.OkPlaced
      (lsProg_579 H) (lsmpl.base 463) := by
    change (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv S)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 H) (lsmpl.base 463)
    rw [← g5ba_decSigSlotSpecFrozenPlaced_d2c_eq_d3 A lim DecSigEnv X W]
    exact hW2Slot
  have hcallees : RunCalleesPlaced A lim (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      H cliRunBudgets (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := hW1
      decryptSignal := hW2
      initiate := hInit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hSlot520
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S (cliDecryptPrekeyNeed cliRunBudgets_placed))
      hh
      hcallees
      (g5ba_pksmSlotOk_tryFrom mmpl gh W hG S rfl)
      (runNeed_cli_le_resStack_placed A lim sEnvs
        (S := S) (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets_placed) (by decide))
      (by decide)
      (by decide)

/-- Outer Block-`579` composition over `binaryKitRunSlotEnvsExact`, `PksmTryFromEnv`,
`DecPkD3UntypedEnvOf`, and `cliRunSemD3 W`. -/
theorem g5b_hrun_of_slots [LibsignalFullPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Inner : (mkSlot
      (encSlotSpecPlaced A lim (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed defaultExtrasF3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hW2Inner : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed defaultExtrasF3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W)
      defaultExtrasF3 W)
    (hSlot520 :
      (slotsOfSigPkFrozenPlaced A lim
        (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv
          (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) :=
  g5b_hrun_of_slotEnvs_of_pub
    (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
    (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
    mmpl gh defaultExtrasF3 W hG hHooks
    (g5bp_cliPubCallees_exact_frozen_ok mmpl gh W hHooks)
    hW1Inner hW2Inner hInit hSlot520

/-- `sendEnv`-parametric outer Block-`579` assembler from inner `W1InnerPlacedOk` and
`InnerDecryptFrozenPlacedOk` contracts. -/
theorem g5b_hrun_of_slots_gen [LibsignalFullPlacement]
    (sendEnv : SpqrSendBudgetEnv)
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Inner : W1InnerPlacedOk mmpl gh W A lim cliRunBudgets_placed scopeIn
      sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed))
    (hW2Inner : InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
      (W2RealTdEnv W.C.F W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W)
      defaultExtrasF3 W)
    (hSlot520 :
      (slotsOfSigPkFrozenPlaced A lim
        (g5ba_binaryKitRunSlotEnvsOf sendEnv W A cliRunBudgets_placed
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (g5ba_binaryKitRunSlotEnvsOf sendEnv W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv
          (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) := by
  let S2c := cliRunSemD2c_placed defaultExtrasF3 W
  let DecPkEnv := DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
    (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv
  let sEnvs := g5ba_binaryKitRunSlotEnvsOf sendEnv W A cliRunBudgets_placed
    (realCliInitBinarySlotEnvFixed W) DecPkEnv
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hh := hHooks.runHooks
  exact g5b_hrun_of_slotEnvs_of_pub
    sEnvs.encrypt sEnvs.decryptSignal mmpl gh defaultExtrasF3 W hG hHooks
    (g5bp_cliPubCallees_of_sendEnv_frozen_ok mmpl gh W sendEnv hHooks)
    (cliEncrypt_slotOk_placed mmpl gh W A lim cliRunBudgets S2c scopeIn sEnvs needs
      sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hh hW1Inner encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
      (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl rfl)
    (cliDecryptSignal_slotOk_full_placed mmpl gh W A lim cliRunBudgets S2c scopeIn sEnvs needs
      (W2RealTdEnv W.C.F W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hh
      (fun F0 peer => w2SessVt_placed_ok A.repAlloc cliRunBudgets h547 F0 peer)
      (fun F0 peer => w2IdVt_placed_ok A.repAlloc cliRunBudgets h547 F0 peer)
      hW2Inner encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl rfl)
    hInit hSlot520

/-! ## Concrete `cliElfBytes` Instantiation -/

/-- Concrete `cliElfBytes` instantiation of `g5b_hrun_of_slots`. -/
theorem g5ba_hole_g5b_hrun_untyped_binaryKit
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSlot520At :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits
        (binaryKitRunSlotEnvsExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf
            (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
            cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
            SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced
        (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
         RunEnv
           (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
             (binaryKitRunSlotEnvsExact W
               (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
               cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
               (DecPkD3UntypedEnvOf
                 (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
                 cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
                 SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
             PksmTryFromEnv (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  exact g5b_hrun_of_slots mmpl ghFixed W h547 hGSpqr.toCliGhostAllocHooks hHooks
    (hole3_w1_inner hLs hblk hext_nodup ghFixed hPl_mng defaultExtrasF3 W γ tp hGSpqr hFs hsat
      hHooks h547)
    (hole3_w2_inner hLs hblk hext_nodup ghFixed hPl_mng defaultExtrasF3 W γ tp hGSpqr hFs hsat
      hHooks h547)
    (hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng defaultExtrasF3 W γ tp hGSpqr hFs hsat
      hghNoAlloc hHooks h547)
    hSlot520At

/-! ## Recv State-Guard Tie and Guarded `decryptSignal` Assemblers -/

private theorem g5ba_ite_congr {α : Sort _} {c₁ c₂ : Prop} [d₁ : Decidable c₁] [d₂ : Decidable c₂]
    {a₁ a₂ b₁ b₂ : α} (hc : c₁ ↔ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (@ite α c₁ d₁ a₁ b₁) = (@ite α c₂ d₂ a₂ b₂) := by
  cases d₁ with
  | isFalse h1 =>
    cases d₂ with
    | isFalse _ => exact hb
    | isTrue h2 => exact False.elim (h1 (hc.mpr h2))
  | isTrue h1 =>
    cases d₂ with
    | isFalse h2 => exact False.elim (h2 (hc.mp h1))
    | isTrue _ => exact ha

private theorem g5ba_fromSessionState_pqrState
    {s s' : CryptoGames.LibsignalSession.SessionState (List (BitVec 8))}
    {tr : CryptoGames.LibsignalSession.TripleRatchet (List (BitVec 8))}
    (h : CryptoGames.LibsignalSession.Mut.exec
      CryptoGames.LibsignalSession.TripleRatchet.fromSessionState s = (.ok tr, s')) :
    tr.pqrState = s.pqRatchetState :=
  (CryptoVerification.LibsignalTripleRatchet.Decrypt.Model.fromSessionState_ok_inv h).2.2.1

/-- Under `TopStateTight F K a.st.pqRatchetState`, guarding `RecvBytesEnv` by `TopStateTight F K`
inside `TryDecryptCliEnvOfPure` equals the unguarded `RecvBytesEnv`. -/
theorem g5ba_tryDecryptCliEnvOfPure_stateGuarded_eq
    (C : CryptoGames.LibsignalSession.Crypto)
    (F : CryptoGames.LibsignalSession.ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (S : CryptoVerification.LibsignalTripleRatchet.SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.TryDecryptEnvArgs)
    (hTight : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
      F K a.st.pqRatchetState) :
    LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
        C S fmtWriteEnv
        (fun stBs msgBs evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K stBs →
            RecvBytesEnv stBs msgBs evs)
        fmtEnv a =
      LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
        C S fmtWriteEnv RecvBytesEnv fmtEnv a := by
  let GuardedRecv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
    fun stBs msgBs evs =>
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K stBs →
        RecvBytesEnv stBs msgBs evs
  have hpq : ∀ x (tr : CryptoGames.LibsignalSession.TripleRatchet (List (BitVec 8))),
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K tr.pqrState →
      LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
          S GuardedRecv fmtEnv x tr =
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
          S RecvBytesEnv fmtEnv x tr := by
    intro x tr htr
    have hrec : GuardedRecv tr.pqrState x.msg.pqRatchet = RecvBytesEnv tr.pqrState x.msg.pqRatchet := by
      funext evs
      exact propext ⟨fun h => h htr, fun h _ => h⟩
    unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
    rw [hrec]
  have hs5 : ∀ x trG (tr : CryptoGames.LibsignalSession.TripleRatchet (List (BitVec 8))) st1 mkg,
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K tr.pqrState →
      LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S GuardedRecv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 mkg =
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S RecvBytesEnv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 mkg := by
    intro x trG tr st1 mkg htr
    unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv
    rw [hpq x tr htr]
  have hs4 : ∀ x trG (tr : CryptoGames.LibsignalSession.TripleRatchet (List (BitVec 8))) st1 ck,
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K tr.pqrState →
      LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S GuardedRecv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 ck =
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S RecvBytesEnv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 ck := by
    intro x trG tr st1 ck htr
    unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv
    rcases CryptoGames.LibsignalSession.Mut.exec
        (CryptoGames.LibsignalSession.RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
          x.msg.counter x.msgType) tr.ratchet with ⟨_ | mkg, r2⟩
    · rfl
    · dsimp only
      rw [hs5 x trG { tr with ratchet := r2 } st1 mkg htr]
  have hs3 : ∀ x trG (tr : CryptoGames.LibsignalSession.TripleRatchet (List (BitVec 8))) st1,
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight F K tr.pqrState →
      LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S GuardedRecv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 =
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv C uuidTryParse S
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt C)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv C)
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env fmtWriteEnv)
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
            S RecvBytesEnv fmtEnv)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
          (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget.s7Env C.F uuidTryParse)
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
          LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
          x trG tr st1 := by
    intro x trG tr st1 htr
    unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv
    rcases CryptoGames.LibsignalSession.Mut.exec
        (CryptoGames.LibsignalSession.RatchetState.dhRatchetStep C x.msg.senderRatchetKey
          (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf x.rest)) tr.ratchet with ⟨_ | ck, r1⟩
    · rfl
    · dsimp only
      rw [hs4 x (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.s3AfterTrGhost trG
        tr.ratchet.receiverChains.length) { tr with ratchet := r1 } st1 ck htr]
  unfold LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
  rcases hex : CryptoGames.LibsignalSession.Mut.exec
      CryptoGames.LibsignalSession.TripleRatchet.fromSessionState a.st with ⟨_ | tr0, st1⟩
  · rfl
  · dsimp only
    have htr0 : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
        F K tr0.pqrState := by
      rw [g5ba_fromSessionState_pqrState hex]
      exact hTight
    unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS2GenEnv
    rcases tr0.ratchet.findReceiverChainKey
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptEnvArgsToGhost a).msg.senderRatchetKey
      with _ | (_ | ck)
    · rfl
    · dsimp only
      rw [hs3 _ _ tr0 st1 htr0]
    · dsimp only
      rw [hs4 _ _ tr0 st1 ck htr0]

/-- Under `PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`, every session loaded via
`decSessKitPlaced.ScopeAt` inside `CliDecryptSignalSlotEnv` satisfies
`TopStateTight W.C.F W.Q.K ses.state.pqRatchetState`, equating the `TopStateTight`-guarded and
unguarded `TryDecryptCliEnvOfPure` slot envelopes at `x`. -/
theorem g5ba_cliDecryptSignalSlotEnv_stateGuarded_eq_of_peerTight640 [LibsignalPlacement]
    {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer,
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decSessKitPlaced
          A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decIdKitPlaced
          A.repAlloc F0 peer B))
    (x : DecSigGhost)
    (hPeer : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
      W.C.F W.Q.K x.F x.peer.val) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
        ⟨W.C, W.Q⟩ A B
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
          W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
          (fun stBs msgBs evs =>
            LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
                W.C.F W.Q.K stBs →
              RecvBytesEnv stBs msgBs evs)
          fmtEnv)
        kitEnv ikitEnv x =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
        ⟨W.C, W.Q⟩ A B
        (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
          W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
          RecvBytesEnv fmtEnv)
        kitEnv ikitEnv x := by
  let tdGuarded := LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
    W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
    (fun stBs msgBs evs =>
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight W.C.F W.Q.K stBs →
        RecvBytesEnv stBs msgBs evs)
    fmtEnv
  let tdBase := LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
    W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv RecvBytesEnv fmtEnv
  let z := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x
  have hzRem : z.rem.val = x.peer.val := rfl
  have hrd : ∀ G ses_st,
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
          W.C.F W.Q.K ses_st.pqRatchetState →
      LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv tdGuarded
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z 0#64 G ses_st) =
        LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv tdBase
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z 0#64 G ses_st) := by
    intro G ses_st hTight
    funext evs
    unfold LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv
      LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.FromVEnv
    refine g5ba_ite_congr Iff.rfl ?_ rfl
    refine congrArg Exists (funext fun G₁ => ?_)
    have htd : tdGuarded
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z 0#64 G ses_st) G₁) =
      tdBase
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z 0#64 G ses_st) G₁) :=
      g5ba_tryDecryptCliEnvOfPure_stateGuarded_eq W.C W.C.F W.Q.K
        (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        fmtWriteEnv RecvBytesEnv fmtEnv _ hTight
    rw [htd]
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
    LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.WithStoresDecEnv
    LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.FromLoadPolledEnv
  refine congrArg
    (LibsignalBinary.Heap.SeqEnv
      (LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.LoadPollStepEnv _ _ _ _))
    (congrArg
      (LibsignalBinary.Heap.SeqEnv _)
      (funext fun evs => ?_))
  refine congrArg (Or _) (congrArg (Or _) (congrArg (Or _)
    (congrArg Exists (funext fun rec =>
      congrArg Exists (funext fun ses =>
        congrArg Exists (funext fun G => ?_))))))
  refine propext ⟨fun ⟨hScAt, hCur, hG, hFrom⟩ => ⟨hScAt, hCur, hG, ?_⟩,
    fun ⟨hScAt, hCur, hG, hFrom⟩ => ⟨hScAt, hCur, hG, ?_⟩⟩
  · have hScAt0 : (CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec
        A.repAlloc 0#64 cliIo.rd x.F cliWrOk
        CryptoVerification.SignalSession.Cli.Slots.scopeKit x.peer 0 0 0 0).ScopeAt
        CryptoVerification.SignalSession.Cli.Slots.scopeKit
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions z.rem.val rec :=
      hScAt
    have hRecTight : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.RecordSpqrStateTight640
        W.C.F W.Q.K rec :=
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
        hScAt0 (hzRem.symm ▸ hPeer)
    have hSesTight := hRecTight ses hCur
    unfold LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.FromRegionSomeEnv at hFrom ⊢
    rw [← hrd G ses.state hSesTight]
    exact hFrom
  · have hScAt0 : (CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec
        A.repAlloc 0#64 cliIo.rd x.F cliWrOk
        CryptoVerification.SignalSession.Cli.Slots.scopeKit x.peer 0 0 0 0).ScopeAt
        CryptoVerification.SignalSession.Cli.Slots.scopeKit
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions z.rem.val rec :=
      hScAt
    have hRecTight : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.RecordSpqrStateTight640
        W.C.F W.Q.K rec :=
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
        hScAt0 (hzRem.symm ▸ hPeer)
    have hSesTight := hRecTight ses hCur
    unfold LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.FromRegionSomeEnv at hFrom ⊢
    rw [hrd G ses.state hSesTight]
    exact hFrom

/-- Lifts an outer `mkSlot` `OkPlaced` witness for `decryptSignal` at a `TopStateTight`-guarded
`TryDecryptCliEnvOfPure` to the `PeerSpqrStateTight640`-guarded `decryptSignal` slot contract
(discharging the false-guard case via `FitsEnv` unsatisfiability at `MallocngMaxAllocSize + 1`). -/
theorem g5ba_decSigSlotOk_decSigGuarded_of_stateGuardedSlot [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Arm64.Program} {S : CryptoVerification.SignalSession.Cli.RunCompose.RunSem}
    {need : Nat}
    (W : CliHooks) (B : RunBudgets)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer,
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decSessKitPlaced
          A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decIdKitPlaced
          A.repAlloc F0 peer B))
    (hSlot : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
          ⟨W.C, W.Q⟩ A B
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
            W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
            (fun stBs msgBs evs =>
              LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
                  W.C.F W.Q.K stBs →
                RecvBytesEnv stBs msgBs evs)
            fmtEnv)
          kitEnv ikitEnv)
        S)
      need).OkPlaced callerProg (lsmpl.base 463)) :
    (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (fun x evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
              W.C.F W.Q.K x.F x.peer.val →
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
              ⟨W.C, W.Q⟩ A B
              (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
                W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
                RecvBytesEnv fmtEnv)
              kitEnv ikitEnv x evs)
        S)
      need).OkPlaced callerProg (lsmpl.base 463) := by
  let StateGuardedEnv : DecSigGhost → List AllocEvent → Prop :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
      ⟨W.C, W.Q⟩ A B
      (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
        W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
        (fun stBs msgBs evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight W.C.F W.Q.K stBs →
            RecvBytesEnv stBs msgBs evs)
        fmtEnv)
      kitEnv ikitEnv
  let PeerGuardedEnv : DecSigGhost → List AllocEvent → Prop :=
    fun x evs =>
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
          W.C.F W.Q.K x.F x.peer.val →
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
          ⟨W.C, W.Q⟩ A B
          (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
            W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
            RecvBytesEnv fmtEnv)
          kitEnv ikitEnv x evs
  intro stk hneed hstk64
  have hCallee := hSlot stk hneed hstk64
  refine Arm64.subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _hL => ?_
  by_cases hPeer :
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K x.F x.peer.val
  · have hEnvEq : PeerGuardedEnv x = StateGuardedEnv x := by
      have h1 : PeerGuardedEnv x =
          LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
            ⟨W.C, W.Q⟩ A B
            (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
              W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) fmtWriteEnv
              RecvBytesEnv fmtEnv)
            kitEnv ikitEnv x := by
        funext evs
        exact propext ⟨fun h => h hPeer, fun h _ => h⟩
      exact h1.trans
        (g5ba_cliDecryptSignalSlotEnv_stateGuarded_eq_of_peerTight640
          W A B fmtWriteEnv RecvBytesEnv fmtEnv kitEnv ikitEnv x hPeer).symm
    have hPreEq :
        (decSigSlotSpecFrozenPlaced A lim PeerGuardedEnv S stk).pre (x, st) =
          (decSigSlotSpecFrozenPlaced A lim StateGuardedEnv S stk).pre (x, st) := by
      funext s
      unfold decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf
        CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk decSigSlotSpecBasePlaced
      dsimp only
      rw [hEnvEq]
    have hPostEq :
        (decSigSlotSpecFrozenPlaced A lim PeerGuardedEnv S stk).post (x, st) =
          (decSigSlotSpecFrozenPlaced A lim StateGuardedEnv S stk).post (x, st) := by
      funext s0' sf
      unfold decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf
        CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk decSigSlotSpecBasePlaced
      dsimp only
      rw [hEnvEq]
    dsimp only [mkSlot] at hCallee hpre ⊢
    exact hCallee.mono_outcome (x, st) R s0 hpc hrun (hPreEq ▸ hpre) hsp fun sf hout => by
      rcases hout with ⟨hret, hcc, hq⟩ | hrest
      · exact Or.inl ⟨hret, hcc, hPostEq ▸ hq⟩
      · exact Or.inr hrest
  · dsimp only [mkSlot, decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf,
      CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk, decSigSlotSpecBasePlaced] at hpre
    simp only [ProofLib.sepConj_assoc, ProofLib.satisfies_pure_sepConj] at hpre
    have hfit : LibsignalBinary.Heap.FitsEnv M lim st (PeerGuardedEnv x) :=
      hpre.1.2.2.2.2.2.2.2.2.2.2.2
    have hev : LibsignalBinary.Heap.FitsEvents M lim st
        [.alloc (VerifiedLibraries.Mallocng.MallocngMaxAllocSize + 1)] :=
      hfit [.alloc (VerifiedLibraries.Mallocng.MallocngMaxAllocSize + 1)]
        (fun hp => False.elim (hPeer hp))
    exact False.elim (Nat.not_succ_le_self _ hev.1.1)

/-- Lifts `InnerDecryptFrozenPlacedOk` at `TopStateTight`-guarded
`SpqrRecvC07C09aBytesEnvOf maxOps` to the `PeerSpqrStateTight640`-guarded
`TryDecryptCliLinkedEnvOf maxOps` `mkSlot` `OkPlaced` contract. -/
theorem g5ba_decSigSlotOk_decSigGuarded_of_stateGuardedInner [LibsignalFullPlacement]
    (maxOps : Nat)
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hW2Inner : InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
      (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
        W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
        (fun stBs msgBs evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
              W.C.F W.Q.K stBs →
            LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
              maxOps W.C.F W.Q.K stBs msgBs evs)
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)) :
    (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (fun x evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
              W.C.F W.Q.K x.F x.peer.val →
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
              ⟨W.C, W.Q⟩ A cliRunBudgets
              (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
                maxOps W.C W.Q.K)
              (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
              (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x evs)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) := by
  let S2c := cliRunSemD2c_placed X W
  let tdStateGuarded :=
    LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
      W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
      LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
      (fun stBs msgBs evs =>
        LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
            W.C.F W.Q.K stBs →
          LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
            maxOps W.C.F W.Q.K stBs msgBs evs)
      LibsignalBinary.Heap.SpecBudget.FormatInnerEnv
  let sEnvsTmp := g5bp_slotEnvsOf
    (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
      ⟨W.C, W.Q⟩ A cliRunBudgets tdStateGuarded
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
    (realCliInitBinarySlotEnvFixed W)
    (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)
  have hStateSlot : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim sEnvsTmp.decryptSignal S2c)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463) :=
    cliDecryptSignal_slotOk_full_placed mmpl gh W A lim cliRunBudgets S2c scopeIn sEnvsTmp
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))
      tdStateGuarded
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hh
      (fun F0 peer => w2SessVt_placed_ok A.repAlloc cliRunBudgets h547 F0 peer)
      (fun F0 peer => w2IdVt_placed_ok A.repAlloc cliRunBudgets h547 F0 peer)
      hW2Inner encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩) rfl rfl
  exact g5ba_decSigSlotOk_decSigGuarded_of_stateGuardedSlot W cliRunBudgets
    LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
    (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
      maxOps W.C.F W.Q.K)
    LibsignalBinary.Heap.SpecBudget.FormatInnerEnv
    (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
    (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
    hStateSlot

/-- Outer Block-`579` assembler over `g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps`. -/
theorem g5b_hrun_of_slots_ofSendDecSigGuarded [LibsignalFullPlacement]
    (sendEnv : SpqrSendBudgetEnv) (maxOps : Nat := 109)
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Slot : (mkSlot
      (encSlotSpecPlaced A lim
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget.CliEncryptSlotEnv
          ⟨W.C, W.Q⟩ A cliRunBudgets sendEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
        (cliRunSemD2c_placed defaultExtrasF3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hW2Slot : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (fun x evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
              W.C.F W.Q.K x.F x.peer.val →
            LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget.CliDecryptSignalSlotEnv
              ⟨W.C, W.Q⟩ A cliRunBudgets
              (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
                maxOps W.C W.Q.K)
              (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
              (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x evs)
        (cliRunSemD2c_placed defaultExtrasF3 W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W)
      defaultExtrasF3 W)
    (hSlot520 :
      (slotsOfSigPkFrozenPlaced A lim
        (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets_placed
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv
          (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) :=
  g5b_hrun_of_slotEnvs_of_pub
    (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets
      (realCliInitBinarySlotEnvFixed W)
      (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)).encrypt
    (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets
      (realCliInitBinarySlotEnvFixed W)
      (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv)).decryptSignal
    mmpl gh defaultExtrasF3 W hG hHooks
    (g5bp_cliPubCallees_of_sendEnv_decSigGuarded_frozen_ok mmpl gh W sendEnv maxOps hHooks)
    hW1Slot hW2Slot hInit hSlot520

/-- Inner-to-outer Block-`579` assembler from `W1InnerPlacedOk` at `sendEnv` and a
`TopStateTight`-guarded `InnerDecryptFrozenPlacedOk` at `SpqrRecvC07C09aBytesEnvOf maxOps`. -/
theorem g5b_hrun_of_slots_ofSendDecSigGuarded_gen [LibsignalFullPlacement]
    (sendEnv : SpqrSendBudgetEnv) (maxOps : Nat := 109)
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (W : CliHooks)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Inner : W1InnerPlacedOk mmpl gh W A lim cliRunBudgets_placed scopeIn
      sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed))
    (hW2Inner : InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ A lim
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed
      (LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure
        W.C (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
        LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
        (fun stBs msgBs evs =>
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.TopStateTight
              W.C.F W.Q.K stBs →
            LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
              maxOps W.C.F W.Q.K stBs msgBs evs)
        LibsignalBinary.Heap.SpecBudget.FormatInnerEnv)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets_placed))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W)
      defaultExtrasF3 W)
    (hSlot520 :
      (slotsOfSigPkFrozenPlaced A lim
        (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets_placed
          (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
            (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv
          (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) := by
  let S2c := cliRunSemD2c_placed defaultExtrasF3 W
  let DecPkEnv := DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
    (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv
  let sEnvs := g5ba_binaryKitRunSlotEnvsOfSendDecSigGuarded sendEnv maxOps W A cliRunBudgets_placed
    (realCliInitBinarySlotEnvFixed W) DecPkEnv
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hh := hHooks.runHooks
  exact g5b_hrun_of_slots_ofSendDecSigGuarded sendEnv maxOps mmpl gh W h547 hG hHooks
    (cliEncrypt_slotOk_placed mmpl gh W A lim cliRunBudgets S2c scopeIn sEnvs needs
      sendEnv
      (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hh hW1Inner encodeInjOn_deserializeScopeP_Q (fun _ h => h) rfl
      (fun _ _ _ _ hf he => ⟨hf.1, he⟩) rfl rfl)
    (g5ba_decSigSlotOk_decSigGuarded_of_stateGuardedInner maxOps mmpl gh defaultExtrasF3 W h547 hh
      hW2Inner)
    hInit hSlot520

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut
