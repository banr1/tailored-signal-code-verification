/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
public import LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0StageAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomMainFitsReduce

/-!
# `DecPkSlot`-Parametric `FitsEnv` Reducers and Post-Bob `prev1` Caps

**Checked by Lean.**

Provides `DecPkSlot`-parametric whole-`main` `FitsEnv` reducers, `RunEnv` inclusion
bridges, unconditional W2 (`decryptSignal`) slot budget witnesses, and `1 GiB` RAM /
`2 ^ 48` VA checks for the sum-form post-Bob `prev1` (`Dom0'`) W4 budget caps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (utf8)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost Init1Data MeAtDispatch PksmGhost RunSem runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (pksmParse_lengths_le signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (chainCloneDomFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak
   w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact
   ckx2_w1EncExact_groupSpec_Stmt ckx2_w1EncExact_phaseCredit_Stmt
   ckx2_w2DecSigExact_groupSpec_Stmt ckx2_w2DecSigExact_phaseCredit_Stmt)
open LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
  (ckx2_w2DecSigExact_groupSpec ckx2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs
   init1Env_sub_r1bFileStepEnv init2Env_sub_r1bBinaryEnv preEnv_sub_r0BinaryEnv
   r1cInit3Env_sub_r1cEnv r2SendEnv_sub_r2Env r3aRecvWEnv_sub_r3aBinaryEnv r3bRecvPEnv_sub_r3bEnv
   runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
   m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
   m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf' m2rg_W4RecvPrekeyTryDecACCmkEnvOf'
   m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' m2rg_verNePrev1P3PathCEnv' m2rg_verNePrev1P3PathCEnvOf')
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (bundleReadEnv_fixed_eq_of_not_overCap dirGetEnv_fixed_eq_of_not_overCap
   mkBinaryKitRealCalleeEnvsFixed not_overCapFile_runFiles_bundle_idKey
   not_overCapFile_runFiles_bundle_kpk not_overCapFile_runFiles_bundle_opk
   not_overCapFile_runFiles_bundle_regId not_overCapFile_runFiles_bundle_spk
   not_overCapFile_runFiles_own_address readFileRuleEnvFixed_eq_of_not_overCap
   realCliInitBinarySlotEnvFixed w3InitBinaryKitSlotEnvFixed_eq_plain)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (CanonicalOrFallbackPksmEnv pksmCanonicalOrFallback_sub_binaryKit
   recv_rest_length_le_msgCapBytes w1_send_outPk_serialized_le_sessionCapBytes
   w1_send_out_serialized_le_sessionCapBytes w3_realCliInitBinarySlotEnv_sub_binaryKit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (W4StageP3Prev1WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (W4StatesRecvEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk W4LoopAdvEnv w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget (Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env R1bStepKpkErrEnv R1bStepKpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomMainFitsReduce
  (mfr_fourSlotMain_fitsEnv_cliBudgetLimits_of_caps mfr_mkFourSlotCalleeEnvs
   mfr_slotMainFitsOneGiBOf mfr_w3InitExact_live_le_peak mfr_w3InitFixed_groupSpec
   mfr_w3InitFixed_phaseCredit)

/-! ## Definitional Slot Alignments and W2 Witnesses -/

/-- Definitional equality aligning `cliEncryptBinaryKitSlotEnvExact` with `ckx2_cliEncryptBinaryKitSlotEnvExact`. -/
theorem fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 [LibsignalPlacement] (W : CliHooks) :
    (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
      cliEncryptBinaryKitSlotEnvExact W A B) =
    (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
      ckx2_cliEncryptBinaryKitSlotEnvExact W A B) :=
  rfl

/-- Definitional equality aligning `cliDecryptSignalBinaryKitSlotEnvExact` with `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
theorem fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 [LibsignalPlacement] (W : CliHooks) :
    (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
      cliDecryptSignalBinaryKitSlotEnvExact W A B) =
    (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A B) := by
  have hdec :
      LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges.tlb_DecodeStateTightEnvOf =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_DecodeStateTightEnvOf :=
    rfl
  have htailCt2 :
      LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.RecvCt2ChunkTailEnv' =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_RecvCt2ChunkTailEnv' := by
    funext rk ct1 dk opt evs
    cases opt <;> rfl
  have hekCt2 : ∀ {F} s ep ch,
      LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.EkSentCt1ReceivedRecvCt2ChunkEnv'
          (F := F) s ep ch =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
          (F := F) s ep ch := by
    intro F s ep ch
    funext evs
    unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.EkSentCt1ReceivedRecvCt2ChunkEnv'
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
    rw [htailCt2]
  have htailEk : ∀ {F} K b uc opt,
      LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.RecvEkChunkSendCt2TailEnv'
          (F := F) K b uc opt =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_RecvEkChunkSendCt2TailEnv'
          (F := F) K b uc opt := by
    intro F K b uc opt
    funext evs
    cases opt <;> rfl
  have hsenv : ∀ {F} K st msg,
      LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
          (F := F) K st msg =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
          (F := F) K st msg := by
    intro F K st msg
    cases st with
    | ekSentCt1Received s =>
      unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
      cases msg.payload with
      | ct2 chunk =>
        dsimp only
        exact congrArg
          (fun E => if (msg.epoch == s.uc.epoch) = true then
            LibsignalBinary.Heap.SeqEnv E LibsignalBinary.Heap.FreeOnlyEvs
          else LibsignalBinary.Heap.FreeOnlyEvs)
          (hekCt2 s msg.epoch chunk)
      | _ => rfl
    | ct1Sampled s =>
      unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
      cases msg.payload with
      | ek chunk => dsimp only; rw [htailEk]
      | ekCt1Ack chunk => dsimp only; rw [htailEk]
      | _ => rfl
    | ekReceivedCt1Sampled s =>
      unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
      dsimp only
      rcases s.uc.send_ct2 K with _ | ⟨_, _, _⟩ <;> rfl
    | ct1Acknowledged s =>
      unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
      cases msg.payload with
      | ek chunk => dsimp only; rw [htailEk]
      | ekCt1Ack chunk => dsimp only; rw [htailEk]
      | _ => rfl
    | _ =>
      unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvEnv'
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvEnv'
      cases msg.payload <;> rfl
  have hproto :
      LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvProtoEnv'
          (F := W.C.F) W.Q.K =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvProtoEnv'
          (F := W.C.F) W.Q.K := by
    funext st msg
    unfold LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvProtoEnv'
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_StatesRecvProtoEnv'
    rw [hsenv]
  have htight :
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aTightLinkedEnvOf
          109 W.C.F W.Q.K =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_SpqrRecvC07C09aTightLinkedEnvOf
          109 W.C.F W.Q.K := by
    unfold LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aTightLinkedEnvOf
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_SpqrRecvC07C09aTightLinkedEnvOf
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aTightLinkedEnvRecvOf
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf
    rw [hdec, hproto]
  have hspqr :
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
          109 W.C.F W.Q.K =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_SpqrRecvC07C09aBytesEnvOf
          109 W.C.F W.Q.K := by
    unfold LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_SpqrRecvC07C09aBytesEnvOf
    simp only [htight]
  have hseg4 :=
    LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.tryDecryptCmkSeg4EnvOf_cmk_eq.trans
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_tryDecryptCmkSeg4EnvOf_cmk_eq.symm
  have htd :
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
          109 W.C W.Q.K =
        LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_TryDecryptCliLinkedEnvOf
          109 W.C W.Q.K := by
    funext a
    unfold LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_TryDecryptCliLinkedEnvOf
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedLoopEnvOf
      LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2.ckx2_TryDecryptCliLinkedLoopEnvOf
    dsimp only
    rcases CryptoGames.LibsignalSession.TripleRatchet.fromSessionState.exec a.st with ⟨_ | _, _⟩
    · rfl
    · rw [hseg4, hspqr]
  funext M A B
  unfold cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliDecryptSignalBinaryKitSlotEnvExact
  rw [htd]

/-- Unconditional W2 (`decryptSignal`) `PhaseCreditSpec` witness. -/
theorem fits2_w2DecSigExact_phaseCredit [LibsignalPlacement] (W : CliHooks) :
    ckx2_w2DecSigExact_phaseCredit_Stmt W :=
  ckx2_w2DecSigExact_phaseCredit W

/-- Unconditional W2 (`decryptSignal`) `PhaseGroupSpec` witness. -/
theorem fits2_w2DecSigExact_groupSpec [LibsignalPlacement] (W : CliHooks) :
    ckx2_w2DecSigExact_groupSpec_Stmt W :=
  ckx2_w2DecSigExact_groupSpec W

/-! ## `DecPkSlot`-Parametric Callee, `run`, and `main` Envelopes -/

/-- `DecPkSlot`-parametric 4-slot `CliRunCalleeEnvs` bundle using `cliEncryptBinaryKitSlotEnvExact` and `cliDecryptSignalBinaryKitSlotEnvExact`. -/
noncomputable abbrev fits2_mkBinaryKitRealCalleeEnvsDecPk [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs :=
  mfr_mkFourSlotCalleeEnvs
    (fun g' => (mkBinaryKitRealCalleeEnvsFixed img S X W g').initEnv)
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    DecPkSlot g

/-- Whole-`signal_session::run` binary-kit allocator trace predicate parametric in `DecPkSlot`. -/
noncomputable abbrev fits2_realCliRunBinaryKitEnvOfDecPk [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : List AllocEvent → Prop :=
  CliRunBinaryEnv cliIo.rd (fits2_mkBinaryKitRealCalleeEnvsDecPk DecPkSlot img S X W g)
    sessionCapBytes g

/-- Whole-`main` binary-kit allocator trace predicate parametric in `DecPkSlot`. -/
noncomputable abbrev fits2_realCliMainBinaryKitEnvOfDecPk [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  RealCliMainBinaryEnvOf (fits2_mkBinaryKitRealCalleeEnvsDecPk DecPkSlot img S X W) i

/-! ## Curried W4 Slot Obligations and Post-Bob `prev1` Caps -/

/-- Curried W4 (`decryptPrekey`) `PhaseCreditSpec` obligation on `DecPkSlot` under `CliPqxdhInputs` and `3#8 :: rest` prekey parse reachability. -/
def fits2_w4DecPk_phaseCredit_Stmt (W : CliHooks)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq : Nat) : Prop :=
  ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
    (pm : PreKeySignalMessage),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
    g.i.stdin.length ≤ msgCapBytes →
    g.c = .recv peerV →
    g.i.stdin = 3#8 :: rest →
    pksmParse rest = some pm →
    pm.message.ciphertext.length ≤ msgCapBytes →
    PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
      w4Cum w4Live w4Peak w4MaxReq

/-- Curried W4 (`decryptPrekey`) `PhaseGroupSpec` obligation on `DecPkSlot` under `CliPqxdhInputs` and `3#8 :: rest` prekey parse reachability. -/
def fits2_w4DecPk_groupSpec_Stmt (W : CliHooks)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (w4GrpS : Nat) : Prop :=
  ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
    (pm : PreKeySignalMessage),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
    g.i.stdin.length ≤ msgCapBytes →
    g.c = .recv peerV →
    g.i.stdin = 3#8 :: rest →
    pksmParse rest = some pm →
    pm.message.ciphertext.length ≤ msgCapBytes →
    PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
      w4GrpS

/-- `DecPkSlot`-parametric call-site allocator-envelope inclusion predicate. -/
def fits2_w4DecPk_slotSub_Stmt (W : CliHooks)
    (DecPkSlot W4TargetSlot : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
    (pm : PreKeySignalMessage) (evs : List AllocEvent),
    CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
    parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
    g.i.stdin.length ≤ msgCapBytes →
    g.c = .recv peerV →
    g.i.stdin = 3#8 :: rest →
    pksmParse rest = some pm →
    pm.message.ciphertext.length ≤ msgCapBytes →
    DecPkSlot (r3bDecPkGhost g meV peerV pm) evs →
    W4TargetSlot (r3bDecPkGhost g meV peerV pm) evs

/-- Baseline `Dom0` W4 allocator budget constants (`cum`, `live`, `peak`, `maxReq`, and `grpS` at `@83`/`@109`/`@128`). -/
def fits2_zbDom0Cum : Nat := 138754427
def fits2_zbDom0Live : Nat := 29203219
def fits2_zbDom0Peak : Nat := 29203219
def fits2_zbDom0MaxReq : Nat := 4194368
def fits2_zbDom0GrpS83 : Nat := 2696470354
def fits2_zbDom0GrpS109 : Nat := 2703750926
def fits2_zbDom0GrpS128 : Nat := 2709071344

theorem fits2_zbDom0_fits_oneGiB_83 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0Cum fits2_zbDom0Live fits2_zbDom0Peak fits2_zbDom0MaxReq fits2_zbDom0GrpS83 := by
  decide

theorem fits2_zbDom0_fits_oneGiB_109 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0Cum fits2_zbDom0Live fits2_zbDom0Peak fits2_zbDom0MaxReq fits2_zbDom0GrpS109 := by
  decide

theorem fits2_zbDom0_fits_oneGiB_128 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0Cum fits2_zbDom0Live fits2_zbDom0Peak fits2_zbDom0MaxReq fits2_zbDom0GrpS128 := by
  decide

/-- Sum-form post-Bob `prev1` (`Dom0'`) W4 allocator budget caps:
`cum = 140,230,427` B, `live = peak = 29,726,017` B, `maxReq = 4,194,368` B, and
`grpS` specialized at `@83`, `@109`, and `@128`. -/
def fits2_zbDom0PrimeCum : Nat := 140230427
def fits2_zbDom0PrimeLive : Nat := 29726017
def fits2_zbDom0PrimePeak : Nat := 29726017
def fits2_zbDom0PrimeMaxReq : Nat := 4194368
def fits2_zbDom0PrimeGrpSOf (maxOps : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpSOf maxOps +
    (3 * FineScale + chainCloneDomFineGrpS)
def fits2_zbDom0PrimeGrpS83 : Nat := 2730214888
def fits2_zbDom0PrimeGrpS109 : Nat := 2737495460
def fits2_zbDom0PrimeGrpS128 : Nat := 2742815878

theorem fits2_zbDom0PrimeGrpSOf_83_eq :
    fits2_zbDom0PrimeGrpSOf 83 = fits2_zbDom0PrimeGrpS83 := by decide
theorem fits2_zbDom0PrimeGrpSOf_109_eq :
    fits2_zbDom0PrimeGrpSOf w4c_defaultDecodeMaxOps = fits2_zbDom0PrimeGrpS109 := by decide
theorem fits2_zbDom0PrimeGrpSOf_128_eq :
    fits2_zbDom0PrimeGrpSOf 128 = fits2_zbDom0PrimeGrpS128 := by decide

/-- Decidable `1 GiB` RAM and `2 ^ 48` VA check for `Dom0'` caps at `@83`. -/
theorem fits2_zbDom0Prime_fits_oneGiB_83 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0PrimeCum fits2_zbDom0PrimeLive fits2_zbDom0PrimePeak fits2_zbDom0PrimeMaxReq
      fits2_zbDom0PrimeGrpS83 := by
  decide

/-- Decidable `1 GiB` RAM and `2 ^ 48` VA check for `Dom0'` caps at `@109`. -/
theorem fits2_zbDom0Prime_fits_oneGiB_109 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0PrimeCum fits2_zbDom0PrimeLive fits2_zbDom0PrimePeak fits2_zbDom0PrimeMaxReq
      fits2_zbDom0PrimeGrpS109 := by
  decide

/-- Decidable `1 GiB` RAM and `2 ^ 48` VA check for `Dom0'` caps at `@128`. -/
theorem fits2_zbDom0Prime_fits_oneGiB_128 :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      fits2_zbDom0PrimeCum fits2_zbDom0PrimeLive fits2_zbDom0PrimePeak fits2_zbDom0PrimeMaxReq
      fits2_zbDom0PrimeGrpS128 := by
  decide

/-! ## Whole-`main` `FitsEnv` Reducers -/

/-- Reduces whole-`main` `FitsEnv` on `fits2_realCliMainBinaryKitEnvOfDecPk` to W1, W2, and `DecPkSlot` W4 credit/group bounds. -/
theorem fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_parts [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hW1Credit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hW1Grp : ckx2_w1EncExact_groupSpec_Stmt W)
    (hW2Credit : ckx2_w2DecSigExact_phaseCredit_Stmt W)
    (hW2Grp : ckx2_w2DecSigExact_groupSpec_Stmt W)
    {w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat}
    (hW4Credit : fits2_w4DecPk_phaseCredit_Stmt W DecPkSlot w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : fits2_w4DecPk_groupSpec_Stmt W DecPkSlot w4GrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (fits2_realCliMainBinaryKitEnvOfDecPk DecPkSlot img S X W i) :=
  mfr_fourSlotMain_fitsEnv_cliBudgetLimits_of_caps W i hi
    (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    DecPkSlot
    (fun g hi_g _hp _hin => mfr_w3InitFixed_phaseCredit img S X W g hi_g)
    mfr_w3InitExact_live_le_peak
    (fun g hi_g _hp _hin => mfr_w3InitFixed_groupSpec img S X W g hi_g)
    (fun g peerV M A w1R hi_g hp _hin hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact hW1Credit g peerV M A w1R hi_g hp hc hrep hdom)
    (Nat.le_refl _)
    (fun g peerV M A w1R hi_g hp _hin hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A w1R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact hW1Grp g peerV M A w1R hi_g hp hc hrep hdom)
    (fun g peerV M A w2R hi_g hp _hin hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact hW2Credit g peerV M A w2R hi_g hp hc hrep hdom)
    (Nat.le_refl _)
    (fun g peerV M A w2R hi_g hp _hin hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact hW2Grp g peerV M A w2R hi_g hp hc hrep hdom)
    hW4Credit
    hW4Lp
    hW4Grp
    hFits

/-- Specializes `fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_parts` by discharging W2 internally, leaving W1 and `DecPkSlot` W4. -/
theorem fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_w4 [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hW1Credit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hW1Grp : ckx2_w1EncExact_groupSpec_Stmt W)
    {w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat}
    (hW4Credit : fits2_w4DecPk_phaseCredit_Stmt W DecPkSlot w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : fits2_w4DecPk_groupSpec_Stmt W DecPkSlot w4GrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (fits2_realCliMainBinaryKitEnvOfDecPk DecPkSlot img S X W i) :=
  fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_parts DecPkSlot img S X W i hi
    hW1Credit hW1Grp
    (fits2_w2DecSigExact_phaseCredit W)
    (fits2_w2DecSigExact_groupSpec W)
    hW4Credit hW4Lp hW4Grp hFits

/-- Composes `fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_w4` with a call-site envelope inclusion `fits2_w4DecPk_slotSub_Stmt`. -/
theorem fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_slotSub [LibsignalPlacement]
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hW1Credit : ckx2_w1EncExact_phaseCredit_Stmt W)
    (hW1Grp : ckx2_w1EncExact_groupSpec_Stmt W)
    {W4TargetSlot : DecPkGhost → List AllocEvent → Prop}
    {w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat}
    (hW4Sub : fits2_w4DecPk_slotSub_Stmt W DecPkSlot W4TargetSlot)
    (hW4Credit : fits2_w4DecPk_phaseCredit_Stmt W W4TargetSlot w4Cum w4Live w4Peak w4MaxReq)
    (hW4Lp : w4Live ≤ w4Peak)
    (hW4Grp : fits2_w4DecPk_groupSpec_Stmt W W4TargetSlot w4GrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (fits2_realCliMainBinaryKitEnvOfDecPk DecPkSlot img S X W i) :=
  fits2_realCliMainBinaryKitEnvOfDecPk_fitsEnv_of_w1_and_w4 DecPkSlot img S X W i hi
    hW1Credit hW1Grp
    (fun g peerV meV rest pm hi_g hp hin hc hstdin hpk hct =>
      PhaseCreditSpec.of_imp
        (fun evs hevs => hW4Sub g peerV meV rest pm evs hi_g hp hin hc hstdin hpk hct hevs)
        (hW4Credit g peerV meV rest pm hi_g hp hin hc hstdin hpk hct))
    hW4Lp
    (fun g peerV meV rest pm hi_g hp hin hc hstdin hpk hct =>
      ⟨fun st0 {_} hevs =>
        (hW4Grp g peerV meV rest pm hi_g hp hin hc hstdin hpk hct).groups_le st0
          (hW4Sub g peerV meV rest pm _ hi_g hp hin hc hstdin hpk hct hevs)⟩)
    hFits

/-- Contravariant allocator-envelope inclusion map on `SingleSlotFineSpec`. -/
def fits2_singleSlotFineSpec_of_imp {E₁ E₂ : List AllocEvent → Prop}
    (hImp : ∀ evs, E₁ evs → E₂ evs) (sp : SingleSlotFineSpec E₂) :
    SingleSlotFineSpec E₁ where
  cum := sp.cum
  live := sp.live
  peak := sp.peak
  maxReq := sp.maxReq
  grpS := sp.grpS
  credit := sp.credit.of_imp hImp
  live_le_peak := sp.live_le_peak
  groups := ⟨fun st0 {_} hevs => sp.groups.groups_le st0 (hImp _ hevs)⟩

/-! ## Stage-Envelope Alignment for Empty Archived Trials and `RunEnv` Inclusion -/

/-- When `w.base.archivedTrials = []`, `IterSeqEnv _ []` collapses to `(· = [])` on both matched and over paths, aligning the `Dom0` and `StageAux` wide slot envelopes. -/
theorem fits2_dom0Fixed_eq_stageAuxFixed_of_nil
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk)
    (hnil : w.base.archivedTrials = []) :
    LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
        SR LoopAdvEnv maxOps w =
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
        SR LoopAdvEnv maxOps w := by
  have hPB :
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
          SR LoopAdvEnv maxOps w =
        m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' LoopAdvEnv maxOps SR w := by
    funext evs
    unfold LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
      m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf
      m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
    dsimp only
    rw [hnil]
    rfl
  have hPA :
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
          SR LoopAdvEnv maxOps w =
        m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' LoopAdvEnv maxOps SR w :=
    rfl
  have hPC :
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
          SR LoopAdvEnv maxOps w =
        m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
          LoopAdvEnv maxOps SR (m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR) w := by
    funext evs
    unfold LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
      m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
      m2rg_verNePrev1P3PathCEnv' m2rg_verNePrev1P3PathCEnvOf'
      W4StageP3Prev1WideEnv
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4RecvPrekeyTryDecACCmkSrEnvOf
      m2rg_W4RecvPrekeyTryDecACCmkEnvOf'
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf
      m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
    dsimp only
    rw [hnil]
    rfl
  funext evs
  unfold LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
  rw [hPB, hPA, hPC]

private theorem fits2_send_stdin_length_le_msgCapBytes {g : RunCall} {peerV : AddrV}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV) :
    g.i.stdin.length ≤ msgCapBytes := by
  have hin_stdin : g.i.stdin.length ≤ stdinCapBytes := by
    simpa [hc, inputOf, CallV.tag] using hin
  have hcap_le : stdinCapBytes ≤ msgCapBytes := by
    unfold stdinCapBytes msgCapBytes
    decide
  exact Nat.le_trans hin_stdin hcap_le

private theorem fits2_preEnv_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i) :
    PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
      PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
  funext evs
  unfold PreEnv cliRunCalleesEnvs
  dsimp only
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi)]

private theorem fits2_init1Env_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (me : MeAtDispatch) (peerV : AddrV) (dir : List (BitVec 8)) :
    Init1Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g me peerV dir =
      Init1Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g me peerV dir := by
  funext evs
  cases me with
  | none => rfl
  | some _ _ =>
    unfold Init1Env cliRunCalleesEnvs
    dsimp only
    rw [readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_idKey hi dir)]

private theorem fits2_init2Env_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i) (d1 : Init1Data) :
    Init2Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g d1 =
      Init2Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g d1 := by
  let cF := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  let cP := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)
  have hreg : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_regId hi d1.dir)
  have hspk : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_spk hi d1.dir)
  have hkpk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_kpk hi d1.dir)
  have hopk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_opk hi d1.dir)
  have hsid : cF.splitId = cP.splitId := rfl
  have hssg : cF.splitSigned = cP.splitSigned := rfl
  have hopkOk : ∀ bs, R1bStepOpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepOpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepOpkOkEnv; rw [hopk, hsid]
  have hopkErr : R1bStepOpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepOpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepOpkErrEnv; rw [hopk, hsid]
  have hst3 : ∀ spkKey kpkKey, Init2Stage3Env cF (runFiles g.i) d1.dir spkKey kpkKey =
      Init2Stage3Env cP (runFiles g.i) d1.dir spkKey kpkKey := by
    intro spkKey kpkKey; funext evs; unfold Init2Stage3Env
    rw [hopk, hopkErr, hsid]; simp only [hopkOk]
  have hkpkOk : ∀ bs, R1bStepKpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepKpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepKpkOkEnv; rw [hkpk, hssg]
  have hkpkErr : R1bStepKpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepKpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepKpkErrEnv; rw [hkpk]; simp only [hkpkOk]
  have hst2 : ∀ spkKey, Init2Stage2Env cF (runFiles g.i) d1.dir spkKey =
      Init2Stage2Env cP (runFiles g.i) d1.dir spkKey := by
    intro spkKey; funext evs; unfold Init2Stage2Env
    rw [hkpk, hkpkErr]; simp only [hkpkOk, hst3]
  have hafter : Init2AfterRegOkEnv cF (runFiles g.i) d1.dir =
      Init2AfterRegOkEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold Init2AfterRegOkEnv
    dsimp only
    rw [hspk, hssg]; simp only [hst2]
  funext evs
  change Init2Env cF g d1 evs = Init2Env cP g d1 evs
  unfold Init2Env
  dsimp only
  rw [hreg, hafter]

/-- Whole-`run` `RunEnv` inclusion into `fits2_realCliRunBinaryKitEnvOfDecPk`. -/
theorem fits2_runEnvDecPk_sub_runBinaryKitEnvOfDecPk [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf
            (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
            (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
            A B (realCliInitBinarySlotEnvFixed W) DecPkSlot)
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      fits2_realCliRunBinaryKitEnvOfDecPk DecPkSlot img S X W g evs :=
  runEnv_to_cliRunBinaryEnv_of_slots
    (fun _ hp =>
      preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
        (Eq.mp (congrFun (fits2_preEnv_fixed_eq_plain hi) _) hp))
    (fun me peerV dir _ _ h1 =>
      init1Env_sub_r1bFileStepEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl g me peerV dir (Eq.mp (congrFun (fits2_init1Env_fixed_eq_plain hi me peerV dir) _) h1))
    (fun _ _ d1 _ _ hd1 h2 =>
      hd1 ▸ init2Env_sub_r1bBinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl rfl rfl rfl g d1 (Eq.mp (congrFun (fits2_init2Env_fixed_eq_plain hi d1) _) h2))
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ h3 =>
      r1cInit3Env_sub_r1cEnv
        (fun _ ⟨w', hx', hF', hspqr', hgv', halice', hslotF'⟩ =>
          w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
            ⟨w', hx', hF', hspqr', hgv', halice',
              Eq.mp
                (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx')) _)
                hslotF'⟩)
        h3)
    (fun _me peerV _ hc hs =>
      r2SendEnv_sub_r2Env
        (fun _ meG _evs _hme he => by
          let w1R : W1BinarySendParams :=
            ⟨A.repAlloc, B, r2PeerGhost0 peerV, r2EncGhost g (r2PeerGhost0 peerV) meG 0#64⟩
          have hptext : g.i.stdin.length ≤ msgCapBytes :=
            fits2_send_stdin_length_le_msgCapBytes hin hc
          have hdom : W1BinarySendDom g.c g.i w1R := by
            intro pAddr hpAddr
            rw [hc] at hpAddr
            injection hpAddr with hpEq
            subst hpEq
            exact ⟨rfl, rfl, rfl, hptext, rfl⟩
          dsimp only [fits2_mkBinaryKitRealCalleeEnvsDecPk, mfr_mkFourSlotCalleeEnvs]
          rw [hc]
          exact ⟨M, A, w1R, rfl, hc ▸ hdom, he⟩)
        (fun meV f m heq =>
          w1_send_out_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc)
        (fun meV f m heq =>
          w1_send_outPk_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc) hs)
    (fun _me peerV rest _ hc hst hrw =>
      r3aRecvWEnv_sub_r3aBinaryEnv
        (fun _ meG m _evs _hme htr hd => by
          let x := r3aDecSigGhost0 g peerV meG m
          let w2R : W2BinaryWhisperParams := ⟨A.repAlloc, B, x.peer, x⟩
          have hct_rest : m.ciphertext.length ≤ rest.length :=
            (signalMessage_tryFrom_lengths_le htr).2.1
          have hrest_cap : rest.length ≤ msgCapBytes :=
            recv_rest_length_le_msgCapBytes hin hc hst
          have hct_cap : m.ciphertext.length ≤ msgCapBytes :=
            Nat.le_trans hct_rest hrest_cap
          have hdom : W2BinaryWhisperDom g.c g.i w2R := by
            intro pAddr hpAddr
            rw [hc] at hpAddr
            injection hpAddr with hpEq
            subst hpEq
            exact ⟨rfl, rfl, rfl, hct_cap, rfl⟩
          dsimp only [fits2_mkBinaryKitRealCalleeEnvsDecPk, mfr_mkFourSlotCalleeEnvs]
          rw [hc]
          exact ⟨M, A, w2R, rfl, hc ▸ hdom, hd⟩) hrw)
    (fun _me peerV rest _ hc hst hrp =>
      r3bRecvPEnv_sub_r3bEnv
        (fun _ hpk =>
          pksmCanonicalOrFallback_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl hpk)
        (fun meV _meG pm _evs _hme hpk hd => by
          have hpk' : pksmParse rest = some pm := hS_pksm ▸ hpk
          have hct_rest : pm.message.ciphertext.length ≤ rest.length :=
            (pksmParse_lengths_le hpk').2.2.1
          have hrest_cap : rest.length ≤ msgCapBytes :=
            recv_rest_length_le_msgCapBytes hin hc hst
          have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
            Nat.le_trans hct_rest hrest_cap
          dsimp only [fits2_mkBinaryKitRealCalleeEnvsDecPk, mfr_mkFourSlotCalleeEnvs]
          rw [hc]
          exact ⟨meV, rest, pm, hst, hpk', hct_cap, hd⟩) hrp)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
