/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomMainFitsReduce

/-!
# Parametric Non-Prekey `RunEnv` and `pqD3ScopedRun` Reach Bridges

**Checked by Lean.**

Establishes parametric `RunEnv`, SPQR state-size, and W4-free `FitsEnv` bridges for the
non-prekey `main` budget obligation (`hole_g5a_untyped_fitsCap`):
1. Outside prekey `recv` (`3#8 :: _`), `RunEnv (cliMainArmEnvs cEnvs sEnvs Pksm S) g` depends
   only on `cEnvs`, `sEnvs.initiate`, `sEnvs.encrypt`, `sEnvs.decryptSignal`, and `S.encrypt`,
   without unfolding the `encrypt` or `decryptSignal` slot envelopes.
2. `pqD3ScopedRun ⟨W.C, W.Q⟩` implies `PeerSpqrStateTight640` and `CliRunTightSpqrStateCaps`.
3. Setting `decPkEnv := fun _ => False` on the non-prekey domain decouples whole-`main` `FitsEnv`
   from the prekey `decryptPrekey` slot, reducing `MainEntryBudgetFitsCapOf` to `encrypt` and
   `decryptSignal` phase-credit and phase-group bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (ReadRule RunAnswer pathOf)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRunBudgets cliRunBudgets_placed inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost PksmGhost RunSem addrValOf runFiles runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (argv_length_le_of_cliPqInputs)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (m5PhaseEnv_groupSpec m6Env_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (binaryKitSlotInit_fineSpec exactCeilingMainCum exactCeilingMainGrpS exactCeilingMainPeak
   exactCeilingMainReq exactCeilingMain_fits_oneGiB exactMainCumOf exactMainGrpSOf exactMainLiveOf
   exactMainPeakGenOf exactMainReqOf w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq
   w1EncExactPeak w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq
   w2DecSigExactPeak w3InitExactCum w3InitExactGrpS w3InitExactLive w3InitExactMaxReq
   w3InitExactPeak w4DecPkExactCum w4DecPkExactGrpS w4DecPkExactLive w4DecPkExactMaxReq
   w4DecPkExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq m3PhaseMaxReq
   m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs r2DeltaLive r2DeltaPeak r2MaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (phaseCredit_or_freeOnly_left)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv OptStageEnv RealCliMainBinaryEnvOf RecvArmBinaryEnv RunArmBinaryEnv
   cliMainArmEnvs cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
   cliRunBinary1MiBCustomPksmCum cliRunBinary1MiBCustomPksmMaxReq
   cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs cliRunCalleesEnvs
   m5Phase_Bounded_phaseCredit_fine)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmPeak
   cliRunOpenedCustomPksmGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
  (hmx_binaryKitRunSlotEnvsSlotOf hmx_runEnvExact_sub_runBinaryKitEnvOfSlot
   mkBinaryKitRealCalleeEnvsSlotOf realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt
   realCliRunBinaryKitEnvOfSlot)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (cliRunBinaryEnv_fine_groupSpec_of_cap)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (ValidPostSetupWitness)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
  (cliRunSpqrStateTightCaps_of_cliPqOrD3RecvInputs
   cliRunTightSpqrStateCaps_of_cliPqOrD3RecvInputs
   peerSpqrStateTight640_of_cliPqOrD3RecvInputs_recv
   peerSpqrStateTight640_of_cliPqOrD3RecvInputs_send)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (CliRunSpqrStateTightCaps CliRunTightSpqrStateCaps PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_seq_freeOnly phaseCredit_w4BoundedEvs_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (phaseCredit_optStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (boxAllocEnv_fine_le_28)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (boxAllocEnv_le_28_fine_groupSpec phaseGroupSpec_optStage w4BoundedEvs_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive pksmCanonSliceLive_le_peak
   pksmCanonSliceMaxReq pksmCanonSlicePeak pksmCanonSlice_fine_groupSpec
   pksmCanonSlice_fine_phaseCredit)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs defaultExtrasF3 pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (R1cInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (R2SendEnv R2TailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (R3aRecvWEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)

/-! ## Non-Prekey `RunEnv` Congruence and `binaryKitRunSlotEnvsExact` Bridges -/

theorem g5ar_r1cInit3Env_eq_of_initiate {sEnvs₁ sEnvs₂ : RunSlotEnvs}
    (hs_init : sEnvs₁.initiate = sEnvs₂.initiate) :
    R1cInit3Env sEnvs₁ = R1cInit3Env sEnvs₂ := by
  funext g d2 evs
  unfold R1cInit3Env
  rw [hs_init]

theorem g5ar_r2TailEnv_eq_of_encrypt {S₁ S₂ : RunSem}
    (hS : S₁.encrypt = S₂.encrypt) :
    R2TailEnv S₁ = R2TailEnv S₂ := by
  funext g meV peerV evs_tail
  unfold R2TailEnv
  rw [hS]

theorem g5ar_r2SendEnv_eq_of_encrypt {sEnvs₁ sEnvs₂ : RunSlotEnvs} {S₁ S₂ : RunSem}
    (hs_enc : sEnvs₁.encrypt = sEnvs₂.encrypt)
    (hS : S₁.encrypt = S₂.encrypt) :
    R2SendEnv sEnvs₁ S₁ = R2SendEnv sEnvs₂ S₂ := by
  funext g me peerV evs
  unfold R2SendEnv
  cases me with
  | none => rfl
  | some _ _ => rw [hs_enc, g5ar_r2TailEnv_eq_of_encrypt hS]

theorem g5ar_r3aRecvWEnv_eq_of_decryptSignal {sEnvs₁ sEnvs₂ : RunSlotEnvs}
    (hs_dec : sEnvs₁.decryptSignal = sEnvs₂.decryptSignal) :
    R3aRecvWEnv sEnvs₁ = R3aRecvWEnv sEnvs₂ := by
  funext g me peerV rest evs
  unfold R3aRecvWEnv
  cases me with
  | none => rfl
  | some _ _ => rw [hs_dec]

/-- Outside prekey `recv` (`3#8 :: _`), `RunEnv aEnvs g` depends only on `aEnvs.pre`, `aEnvs.init1`,
`aEnvs.init2`, `aEnvs.init3`, `aEnvs.send`, and `aEnvs.recvW` (independent of `pksmTryFrom` and
`recvP`). -/
theorem g5ar_runEnv_armEnvs_nonPrekey_eq
    {aEnvs₁ aEnvs₂ : RunArmEnvs} {g : RunCall}
    (hpre : aEnvs₁.pre = aEnvs₂.pre)
    (hinit1 : aEnvs₁.init1 = aEnvs₂.init1)
    (hinit2 : aEnvs₁.init2 = aEnvs₂.init2)
    (hinit3 : aEnvs₁.init3 = aEnvs₂.init3)
    (hsend : aEnvs₁.send = aEnvs₂.send)
    (hrecvW : aEnvs₁.recvW = aEnvs₂.recvW)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) :
    RunEnv aEnvs₁ g = RunEnv aEnvs₂ g := by
  have hi3 : ∀ meV peerV dir,
      RunInit3Env aEnvs₁ g meV peerV dir = RunInit3Env aEnvs₂ g meV peerV dir := by
    intro meV peerV dir; funext evs; unfold RunInit3Env; rw [hinit3]
  have hi2 : ∀ meV peerV dir,
      RunInit2ChainEnv aEnvs₁ g meV peerV dir = RunInit2ChainEnv aEnvs₂ g meV peerV dir := by
    intro meV peerV dir; funext evs; unfold RunInit2ChainEnv; rw [hinit2, hi3]
  have harm : ∀ me, RunArmAtMeEnv aEnvs₁ g me = RunArmAtMeEnv aEnvs₂ g me := by
    intro me; funext evs; unfold RunArmAtMeEnv
    cases hc : g.c with
    | keygen _ _ => rfl
    | send _ => rw [hsend]
    | init _ _ => cases me <;> simp only [hinit1, hi2]
    | recv peerV =>
      cases hst : g.i.stdin with
      | nil => rfl
      | cons t rest =>
        by_cases ht2 : t = 2#8
        · simp only [ht2, ↓reduceIte, hrecvW]
        · by_cases ht3 : t = 3#8
          · exfalso; exact hnp peerV rest hc (ht3 ▸ hst)
          · simp only [ht2, ht3, ↓reduceIte]
  have hdisp : RunDispatchEnv aEnvs₁ g = RunDispatchEnv aEnvs₂ g := by
    funext evs; unfold RunDispatchEnv; simp only [harm]
  have hcore : RunCoreEnv aEnvs₁ g = RunCoreEnv aEnvs₂ g := by
    funext evs; unfold RunCoreEnv; rw [hpre, hdisp]
  funext evs; unfold RunEnv; rw [hcore]

/-- Outside prekey `recv` (`3#8 :: _`), `RunEnv (cliMainArmEnvs cEnvs sEnvs Pksm S) g` depends only
on `cEnvs`, `sEnvs.initiate`, `sEnvs.encrypt`, `sEnvs.decryptSignal`, and `S.encrypt` (completely
independent of `sEnvs.decryptPrekey` and `Pksm`). -/
theorem g5ar_runEnv_cliMainArmEnvs_nonPrekey_eq
    {cEnvs : RunCalleesEnvs} {sEnvs₁ sEnvs₂ : RunSlotEnvs}
    {Pksm₁ Pksm₂ : PksmGhost → List AllocEvent → Prop}
    {S₁ S₂ : RunSem} {g : RunCall}
    (hs_init : sEnvs₁.initiate = sEnvs₂.initiate)
    (hs_enc : sEnvs₁.encrypt = sEnvs₂.encrypt)
    (hs_dec : sEnvs₁.decryptSignal = sEnvs₂.decryptSignal)
    (hS : S₁.encrypt = S₂.encrypt)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) :
    RunEnv (cliMainArmEnvs cEnvs sEnvs₁ Pksm₁ S₁) g =
      RunEnv (cliMainArmEnvs cEnvs sEnvs₂ Pksm₂ S₂) g :=
  g5ar_runEnv_armEnvs_nonPrekey_eq rfl rfl rfl
    (g5ar_r1cInit3Env_eq_of_initiate hs_init)
    (g5ar_r2SendEnv_eq_of_encrypt hs_enc hS)
    (g5ar_r3aRecvWEnv_eq_of_decryptSignal hs_dec)
    hnp

/-- `(cliRunSemD3 W).encrypt` and `(cliRunSemD2c_placed X W).encrypt` are definitionally equal
(`encDef ⟨W.C, W.Q⟩ scopeIn`). -/
theorem g5ar_cliRunSemD3_encrypt_eq_d2c [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    (cliRunSemD3 W).encrypt = (cliRunSemD2c_placed X W).encrypt :=
  rfl

/-- Specialization of `g5ar_runEnv_cliMainArmEnvs_nonPrekey_eq` to `binaryKitRunSlotEnvsExact`
without unfolding the `encrypt` or `decryptSignal` slot envelopes. -/
theorem g5ar_runEnv_exact_nonPrekey_eq [LibsignalPlacement] {M : AllocCostModel}
    {cEnvs : RunCalleesEnvs} {W : CliHooks} {A : RustCliAllocBudget M}
    {B₁ B₂ : RunBudgets}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop}
    {Pksm₁ Pksm₂ : PksmGhost → List AllocEvent → Prop}
    {S₁ S₂ : RunSem} {g : RunCall}
    (hB : B₁ = B₂ := by rfl)
    (hS : S₁.encrypt = S₂.encrypt := by rfl)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) :
    RunEnv (cliMainArmEnvs cEnvs (binaryKitRunSlotEnvsExact W A B₁ InitEnv DecPkEnv₁) Pksm₁ S₁) g =
      RunEnv (cliMainArmEnvs cEnvs (binaryKitRunSlotEnvsExact W A B₂ InitEnv DecPkEnv₂) Pksm₂ S₂) g := by
  subst hB
  exact g5ar_runEnv_cliMainArmEnvs_nonPrekey_eq rfl rfl rfl hS hnp

/-- Transfers a non-prekey `CliRunBinaryEnv` inclusion at `(B₂, DecPkEnv₂, Pksm₂, S₂)` to
`(cliRunBudgets_placed, DecPkEnv₁, PksmTryFromEnv, cliRunSemD3 W)` without unfolding the
`encrypt` or `decryptSignal` slot envelopes. -/
theorem g5ar_d3_nonPrekey_runEnv_sub [LibsignalPlacement] {M : AllocCostModel}
    {W : CliHooks} {A : RustCliAllocBudget M}
    {B₂ : RunBudgets}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop}
    {Pksm₂ : PksmGhost → List AllocEvent → Prop}
    {S₂ : RunSem}
    {E_pq : RunCall → CliRunCalleeEnvs}
    (hB : cliRunBudgets_placed = B₂ := by rfl)
    (hS : (cliRunSemD3 W).encrypt = S₂.encrypt := by rfl)
    (hSub : ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A B₂ (realCliInitBinarySlotEnvFixed W) DecPkEnv₂)
            Pksm₂ S₂)
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs := by
  intro g hi hparse hin hnp evs hrun
  have heq :=
    g5ar_runEnv_exact_nonPrekey_eq (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (W := W) (A := A) (InitEnv := realCliInitBinarySlotEnvFixed W)
      (DecPkEnv₁ := DecPkEnv₁) (DecPkEnv₂ := DecPkEnv₂)
      (Pksm₁ := PksmTryFromEnv) (Pksm₂ := Pksm₂)
      hB hS hnp
  exact hSub g hi hparse hin hnp evs (Eq.mp (congrFun heq evs) hrun)

/-- Specialization of `g5ar_d3_nonPrekey_runEnv_sub` when the source `CliRunBinaryEnv` inclusion
holds on all `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i` (including prekey calls). -/
theorem g5ar_d3_nonPrekey_runEnv_sub_of_all [LibsignalPlacement] {M : AllocCostModel}
    {W : CliHooks} {A : RustCliAllocBudget M}
    {B₂ : RunBudgets}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop}
    {Pksm₂ : PksmGhost → List AllocEvent → Prop}
    {S₂ : RunSem}
    {E_pq : RunCall → CliRunCalleeEnvs}
    (hB : cliRunBudgets_placed = B₂ := by rfl)
    (hS : (cliRunSemD3 W).encrypt = S₂.encrypt := by rfl)
    (hSub : ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A B₂ (realCliInitBinarySlotEnvFixed W) DecPkEnv₂)
            Pksm₂ S₂)
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs :=
  g5ar_d3_nonPrekey_runEnv_sub hB hS (fun g hi hparse hin _hnp => hSub g hi hparse hin)

/-- Specialization of `g5ar_d3_nonPrekey_runEnv_sub_of_all` to `B₂ := cliRunBudgets` and
`S₂ := cliRunSemD2c_placed X W`. -/
theorem g5ar_d3_nonPrekey_runEnv_sub_d2c [LibsignalPlacement] {M : AllocCostModel}
    (X : UnreachedPqxdhPrimitives)
    {W : CliHooks} {A : RustCliAllocBudget M}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop}
    {Pksm₂ : PksmGhost → List AllocEvent → Prop}
    {E_pq : RunCall → CliRunCalleeEnvs}
    (hSub : ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets (realCliInitBinarySlotEnvFixed W) DecPkEnv₂)
            Pksm₂ (cliRunSemD2c_placed X W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs :=
  g5ar_d3_nonPrekey_runEnv_sub_of_all rfl (g5ar_cliRunSemD3_encrypt_eq_d2c X W) hSub

/-! ## `pqD3ScopedRun` SPQR State-Size Bridges -/

theorem g5ar_cliPqOrD3RecvInputs_of_pqD3ScopedRun
    {WP : PEParams} {Run₀ : Inputs → RunAnswer → Prop} {i : Inputs} {a : RunAnswer}
    (hdom : pqD3ScopedRun WP Run₀ i a) :
    CliPqOrD3RecvInputs WP i :=
  hdom.1

/-- Under `pqD3ScopedRun W Run₀ i a`, any `.send peer` call satisfies
`PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer)` (excluding the D3 `.recv` arm). -/
theorem g5ar_peerSpqrStateTight640_send_of_pqD3
    {W : PEParams} {Run₀ : Inputs → RunAnswer → Prop} {i : Inputs} {a : RunAnswer} {peer : AddrV}
    (hdom : pqD3ScopedRun W Run₀ i a)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) :=
  peerSpqrStateTight640_of_cliPqOrD3RecvInputs_send hdom.1 hparse

/-- Under `pqD3ScopedRun W Run₀ i a`, any `.recv peer` call satisfies
`PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer)`. -/
theorem g5ar_peerSpqrStateTight640_recv_of_pqD3
    {W : PEParams} {Run₀ : Inputs → RunAnswer → Prop} {i : Inputs} {a : RunAnswer} {peer : AddrV}
    (hdom : pqD3ScopedRun W Run₀ i a)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) (addrValOf peer) :=
  peerSpqrStateTight640_of_cliPqOrD3RecvInputs_recv hdom.1 hparse

theorem g5ar_cliRunSpqrStateTightCaps_of_pqD3
    {W : PEParams} {Run₀ : Inputs → RunAnswer → Prop} {maxInitDir bundleCap : Nat}
    {g : RunCall} {a : RunAnswer}
    (hdom : pqD3ScopedRun W Run₀ g.i a)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    CliRunSpqrStateTightCaps W.C.F W.Q.K maxInitDir bundleCap g :=
  cliRunSpqrStateTightCaps_of_cliPqOrD3RecvInputs hdom.1 hparse hinit

/-- Canonical `1 MiB` (`maxInitDir = 26`, `bundleCap = 1,637` B) `CliRunTightSpqrStateCaps` lift
from `pqD3ScopedRun W Run₀ g.i a`. -/
theorem g5ar_cliRunTightSpqrStateCaps_of_pqD3
    {W : PEParams} {Run₀ : Inputs → RunAnswer → Prop} {g : RunCall} {a : RunAnswer}
    (hdom : pqD3ScopedRun W Run₀ g.i a)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ 26 ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ 1637)) :
    CliRunTightSpqrStateCaps W.C.F W.Q.K g :=
  cliRunTightSpqrStateCaps_of_cliPqOrD3RecvInputs hdom.1 hparse hinit

/-! ## Non-Prekey `RunEnv` Inclusion and W4-Free `FitsEnv` -/

/-- Outside prekey `recv` (`3#8 :: _`), `CliRunBinaryEnv rd E wireOutCap g` depends only on
`E.initEnv`, `E.encEnv`, and `E.decSigEnv` (independent of `E.pksmEnv` and `E.decPkEnv`). -/
theorem g5ar_cliRunBinaryEnv_nonPrekey_eq
    {rd : ReadRule} {E₁ E₂ : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall}
    (hinit : E₁.initEnv = E₂.initEnv)
    (henc : E₁.encEnv = E₂.encEnv)
    (hds : E₁.decSigEnv = E₂.decSigEnv)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) :
    CliRunBinaryEnv rd E₁ wireOutCap g = CliRunBinaryEnv rd E₂ wireOutCap g := by
  have harm :
      RunArmBinaryEnv rd (runFiles g.i) E₁ wireOutCap g.i.stdin g.c =
        RunArmBinaryEnv rd (runFiles g.i) E₂ wireOutCap g.i.stdin g.c := by
    funext evs
    unfold RunArmBinaryEnv
    cases hc : g.c with
    | keygen _ _ => rfl
    | init _ _ => rw [hinit]
    | send _ => rw [henc]
    | recv peerV =>
      unfold RecvArmBinaryEnv
      cases hst : g.i.stdin with
      | nil => rfl
      | cons b rest =>
        by_cases hb2 : b = 2#8
        · simp only [hb2, ↓reduceIte, hds]
        · by_cases hb3 : b = 3#8
          · exfalso; exact hnp peerV rest hc (hb3 ▸ hst)
          · simp only [hb2, hb3, ↓reduceIte]
  funext evs
  unfold CliRunBinaryEnv
  rw [harm]

/-- Non-prekey `CliRunCalleeEnvs` bundle agreeing with `mkBinaryKitRealCalleeEnvsSlotOf` on
`initEnv`, `encEnv`, `decSigEnv`, and `pksmEnv`, with `decPkEnv := fun _ => False`. -/
noncomputable def g5ar_mkNonPrekeyCalleeEnvsSlotOf [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs :=
  { mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g with
    decPkEnv := fun _ => False }

/-- Whole-`main` non-prekey allocator trace predicate over `g5ar_mkNonPrekeyCalleeEnvsSlotOf`. -/
noncomputable abbrev g5ar_realCliMainNonPrekeyEnvOfSlot [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  RealCliMainBinaryEnvOf (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W) i

/-- Slot-parametric non-prekey `RunEnv` inclusion into `realCliRunBinaryKitEnvOfSlot` at
`cliRunSemD3 W` and `cliRunBudgets_placed`. -/
theorem g5ar_d3_nonPrekey_runEnvSlot_sub_binaryKit [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S₂ : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (A : RustCliAllocBudget M)
    {DecPkEnv₁ : DecPkGhost → List AllocEvent → Prop}
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        realCliRunBinaryKitEnvOfSlot EncSlot DecSigSlot img S₂ X W g evs := by
  intro g hi hparse hin hnp evs hrun
  have hS_d3 : (cliRunSemD3 W).encrypt = S₂.encrypt := by
    calc (cliRunSemD3 W).encrypt
      _ = encDef ⟨W.C, W.Q⟩ scopeIn := rfl
      _ = S₂.encrypt := hS_enc.symm
  have heq :
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
          PksmTryFromEnv (cliRunSemD3 W))
        g =
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv) S₂)
        g :=
    g5ar_runEnv_cliMainArmEnvs_nonPrekey_eq rfl (by rfl) (by rfl) hS_d3 hnp
  exact hmx_runEnvExact_sub_runBinaryKitEnvOfSlot (FallbackEnv := PksmTryFromEnv)
    EncSlot DecSigSlot img S₂ X W A cliRunBudgets hi hparse hin hS_enc hS_pksm evs
    (Eq.mp (congrFun heq evs) hrun)

/-- Specialization of `g5ar_d3_nonPrekey_runEnvSlot_sub_binaryKit` to
`binaryKitRunSlotEnvsExact`. -/
theorem g5ar_d3_nonPrekey_runEnvExact_sub_binaryKit [LibsignalPlacement] {M : AllocCostModel}
    (img : Image) (S₂ : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (A : RustCliAllocBudget M)
    {DecPkEnv₁ : DecPkGhost → List AllocEvent → Prop}
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        realCliRunBinaryKitEnvOfSlot
          (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
          (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
          img S₂ X W g evs :=
  g5ar_d3_nonPrekey_runEnvSlot_sub_binaryKit
    (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    img S₂ X W A hS_enc hS_pksm

/-- Non-prekey `RunEnv` inclusion into `g5ar_mkNonPrekeyCalleeEnvsSlotOf`. -/
theorem g5ar_d3_nonPrekey_runEnvSlot_sub_nonPrekeyKit [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S₂ : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (A : RustCliAllocBudget M)
    {DecPkEnv₁ : DecPkGhost → List AllocEvent → Prop}
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd
          (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S₂ X W g)
          sessionCapBytes g evs := by
  intro g hi hparse hin hnp evs hrun
  have hbin :=
    g5ar_d3_nonPrekey_runEnvSlot_sub_binaryKit EncSlot DecSigSlot img S₂ X W A
      (DecPkEnv₁ := DecPkEnv₁) hS_enc hS_pksm g hi hparse hin hnp evs hrun
  have heq :=
    g5ar_cliRunBinaryEnv_nonPrekey_eq (rd := cliIo.rd)
      (E₁ := mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S₂ X W g)
      (E₂ := g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S₂ X W g)
      (wireOutCap := sessionCapBytes) rfl rfl rfl hnp
  exact Eq.mp (congrFun heq evs) hbin

/-- Specialization of `g5ar_d3_nonPrekey_runEnvSlot_sub_nonPrekeyKit` to
`binaryKitRunSlotEnvsExact`. -/
theorem g5ar_d3_nonPrekey_runEnvExact_sub_nonPrekeyKit [LibsignalPlacement] {M : AllocCostModel}
    (img : Image) (S₂ : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (A : RustCliAllocBudget M)
    {DecPkEnv₁ : DecPkGhost → List AllocEvent → Prop}
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
              (realCliInitBinarySlotEnvFixed W) DecPkEnv₁)
            PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd
          (g5ar_mkNonPrekeyCalleeEnvsSlotOf
            (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
            (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
            img S₂ X W g)
          sessionCapBytes g evs :=
  g5ar_d3_nonPrekey_runEnvSlot_sub_nonPrekeyKit
    (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    img S₂ X W A hS_enc hS_pksm

private theorem g5ar_max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem g5ar_optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem g5ar_optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private def g5ar_nonPrekeyCalleeFineSpecs [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    CliRealCalleeFineSpecs
      (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g) where
  initCum := w3InitExactCum
  initLive := w3InitExactLive
  initPeak := w3InitExactPeak
  initMaxReq := w3InitExactMaxReq
  initGrpS := w3InitExactGrpS
  init_spec := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).credit
  init_lp := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).live_le_peak
  init_grp := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).groups
  encCum := Senc.cum
  encLive := Senc.live
  encPeak := Senc.peak
  encMaxReq := Senc.maxReq
  encGrpS := Senc.grpS
  enc_spec := Senc.credit
  enc_lp := Senc.live_le_peak
  enc_grp := Senc.groups
  decSigCum := Sds.cum
  decSigLive := Sds.live
  decSigPeak := Sds.peak
  decSigMaxReq := Sds.maxReq
  decSigGrpS := Sds.grpS
  decSig_spec := Sds.credit
  decSig_lp := Sds.live_le_peak
  decSig_grp := Sds.groups
  pksmCum := pksmCanonSliceCum msgCapBytes
  pksmLive := pksmCanonSliceLive msgCapBytes
  pksmPeak := pksmCanonSlicePeak msgCapBytes
  pksmMaxReq := pksmCanonSliceMaxReq msgCapBytes
  pksmGrpS := pksmCanonSliceGrpS msgCapBytes
  pksm_spec := fun _ hrest => pksmCanonSlice_fine_phaseCredit hrest
  pksm_lp := pksmCanonSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmCanonSlice_fine_groupSpec hrest
  decPkCum := 0
  decPkLive := 0
  decPkPeak := 0
  decPkMaxReq := 0
  decPkGrpS := 0
  decPk_spec := (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
  decPk_lp := Nat.le_refl 0
  decPk_grp := (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)

private theorem g5ar_nonPrekeyCalleeFineSpecs_bounds [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (hEnc : Senc.cum ≤ w1EncExactCum ∧ Senc.live ≤ w1EncExactLive ∧ Senc.peak ≤ w1EncExactPeak ∧
      Senc.maxReq ≤ w1EncExactMaxReq ∧ Senc.grpS ≤ w1EncExactGrpS)
    (hDs : Sds.cum ≤ w2DecSigExactCum ∧ Sds.live ≤ w2DecSigExactLive ∧ Sds.peak ≤ w2DecSigExactPeak ∧
      Sds.maxReq ≤ w2DecSigExactMaxReq ∧ Sds.grpS ≤ w2DecSigExactGrpS)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
    cliRunBinary1MiBCustomPksmCum
      SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRunBinary1MiBCustomPksmCum
        (pksmCanonSliceCum msgCapBytes) w3InitExactCum
        w1EncExactCum w2DecSigExactCum w4DecPkExactCum ∧
    cliRun1MiBCustomPksmLive
      SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRun1MiBCustomPksmLive
        (pksmCanonSliceLive msgCapBytes) w3InitExactLive
        w1EncExactLive w2DecSigExactLive w4DecPkExactLive ∧
    cliRun1MiBCustomPksmPeak
      SE.pksmLive SE.pksmPeak SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRun1MiBCustomPksmPeak
        (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
        w3InitExactPeak w1EncExactLive w1EncExactPeak w2DecSigExactPeak w4DecPkExactPeak ∧
    cliRunBinary1MiBCustomPksmMaxReq
      SE.pksmMaxReq SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq
        w1EncExactMaxReq w2DecSigExactMaxReq w4DecPkExactMaxReq ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes
      SE.pksmGrpS SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS
        w1EncExactGrpS w2DecSigExactGrpS w4DecPkExactGrpS := by
  rcases hEnc with ⟨hec, hel, hep, her, heg⟩
  rcases hDs with ⟨hdc, hdl, hdp, hdr, hdg⟩
  have hpc : 0 ≤ w4DecPkExactCum := Nat.zero_le _
  have hpl : 0 ≤ w4DecPkExactLive := Nat.zero_le _
  have hpp : 0 ≤ w4DecPkExactPeak := Nat.zero_le _
  have hpr : 0 ≤ w4DecPkExactMaxReq := Nat.zero_le _
  have hpg : 0 ≤ w4DecPkExactGrpS := Nat.zero_le _
  dsimp only [g5ar_nonPrekeyCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliRunBinary1MiBCustomPksmCum
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono (Nat.add_le_add hec (Nat.le_refl _))
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdc)
            (Nat.add_le_add (Nat.le_refl _) hpc))))
  · unfold cliRun1MiBCustomPksmLive
    have hr2l :
        r2DeltaLive fineCostModel Senc.live sessionCapBytes ≤
          r2DeltaLive fineCostModel w1EncExactLive sessionCapBytes := by
      unfold r2DeltaLive
      exact Nat.add_le_add hel (Nat.le_refl _)
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono hr2l
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdl)
            (Nat.add_le_add (Nat.le_refl _) hpl))))
  · unfold cliRun1MiBCustomPksmPeak
    have hr2p :
        r2DeltaPeak fineCostModel Senc.live Senc.peak sessionCapBytes ≤
          r2DeltaPeak fineCostModel w1EncExactLive w1EncExactPeak sessionCapBytes := by
      unfold r2DeltaPeak
      exact g5ar_max_mono hep (Nat.add_le_add hel (Nat.le_refl _))
    exact g5ar_max_mono (Nat.le_refl _)
      (Nat.add_le_add (Nat.le_refl _)
        (g5ar_max_mono (Nat.le_refl _)
          (g5ar_max_mono hr2p
            (g5ar_max_mono (g5ar_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hdp))
              (g5ar_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpp))))))
  · unfold cliRunBinary1MiBCustomPksmMaxReq
    have hr2r :
        r2MaxReq Senc.maxReq sessionCapBytes ≤
          r2MaxReq w1EncExactMaxReq sessionCapBytes := by
      unfold r2MaxReq
      exact g5ar_max_mono her (Nat.le_refl _)
    exact g5ar_max_mono (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono hr2r
          (g5ar_max_mono (g5ar_max_mono (Nat.le_refl _) hdr)
            (g5ar_max_mono (Nat.le_refl _) hpr))))
  · unfold cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono (Nat.add_le_add heg (Nat.le_refl _))
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdg)
            (Nat.add_le_add (Nat.le_refl _) hpg))))

/-- Proves whole-`main` `FitsEnv fineCostModel cliBudgetLimits fineCostModel.init` on
`g5ar_realCliMainNonPrekeyEnvOfSlot` from `encrypt` and `decryptSignal` slot specs alone. -/
theorem g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_slotSpecs [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (S_enc : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hparse
      se.cum ≤ w1EncExactCum ∧ se.live ≤ w1EncExactLive ∧ se.peak ≤ w1EncExactPeak ∧
      se.maxReq ≤ w1EncExactMaxReq ∧ se.grpS ≤ w1EncExactGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hparse
      sd.cum ≤ w2DecSigExactCum ∧ sd.live ≤ w2DecSigExactLive ∧ sd.peak ≤ w2DecSigExactPeak ∧
      sd.maxReq ≤ w2DecSigExactMaxReq ∧ sd.grpS ≤ w2DecSigExactGrpS) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  obtain ⟨hinit_grp, hram0, hva0⟩ := exactCeilingMain_fits_oneGiB
  have hcap1G : cliOneGiB ≤ cliBudgetLimits.physCap := by
    unfold cliBudgetLimits cliOneGiB
    decide
  have hram :
      cliDecoupledRamNeed cliBudgetLimits.staticBytes
        exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
        ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ cliBudgetLimits.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  have hva :
      cliDecoupledVaNeed cliBudgetLimits.staticBytes cliBudgetLimits.staticCount
        exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
        ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  intro i hi
  let rCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) w3InitExactCum w1EncExactCum w2DecSigExactCum w4DecPkExactCum
  let rLive := cliRun1MiBCustomPksmLive
    (pksmCanonSliceLive msgCapBytes) w3InitExactLive w1EncExactLive w2DecSigExactLive w4DecPkExactLive
  let rPeak := cliRun1MiBCustomPksmPeak
    (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
    w3InitExactPeak w1EncExactLive w1EncExactPeak w2DecSigExactPeak w4DecPkExactPeak
  let rMaxReq := cliRunBinary1MiBCustomPksmMaxReq
    (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq
    w1EncExactMaxReq w2DecSigExactMaxReq w4DecPkExactMaxReq
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS
    w1EncExactGrpS w2DecSigExactGrpS w4DecPkExactGrpS
  have hsm1024 :
      1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (CliRunBinaryEnv cliIo.rd
          (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Senc := S_enc w.g hi_g w.parse_ok
    let Sds := S_decSig w.g hi_g w.parse_ok
    let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
    obtain ⟨h1, h2, h3, h4, _⟩ :=
      g5ar_nonPrekeyCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds
        (hEncCaps w.g hi_g w.parse_ok)
        (hDecSigCaps w.g hi_g w.parse_ok) hi_g
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
        SE hi_g w.stdin_le w.parse_ok).mono h1 h2 h3 h4
    refine (hrun.seq
      ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
        (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact g5ar_max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact g5ar_max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i)
      exactCeilingMainCum
      (exactMainLiveOf w1EncExactLive w2DecSigExactLive w4DecPkExactLive)
      exactCeilingMainPeak
      exactCeilingMainReq := by
    refine ((cliMainBoundedSetup_phaseCredit_fine
        (argv_length_le_of_cliPqInputs hi)).seq
      (g5ar_optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold exactCeilingMainCum exactMainCumOf
      dsimp only [rCum]
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold exactMainLiveOf cliMainTightLiveOf cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold exactCeilingMainPeak exactMainPeakGenOf cliMainTightPeakOf cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold exactCeilingMainReq exactMainReqOf cliMainTightReqOf cliMainMaxReq
      have h16k :
          max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes
        decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      ((rGrpS + 27 * FineScale) +
        cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Senc := S_enc w.g hi_g w.parse_ok
        let Sds := S_decSig w.g hi_g w.parse_ok
        let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
        obtain ⟨_, _, _, _, h5⟩ :=
          g5ar_nonPrekeyCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds
            (hEncCaps w.g hi_g w.parse_ok)
            (hDecSigCaps w.g hi_g w.parse_ok) hi_g
        have h15 : 15 * FineScale ≤ rGrpS := by
          dsimp only [rGrpS]
          unfold cliRunOpenedCustomPksmGrpS
          exact Nat.le_add_right (15 * FineScale) _
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ rGrpS - 15 * FineScale := hinit_grp
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le h15 hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv
              (CliRunBinaryEnv cliIo.rd
                (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            ((rGrpS + 27 * FineScale) +
              cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i)
      exactCeilingMainGrpS :=
    ((cliMainBoundedSetup_fine_groupSpec
        (argv_length_le_of_cliPqInputs hi)).seq
      (g5ar_optStage_groupSpec hex_grp)).mono
      (by unfold exactCeilingMainGrpS exactMainGrpSOf
          dsimp only [rGrpS]
          generalize FineScale = fs; omega)
  have hlp :
      exactMainLiveOf w1EncExactLive w2DecSigExactLive w4DecPkExactLive ≤
      exactCeilingMainPeak := by
    unfold exactCeilingMainPeak exactMainLiveOf exactMainPeakGenOf
      cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

/-- Curried companion to `g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_slotSpecs` taking
explicit `PhaseCreditSpec` and `PhaseGroupSpec` bounds for `EncSlot` and `DecSigSlot`. -/
theorem g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_curried [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) w2DecSigExactGrpS) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  let S_enc (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv) :=
    { cum := w1EncExactCum
      live := w1EncExactLive
      peak := w1EncExactPeak
      maxReq := w1EncExactMaxReq
      grpS := w1EncExactGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := Nat.le_refl _
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncGrp g peerV M A w1R hi_g hp hgc hrep hdom).groups_le st0 he } }
  let S_decSig (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv) :=
    { cum := w2DecSigExactCum
      live := w2DecSigExactLive
      peak := w2DecSigExactPeak
      maxReq := w2DecSigExactMaxReq
      grpS := w2DecSigExactGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := Nat.le_refl _
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigGrp g peerV M A w2R hi_g hp hgc hrep hdom).groups_le st0 he } }
  exact g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_slotSpecs
    EncSlot DecSigSlot img S X W S_enc S_decSig
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

/-! ## Parametric `RunSlotEnvs` and Cap-Parametric Reducers -/

/-- `RunSlotEnvs`-parametric non-prekey `RunEnv` inclusion into
`g5ar_mkNonPrekeyCalleeEnvsSlotOf` for any `sEnvs` matching on `initiate`, `encrypt`, and
`decryptSignal`. -/
theorem g5ar_d3_nonPrekey_runEnv_of_slots_sub_nonPrekeyKit [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S₂ : RunSem) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks) (A : RustCliAllocBudget M)
    (sEnvs : RunSlotEnvs)
    (hs_init : sEnvs.initiate = realCliInitBinarySlotEnvFixed W := by rfl)
    (hs_enc : sEnvs.encrypt = EncSlot A cliRunBudgets_placed := by rfl)
    (hs_ds : sEnvs.decryptSignal = DecSigSlot A cliRunBudgets_placed := by rfl)
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl) :
    ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd
          (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S₂ X W g)
          sessionCapBytes g evs := by
  intro g hi hparse hin hnp evs hrun
  have heq :
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W))
        g =
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W) sEnvs.decryptPrekey)
          PksmTryFromEnv (cliRunSemD3 W))
        g :=
    g5ar_runEnv_cliMainArmEnvs_nonPrekey_eq hs_init hs_enc hs_ds rfl hnp
  exact g5ar_d3_nonPrekey_runEnvSlot_sub_nonPrekeyKit EncSlot DecSigSlot img S₂ X W A
    (DecPkEnv₁ := sEnvs.decryptPrekey) hS_enc hS_pksm g hi hparse hin hnp evs
    (Eq.mp (congrFun heq evs) hrun)

private theorem g5ar_nonPrekeyCalleeFineSpecs_bounds_of_caps [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall}
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat}
    (Senc : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (hEnc : Senc.cum ≤ encCum ∧ Senc.live ≤ encLive ∧ Senc.peak ≤ encPeak ∧
      Senc.maxReq ≤ encMaxReq ∧ Senc.grpS ≤ encGrpS)
    (hDs : Sds.cum ≤ decSigCum ∧ Sds.live ≤ decSigLive ∧ Sds.peak ≤ decSigPeak ∧
      Sds.maxReq ≤ decSigMaxReq ∧ Sds.grpS ≤ decSigGrpS)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
    cliRunBinary1MiBCustomPksmCum
      SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRunBinary1MiBCustomPksmCum
        (pksmCanonSliceCum msgCapBytes) w3InitExactCum encCum decSigCum 0 ∧
    cliRun1MiBCustomPksmLive
      SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRun1MiBCustomPksmLive
        (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive 0 ∧
    cliRun1MiBCustomPksmPeak
      SE.pksmLive SE.pksmPeak SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRun1MiBCustomPksmPeak
        (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
        w3InitExactPeak encLive encPeak decSigPeak 0 ∧
    cliRunBinary1MiBCustomPksmMaxReq
      SE.pksmMaxReq SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq 0 ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes
      SE.pksmGrpS SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS 0 := by
  rcases hEnc with ⟨hec, hel, hep, her, heg⟩
  rcases hDs with ⟨hdc, hdl, hdp, hdr, hdg⟩
  dsimp only [g5ar_nonPrekeyCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliRunBinary1MiBCustomPksmCum
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono (Nat.add_le_add hec (Nat.le_refl _))
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdc) (Nat.le_refl _))))
  · unfold cliRun1MiBCustomPksmLive
    have hr2l :
        r2DeltaLive fineCostModel Senc.live sessionCapBytes ≤
          r2DeltaLive fineCostModel encLive sessionCapBytes := by
      unfold r2DeltaLive
      exact Nat.add_le_add hel (Nat.le_refl _)
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono hr2l
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdl) (Nat.le_refl _))))
  · unfold cliRun1MiBCustomPksmPeak
    have hr2p :
        r2DeltaPeak fineCostModel Senc.live Senc.peak sessionCapBytes ≤
          r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes := by
      unfold r2DeltaPeak
      exact g5ar_max_mono hep (Nat.add_le_add hel (Nat.le_refl _))
    exact g5ar_max_mono (Nat.le_refl _)
      (Nat.add_le_add (Nat.le_refl _)
        (g5ar_max_mono (Nat.le_refl _)
          (g5ar_max_mono hr2p
            (g5ar_max_mono (g5ar_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hdp))
              (Nat.le_refl _)))))
  · unfold cliRunBinary1MiBCustomPksmMaxReq
    have hr2r :
        r2MaxReq Senc.maxReq sessionCapBytes ≤
          r2MaxReq encMaxReq sessionCapBytes := by
      unfold r2MaxReq
      exact g5ar_max_mono her (Nat.le_refl _)
    exact g5ar_max_mono (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono hr2r
          (g5ar_max_mono (g5ar_max_mono (Nat.le_refl _) hdr) (Nat.le_refl _))))
  · unfold cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add (Nat.le_refl _)
      (g5ar_max_mono (Nat.le_refl _)
        (g5ar_max_mono (Nat.add_le_add heg (Nat.le_refl _))
          (g5ar_max_mono (Nat.add_le_add (Nat.le_refl _) hdg) (Nat.le_refl _))))

/-- Cap- and `BudgetLimits`-parametric whole-`main` `FitsEnv` on
`g5ar_realCliMainNonPrekeyEnvOfSlot`. -/
theorem g5ar_nonPrekeyMain_fitsEnv_of_caps [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat}
    (S_enc : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hparse
      se.cum ≤ encCum ∧ se.live ≤ encLive ∧ se.peak ≤ encPeak ∧
      se.maxReq ≤ encMaxReq ∧ se.grpS ≤ encGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hparse
      sd.cum ≤ decSigCum ∧ sd.live ≤ decSigLive ∧ sd.peak ≤ decSigPeak ∧
      sd.maxReq ≤ decSigMaxReq ∧ sd.grpS ≤ decSigGrpS)
    (hinit_grp :
      234 * FineScale + w3InitExactGrpS ≤
        cliRunOpenedCustomPksmGrpS msgCapBytes
          (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS 0 -
        15 * FineScale)
    (hram :
      cliDecoupledRamNeed lim.staticBytes
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      lim.physCap)
    (hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      2 ^ 48) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init
        (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  intro i hi
  let rCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) w3InitExactCum encCum decSigCum 0
  let rLive := cliRun1MiBCustomPksmLive
    (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive 0
  let rPeak := cliRun1MiBCustomPksmPeak
    (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
    w3InitExactPeak encLive encPeak decSigPeak 0
  let rMaxReq := cliRunBinary1MiBCustomPksmMaxReq
    (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq 0
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS 0
  have hsm1024 :
      1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (CliRunBinaryEnv cliIo.rd
          (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Senc := S_enc w.g hi_g w.parse_ok
    let Sds := S_decSig w.g hi_g w.parse_ok
    let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
    obtain ⟨h1, h2, h3, h4, _⟩ :=
      g5ar_nonPrekeyCalleeFineSpecs_bounds_of_caps EncSlot DecSigSlot img S X W Senc Sds
        (hEncCaps w.g hi_g w.parse_ok)
        (hDecSigCaps w.g hi_g w.parse_ok) hi_g
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
        SE hi_g w.stdin_le w.parse_ok).mono h1 h2 h3 h4
    refine (hrun.seq
      ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
        (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact g5ar_max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact g5ar_max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i)
      (exactMainCumOf encCum decSigCum 0)
      (exactMainLiveOf encLive decSigLive 0)
      (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
      (exactMainReqOf encMaxReq decSigMaxReq 0) := by
    refine ((cliMainBoundedSetup_phaseCredit_fine
        (argv_length_le_of_cliPqInputs hi)).seq
      (g5ar_optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold exactMainCumOf
      dsimp only [rCum]
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold exactMainLiveOf cliMainTightLiveOf cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold exactMainPeakGenOf cliMainTightPeakOf cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold exactMainReqOf cliMainTightReqOf cliMainMaxReq
      have h16k :
          max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes
        decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      ((rGrpS + 27 * FineScale) +
        cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Senc := S_enc w.g hi_g w.parse_ok
        let Sds := S_decSig w.g hi_g w.parse_ok
        let SE := g5ar_nonPrekeyCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds hi_g
        obtain ⟨_, _, _, _, h5⟩ :=
          g5ar_nonPrekeyCalleeFineSpecs_bounds_of_caps EncSlot DecSigSlot img S X W Senc Sds
            (hEncCaps w.g hi_g w.parse_ok)
            (hDecSigCaps w.g hi_g w.parse_ok) hi_g
        have h15 : 15 * FineScale ≤ rGrpS := by
          dsimp only [rGrpS]
          unfold cliRunOpenedCustomPksmGrpS
          exact Nat.le_add_right (15 * FineScale) _
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ rGrpS - 15 * FineScale := hinit_grp
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le h15 hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv
              (CliRunBinaryEnv cliIo.rd
                (g5ar_mkNonPrekeyCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            ((rGrpS + 27 * FineScale) +
              cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i)
      (exactMainGrpSOf encGrpS decSigGrpS 0) :=
    ((cliMainBoundedSetup_fine_groupSpec
        (argv_length_le_of_cliPqInputs hi)).seq
      (g5ar_optStage_groupSpec hex_grp)).mono
      (by unfold exactMainGrpSOf
          dsimp only [rGrpS]
          generalize FineScale = fs; omega)
  have hlp :
      exactMainLiveOf encLive decSigLive 0 ≤
      exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0 := by
    unfold exactMainLiveOf exactMainPeakGenOf
      cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- Curried cap-parametric `FitsEnv` at `cliBudgetLimits` over arbitrary `(enc*, decSig*)`
bounds with `encLive ≤ encPeak` and `decSigLive ≤ decSigPeak`. -/
theorem g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_curried_caps [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat}
    (hEncLp : encLive ≤ encPeak)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) decSigGrpS)
    (hinit_grp :
      234 * FineScale + w3InitExactGrpS ≤
        cliRunOpenedCustomPksmGrpS msgCapBytes
          (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS 0 -
        15 * FineScale)
    (hram :
      cliDecoupledRamNeed cliDefaultStaticBytes
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      cliOneGiB)
    (hva :
      cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      2 ^ 48) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (g5ar_realCliMainNonPrekeyEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  let S_enc (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv) :=
    { cum := encCum
      live := encLive
      peak := encPeak
      maxReq := encMaxReq
      grpS := encGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := hEncLp
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncGrp g peerV M A w1R hi_g hp hgc hrep hdom).groups_le st0 he } }
  let S_decSig (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv) :=
    { cum := decSigCum
      live := decSigLive
      peak := decSigPeak
      maxReq := decSigMaxReq
      grpS := decSigGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := hDecSigLp
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigGrp g peerV M A w2R hi_g hp hgc hrep hdom).groups_le st0 he } }
  have hcap1G : cliOneGiB ≤ cliBudgetLimits.physCap := by
    unfold cliBudgetLimits cliOneGiB
    decide
  have hram_lim :
      cliDecoupledRamNeed cliBudgetLimits.staticBytes
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      cliBudgetLimits.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram hcap1G)
  have hva_lim :
      cliDecoupledVaNeed cliBudgetLimits.staticBytes cliBudgetLimits.staticCount
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva
  exact g5ar_nonPrekeyMain_fitsEnv_of_caps rfl EncSlot DecSigSlot img S X W S_enc S_decSig
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    hinit_grp hram_lim hva_lim

/-- 9-op Bob session-build allocation envelope (`SeqEnv (W4BoundedEvs 9 68) FreeOnlyEvs`). -/
def g5ar_W4BobSessionBuild9Env : List AllocEvent → Prop :=
  SeqEnv (W4BoundedEvs 9 68) FreeOnlyEvs

/-- Fine `PhaseCreditSpec` for `g5ar_W4BobSessionBuild9Env` (`cum = 87,075 B`, `live = 0`,
`peak = 0`, `maxReq = 68`). -/
theorem g5ar_bob9_fine_phaseCredit :
    PhaseCreditSpec fineCostModel g5ar_W4BobSessionBuild9Env 87075 0 0 68 :=
  (phaseCredit_seq_freeOnly fineCostModel_modelHyps
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 9 68
      (by rw [fineCostModel_smallMaxReq_eq]; decide))).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 68)

/-- Fine `PhaseGroupSpec` for `g5ar_W4BobSessionBuild9Env` (`grpS = 27 * FineScale`). -/
theorem g5ar_bob9_fine_groupSpec :
    PhaseGroupSpec fineCostModel g5ar_W4BobSessionBuild9Env (27 * FineScale) :=
  ((w4BoundedEvs_groupSpec fineCostModel 9 68).seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (by unfold FineScale; decide)

/-- Fine `PhaseCreditSpec` for `W4OuterPeakSpec.OptStageEnv (BoxAllocEnv 16)` (`cum = 488 B`,
`live = 0`, `peak = 0`, `maxReq = 16`). -/
theorem g5ar_optStage_boxAlloc16_fine_phaseCredit :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.OptStageEnv (BoxAllocEnv 16))
      488 0 0 16 :=
  phaseCredit_optStageEnv fineCostModel_modelHyps (boxAllocEnv_fine_le_28 (by decide : 16 ≤ 28))

/-- Tight fine `PhaseGroupSpec` for `W4OuterPeakSpec.OptStageEnv (BoxAllocEnv 16)`
(`grpS = 11,056`). -/
theorem g5ar_optStage_boxAlloc16_fine_groupSpec_tight :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.OptStageEnv (BoxAllocEnv 16))
      11056 :=
  phaseGroupSpec_optStage (boxAllocEnv_le_28_fine_groupSpec (by decide : 16 ≤ 28))

theorem g5ar_optStage_boxAlloc16_fine_groupSpec_3scale :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.OptStageEnv (BoxAllocEnv 16))
      (3 * FineScale) :=
  g5ar_optStage_boxAlloc16_fine_groupSpec_tight.mono (by unfold FineScale; decide)

/-- Arithmetic check that `w1EncExact*` (`128` ops) absorbs the `109`-op send envelope with
`33,210 B` cumulative slack and `57 * FineScale` group slack. -/
theorem g5ar_w1EncExact_absorbs_109_decide :
    w1SendRealDcanCum + 26 * 738 ≤ w1EncExactCum ∧
    w1EncExactCum - w1SendRealDcanCum = 33210 ∧
    w1SendRealDcanGrpS + 26 * (3 * FineScale) ≤ w1EncExactGrpS ∧
    w1EncExactGrpS - (w1SendRealDcanGrpS + 26 * (3 * FineScale)) = 57 * FineScale := by
  decide

/-- Arithmetic check that the non-prekey whole-`main` ceiling fits `1 GiB` and `2^48` VA
with `+9,603 B` (`OptSecret32AllocEnv`) and `+3 * FineScale` added to both `encrypt` and
`decryptSignal`. -/
theorem g5ar_nonPrekeyCeiling_plus_3b_fits_oneGiB :
    234 * FineScale + w3InitExactGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS
        (w1EncExactGrpS + 3 * FineScale) (w2DecSigExactGrpS + 3 * FineScale) 0 -
      15 * FineScale ∧
    cliDecoupledRamNeed cliDefaultStaticBytes
      (exactMainCumOf (w1EncExactCum + 9603) (w2DecSigExactCum + 9603) 0)
      (exactMainPeakGenOf w1EncExactLive w1EncExactPeak w2DecSigExactLive w2DecSigExactPeak 0 0)
      (exactMainReqOf w1EncExactMaxReq w2DecSigExactMaxReq 0)
      ((exactMainGrpSOf (w1EncExactGrpS + 3 * FineScale) (w2DecSigExactGrpS + 3 * FineScale) 0 +
        FineScale - 1) / FineScale) ≤
      cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      (exactMainCumOf (w1EncExactCum + 9603) (w2DecSigExactCum + 9603) 0)
      (exactMainPeakGenOf w1EncExactLive w1EncExactPeak w2DecSigExactLive w2DecSigExactPeak 0 0)
      (exactMainReqOf w1EncExactMaxReq w2DecSigExactMaxReq 0)
      ((exactMainGrpSOf (w1EncExactGrpS + 3 * FineScale) (w2DecSigExactGrpS + 3 * FineScale) 0 +
        FineScale - 1) / FineScale) ≤
      2 ^ 48 := by
  decide

/-! ## `MainEntryBudgetFitsCapOf` Reducers -/

/-- Prekey-branch join reducer signature reducing `MainEntryBudgetFitsCapOf` on
`pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))` to whole-`main` `FitsEnv` and non-prekey
`RunEnv` inclusion on `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
abbrev g5ar_PrekeyJoinReducer [LibsignalPlacement] (W : CliHooks) (sEnvs : RunSlotEnvs) : Prop :=
  ∀ (E_pq : RunCall → CliRunCalleeEnvs),
    (∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E_pq i)) →
    (∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) →
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W)))

/-- Closes `MainEntryBudgetFitsCapOf` from `g5ar_PrekeyJoinReducer` and
`realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt` without unfolding `encrypt` or
`decryptSignal` slot envelopes. -/
theorem g5ar_hole_g5a_of_exactKitFits
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    {img : Image} {S₂ : RunSem} {X : UnreachedPqxdhPrimitives}
    (hJoin : g5ar_PrekeyJoinReducer W
      (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          PqxdhAcceptBadKemErrEnv)))
    (hS_enc : S₂.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S₂.pksmParse = pksmParse := by rfl)
    (hFits :
      realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt
        (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
        (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
        img S₂ X W) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
              PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) :=
  hJoin
    (mkBinaryKitRealCalleeEnvsSlotOf
      (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      img S₂ X W)
    hFits
    (g5ar_d3_nonPrekey_runEnvExact_sub_binaryKit img S₂ X W A hS_enc hS_pksm)

/-- Closes `MainEntryBudgetFitsCapOf` from `g5ar_PrekeyJoinReducer` and `PhaseCreditSpec` /
`PhaseGroupSpec` bounds for `cliEncryptBinaryKitSlotEnvExact` and
`cliDecryptSignalBinaryKitSlotEnvExact` alone. -/
theorem g5ar_hole_g5a_of_enc_decSig
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (hJoin : g5ar_PrekeyJoinReducer W
      (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
        (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
          (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
          PqxdhAcceptBadKemErrEnv)))
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel
        (cliEncryptBinaryKitSlotEnvExact W A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel
        (cliEncryptBinaryKitSlotEnvExact W A' w1R.B w1R.x)
        w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel
        (cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel
        (cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B w2R.x)
        w2DecSigExactGrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
              PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) :=
  hJoin
    (g5ar_mkNonPrekeyCalleeEnvsSlotOf
      (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      (default : Image) (cliRunSemD3 W) defaultExtrasF3 W)
    (g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_curried
      (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      (default : Image) (cliRunSemD3 W) defaultExtrasF3 W
      hEncCredit hEncGrp hDecSigCredit hDecSigGrp)
    (g5ar_d3_nonPrekey_runEnvExact_sub_nonPrekeyKit
      (default : Image) (cliRunSemD3 W) defaultExtrasF3 W A)

/-- Slot- and cap-parametric `MainEntryBudgetFitsCapOf` reducer over arbitrary `sEnvs`,
`EncSlot`, `DecSigSlot`, and `(enc*, decSig*)` caps. -/
theorem g5ar_hole_g5a_of_slots_caps
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat}
    (hJoin : g5ar_PrekeyJoinReducer W sEnvs)
    (hs_init : sEnvs.initiate = realCliInitBinarySlotEnvFixed W := by rfl)
    (hs_enc : sEnvs.encrypt = EncSlot A cliRunBudgets_placed := by rfl)
    (hs_ds : sEnvs.decryptSignal = DecSigSlot A cliRunBudgets_placed := by rfl)
    (hEncLp : encLive ≤ encPeak)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel
        (EncSlot A' w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel
        (EncSlot A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel
        (DecSigSlot A' w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel
        (DecSigSlot A' w2R.B w2R.x) decSigGrpS)
    (hinit_grp :
      234 * FineScale + w3InitExactGrpS ≤
        cliRunOpenedCustomPksmGrpS msgCapBytes
          (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS
          encGrpS decSigGrpS 0 -
        15 * FineScale)
    (hram :
      cliDecoupledRamNeed cliDefaultStaticBytes
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      cliOneGiB)
    (hva :
      cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
        (exactMainCumOf encCum decSigCum 0)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak 0 0)
        (exactMainReqOf encMaxReq decSigMaxReq 0)
        ((exactMainGrpSOf encGrpS decSigGrpS 0 + FineScale - 1) / FineScale) ≤
      2 ^ 48) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) :=
  hJoin
    (g5ar_mkNonPrekeyCalleeEnvsSlotOf
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W)
    (g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_curried_caps
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W
      hEncLp hDecSigLp hEncCredit hEncGrp hDecSigCredit hDecSigGrp hinit_grp hram hva)
    (g5ar_d3_nonPrekey_runEnv_of_slots_sub_nonPrekeyKit
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W A sEnvs
      hs_init hs_enc hs_ds)

/-- Specialization of `g5ar_hole_g5a_of_slots_caps` to `w1EncExact*` and `w2DecSigExact*`. -/
theorem g5ar_hole_g5a_of_slots
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (sEnvs : RunSlotEnvs)
    (hJoin : g5ar_PrekeyJoinReducer W sEnvs)
    (hs_init : sEnvs.initiate = realCliInitBinarySlotEnvFixed W := by rfl)
    (hs_enc : sEnvs.encrypt = EncSlot A cliRunBudgets_placed := by rfl)
    (hs_ds : sEnvs.decryptSignal = DecSigSlot A cliRunBudgets_placed := by rfl)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel
        (EncSlot A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel
        (EncSlot A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel
        (DecSigSlot A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A' : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel
        (DecSigSlot A' w2R.B w2R.x) w2DecSigExactGrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) :=
  hJoin
    (g5ar_mkNonPrekeyCalleeEnvsSlotOf
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W)
    (g5ar_nonPrekeyMain_fitsEnv_cliBudgetLimits_of_curried
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W
      hEncCredit hEncGrp hDecSigCredit hDecSigGrp)
    (g5ar_d3_nonPrekey_runEnv_of_slots_sub_nonPrekeyKit
      EncSlot DecSigSlot (default : Image) (cliRunSemD3 W) defaultExtrasF3 W A sEnvs
      hs_init hs_enc hs_ds)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach
