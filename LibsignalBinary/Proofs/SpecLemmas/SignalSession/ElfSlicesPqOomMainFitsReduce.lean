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
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut

/-!
# Slot- and Cap-Parametric Whole-`main` `FitsEnv` Reducers

**Checked by Lean.**

Reduces whole-`main` `FitsEnv fineCostModel cliBudgetLimits` on
`realCliMainBinaryKitEnvOfExact` to per-slot `PhaseCreditSpec` and `PhaseGroupSpec`
obligations on the four `signal_session::run` callees (`init`, `encrypt`, `decryptSignal`,
and `decryptPrekey`) together with decidable `1 GiB` RAM and `2 ^ 48` VA cap checks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomMainFitsReduce

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost PksmGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (argv_length_le_of_cliPqInputs)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (m5PhaseEnv_groupSpec m6Env_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (binaryKitSlotInit_fineSpec exactCeilingMain_fits_oneGiB w1EncExactCum w1EncExactGrpS
   w1EncExactLive w1EncExactMaxReq w1EncExactPeak w2DecSigExactCum w2DecSigExactGrpS
   w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak w3InitExactCum w3InitExactGrpS
   w3InitExactLive w3InitExactMaxReq w3InitExactPeak w4DecPkExactCum w4DecPkExactGrpS
   w4DecPkExactLive w4DecPkExactMaxReq w4DecPkExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (phaseCredit_or_freeOnly_left)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv OptStageEnv RealCliMainBinaryEnvOf cliMainArmEnvs
   cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
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
   mkBinaryKitRealCalleeEnvsSlotOf realCliMainBinaryKitEnvOfSlot realCliRunBinaryKitEnvOfSlot)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (mkBinaryKitRealCalleeEnvsFixed realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (cliRunBinaryEnv_fine_groupSpec_of_cap d3RecvW4Ext_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (ValidPostSetupWitness cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive
   pksmCanonSliceLive_le_peak pksmCanonSliceMaxReq pksmCanonSlicePeak
   pksmCanonSlice_fine_groupSpec pksmCanonSlice_fine_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)

/-! ## Target Abbreviations, 4-Slot Callee Bundle, and `1 GiB` Cap Predicates -/

/-- Whole-`main` binary-kit allocator trace predicate at `cliEncryptBinaryKitSlotEnvExact` and `cliDecryptSignalBinaryKitSlotEnvExact`. -/
noncomputable abbrev mfr_realCliMainBinaryKitEnvOfExact [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  realCliMainBinaryKitEnvOfSlot
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W i

/-- Mode-dispatched 4-slot `CliRunCalleeEnvs` bundle parametric in `InitEnvOf`, `EncSlot`, `DecSigSlot`, and `DecPkSlot`, with `pksmEnv := PksmCanonSliceEnv`. -/
noncomputable def mfr_mkFourSlotCalleeEnvs
    (InitEnvOf : RunCall → List AllocEvent → Prop)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (g : RunCall) : CliRunCalleeEnvs where
  initEnv := InitEnvOf g
  encEnv := match g.c with
    | .send _ => fun evs =>
      ∃ (M : AllocCostModel) (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
        w1R.repAlloc = A.repAlloc ∧
        W1BinarySendDom g.c g.i w1R ∧
        EncSlot A w1R.B w1R.x evs
    | _ => fun _ => False
  decSigEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ (M : AllocCostModel) (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
        w2R.repAlloc = A.repAlloc ∧
        W2BinaryWhisperDom g.c g.i w2R ∧
        DecSigSlot A w2R.B w2R.x evs
    | _ => fun _ => False
  pksmEnv := PksmCanonSliceEnv
  decPkEnv := match g.c with
    | .recv peerV => fun evs =>
      ∃ (meV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        g.i.stdin = 3#8 :: rest ∧
        pksmParse rest = some pm ∧
        pm.message.ciphertext.length ≤ msgCapBytes ∧
        DecPkSlot (r3bDecPkGhost g meV peerV pm) evs
    | _ => fun _ => False

theorem mfr_mkFourSlotCalleeEnvs_eq_slotOf [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    mfr_mkFourSlotCalleeEnvs
      (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
      EncSlot DecSigSlot (cliDecPkCanonSlotEnvExact X W) =
    mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W :=
  rfl

/-- Whole-`main` cumulative byte cap `Δcum` from 4-slot callee caps. -/
def mfr_fourSlotMainCumOf (initCum encCum decSigCum decPkCum : Nat) : Nat :=
  let runCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) initCum encCum decSigCum decPkCum
  123250 + m3PhaseDeltaCum_tight + runCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

/-- Whole-`main` net live byte cap `Δlive` from 4-slot callee caps. -/
def mfr_fourSlotMainLiveOf (initLive encLive decSigLive decPkLive : Nat) : Nat :=
  cliMainTightLiveOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) initLive encLive decSigLive decPkLive)

/-- Whole-`main` peak live byte cap `Δpeak` from 4-slot callee caps. -/
def mfr_fourSlotMainPeakOf
    (initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak : Nat) : Nat :=
  cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) initLive encLive decSigLive decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
      initPeak encLive encPeak decSigPeak decPkPeak)

/-- Whole-`main` maximum single-allocation request `maxReq` from 4-slot callee caps. -/
def mfr_fourSlotMainReqOf (initMaxReq encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max (max (16 * 2048) 16384)
    (cliMainTightReqOf
      (cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes) initMaxReq encMaxReq decSigMaxReq decPkMaxReq))

/-- Whole-`main` scaled mallocng group count `grpS` from 4-slot callee caps. -/
def mfr_fourSlotMainGrpSOf (initGrpS encGrpS decSigGrpS decPkGrpS : Nat) : Nat :=
  let runGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) initGrpS encGrpS decSigGrpS decPkGrpS +
    27 * FineScale
  cliMainWidenedSetupFineGrpS + runGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

/-- Decidable `1 GiB` physical RAM and `2 ^ 48` VA side-condition predicate for 4-slot caps. -/
abbrev mfr_fourSlotMainFitsOneGiBOf
    (initCum initLive initPeak initMaxReq initGrpS
     encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) : Prop :=
  234 * FineScale + initGrpS ≤
    cliRunOpenedCustomPksmGrpS msgCapBytes
      (pksmCanonSliceGrpS msgCapBytes) initGrpS encGrpS decSigGrpS decPkGrpS -
    15 * FineScale ∧
  cliDecoupledRamNeed cliDefaultStaticBytes
    (mfr_fourSlotMainCumOf initCum encCum decSigCum decPkCum)
    (mfr_fourSlotMainPeakOf
      initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
    (mfr_fourSlotMainReqOf initMaxReq encMaxReq decSigMaxReq decPkMaxReq)
    ((mfr_fourSlotMainGrpSOf initGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤
  cliOneGiB ∧
  cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
    (mfr_fourSlotMainCumOf initCum encCum decSigCum decPkCum)
    (mfr_fourSlotMainPeakOf
      initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
    (mfr_fourSlotMainReqOf initMaxReq encMaxReq decSigMaxReq decPkMaxReq)
    ((mfr_fourSlotMainGrpSOf initGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤
  2 ^ 48

instance mfr_instDecidableFourSlotMainFitsOneGiBOf
    (initCum initLive initPeak initMaxReq initGrpS
     encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) :
    Decidable
      (mfr_fourSlotMainFitsOneGiBOf
        initCum initLive initPeak initMaxReq initGrpS
        encCum encLive encPeak encMaxReq encGrpS
        decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
        decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS) :=
  inferInstance

/-- Decidable 3-slot `1 GiB` RAM and `2 ^ 48` VA side-condition predicate with W3 fixed at `w3InitExact*`. -/
abbrev mfr_slotMainFitsOneGiBOf
    (encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) : Prop :=
  mfr_fourSlotMainFitsOneGiBOf
    w3InitExactCum w3InitExactLive w3InitExactPeak w3InitExactMaxReq w3InitExactGrpS
    encCum encLive encPeak encMaxReq encGrpS
    decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
    decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS

/-- Closed `1 GiB` RAM and `2 ^ 48` VA witness at the `@128` ceiling (`890,381,872 B ≤ 1,073,741,824 B`). -/
theorem mfr_slotMainFitsOneGiBOf_exactCeiling :
    mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4DecPkExactCum w4DecPkExactLive w4DecPkExactPeak w4DecPkExactMaxReq w4DecPkExactGrpS :=
  exactCeilingMain_fits_oneGiB

/-! ## Monotonicity and Optional-Stage Credit/Group Helpers -/

private theorem mfr_max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem mfr_optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem mfr_optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## W3 (`initEnv`) Slot Dischargers -/

/-- `PhaseCreditSpec` for `(mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv` under `CliPqxdhInputs`. -/
theorem mfr_w3InitFixed_phaseCredit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseCreditSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
      w3InitExactCum w3InitExactLive w3InitExactPeak w3InitExactMaxReq :=
  (binaryKitSlotInit_fineSpec
    (fun {_M} _A _B _x _evs => False)
    (fun {_M} _A _B _x _evs => False)
    img S X W g hi_g).credit

theorem mfr_w3InitExact_live_le_peak : w3InitExactLive ≤ w3InitExactPeak := by
  decide

/-- `PhaseGroupSpec` for `(mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv` under `CliPqxdhInputs`. -/
theorem mfr_w3InitFixed_groupSpec [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseGroupSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
      w3InitExactGrpS :=
  (binaryKitSlotInit_fineSpec
    (fun {_M} _A _B _x _evs => False)
    (fun {_M} _A _B _x _evs => False)
    img S X W g hi_g).groups

/-! ## Core 4-Slot Whole-`main` `FitsEnv` Reducer -/

/-- Core 4-slot whole-`main` `FitsEnv` reducer at `cliBudgetLimits` under `CliPqxdhInputs`,
discharging outer `main` setup/commit stages and `PksmCanonSliceEnv` internally. -/
theorem mfr_fourSlotMain_fitsEnv_cliBudgetLimits_of_caps
    (W : CliHooks) (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (InitEnvOf : RunCall → List AllocEvent → Prop)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    {initCum initLive initPeak initMaxReq initGrpS
     encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hInitCredit : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      g.i.stdin.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (InitEnvOf g) initCum initLive initPeak initMaxReq)
    (hInitLp : initLive ≤ initPeak)
    (hInitGrp : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      g.i.stdin.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (InitEnvOf g) initGrpS)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkCum decPkLive decPkPeak decPkMaxReq)
    (hDecPkLp : decPkLive ≤ decPkPeak)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkGrpS)
    (hFits : mfr_fourSlotMainFitsOneGiBOf
      initCum initLive initPeak initMaxReq initGrpS
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (RealCliMainBinaryEnvOf
        (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot) i) := by
  obtain ⟨hinit_grp, hram0, hva0⟩ := hFits
  let rCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) initCum encCum decSigCum decPkCum
  let rLive := cliRun1MiBCustomPksmLive
    (pksmCanonSliceLive msgCapBytes) initLive encLive decSigLive decPkLive
  let rPeak := cliRun1MiBCustomPksmPeak
    (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
    initPeak encLive encPeak decSigPeak decPkPeak
  let rMaxReq := cliRunBinary1MiBCustomPksmMaxReq
    (pksmCanonSliceMaxReq msgCapBytes) initMaxReq encMaxReq decSigMaxReq decPkMaxReq
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) initGrpS encGrpS decSigGrpS decPkGrpS
  let mkSE (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
      (hin : g.i.stdin.length ≤ msgCapBytes) :
      CliRealCalleeFineSpecs
        (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot g) :=
    { initCum := initCum
      initLive := initLive
      initPeak := initPeak
      initMaxReq := initMaxReq
      initGrpS := initGrpS
      init_spec := hInitCredit g hi_g hparse hin
      init_lp := hInitLp
      init_grp := hInitGrp g hi_g hparse hin
      encCum := encCum
      encLive := encLive
      encPeak := encPeak
      encMaxReq := encMaxReq
      encGrpS := encGrpS
      enc_spec := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hin hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hin hgc hrep hdom).credit_le st0 he }
      enc_lp := hEncLp
      enc_grp := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncGrp g peerV M A w1R hi_g hp hin hgc hrep hdom).groups_le st0 he }
      decSigCum := decSigCum
      decSigLive := decSigLive
      decSigPeak := decSigPeak
      decSigMaxReq := decSigMaxReq
      decSigGrpS := decSigGrpS
      decSig_spec := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hin hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hin hgc hrep hdom).credit_le st0 he }
      decSig_lp := hDecSigLp
      decSig_grp := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigGrp g peerV M A w2R hi_g hp hin hgc hrep hdom).groups_le st0 he }
      pksmCum := pksmCanonSliceCum msgCapBytes
      pksmLive := pksmCanonSliceLive msgCapBytes
      pksmPeak := pksmCanonSlicePeak msgCapBytes
      pksmMaxReq := pksmCanonSliceMaxReq msgCapBytes
      pksmGrpS := pksmCanonSliceGrpS msgCapBytes
      pksm_spec := fun _ hrest => pksmCanonSlice_fine_phaseCredit hrest
      pksm_lp := pksmCanonSliceLive_le_peak msgCapBytes
      pksm_grp := fun _ hrest => pksmCanonSlice_fine_groupSpec hrest
      decPkCum := decPkCum
      decPkLive := decPkLive
      decPkPeak := decPkPeak
      decPkMaxReq := decPkMaxReq
      decPkGrpS := decPkGrpS
      decPk_spec := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkCredit g peerV meV rest pm hi_g hp hin hgc hst hpk hct).req_align evs he
              credit_le := fun st0 {_} ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkCredit g peerV meV rest pm hi_g hp hin hgc hst hpk hct).credit_le st0 he }
      decPk_lp := hDecPkLp
      decPk_grp := by
        dsimp only [mfr_mkFourSlotCalleeEnvs]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkGrp g peerV meV rest pm hi_g hp hin hgc hst hpk hct).groups_le st0 he } }
  have hsm1024 :
      1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (CliRunBinaryEnv cliIo.rd
          (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot w.g)
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
    let SE := mkSE w.g hi_g w.parse_ok w.stdin_le
    have hrun :=
      cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs SE hi_g w.stdin_le w.parse_ok
    refine (hrun.seq
      ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
        (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact mfr_max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact mfr_max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot w.g)
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
      (RealCliMainBinaryEnvOf
        (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot) i)
      (mfr_fourSlotMainCumOf initCum encCum decSigCum decPkCum)
      (mfr_fourSlotMainLiveOf initLive encLive decSigLive decPkLive)
      (mfr_fourSlotMainPeakOf
        initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
      (mfr_fourSlotMainReqOf initMaxReq encMaxReq decSigMaxReq decPkMaxReq) := by
    refine ((cliMainBoundedSetup_phaseCredit_fine
        (argv_length_le_of_cliPqInputs hi)).seq
      (mfr_optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold mfr_fourSlotMainCumOf
      dsimp only [rCum]
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold mfr_fourSlotMainLiveOf cliMainTightLiveOf cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold mfr_fourSlotMainPeakOf cliMainTightPeakOf cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold mfr_fourSlotMainReqOf cliMainTightReqOf cliMainMaxReq
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
            (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      ((rGrpS + 27 * FineScale) +
        cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let SE := mkSE w.g hi_g w.parse_ok w.stdin_le
        have h15 : 15 * FineScale ≤ rGrpS := by
          dsimp only [rGrpS]
          unfold cliRunOpenedCustomPksmGrpS
          exact Nat.le_add_right (15 * FineScale) _
        have hrun :=
          cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le h15 hinit_grp (Nat.le_refl rGrpS)
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv
              (CliRunBinaryEnv cliIo.rd
                (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            ((rGrpS + 27 * FineScale) +
              cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf
        (mfr_mkFourSlotCalleeEnvs InitEnvOf EncSlot DecSigSlot DecPkSlot) i)
      (mfr_fourSlotMainGrpSOf initGrpS encGrpS decSigGrpS decPkGrpS) :=
    ((cliMainBoundedSetup_fine_groupSpec
        (argv_length_le_of_cliPqInputs hi)).seq
      (mfr_optStage_groupSpec hex_grp)).mono
      (by unfold mfr_fourSlotMainGrpSOf
          dsimp only [rGrpS]
          generalize FineScale = fs; omega)
  have hlp :
      mfr_fourSlotMainLiveOf initLive encLive decSigLive decPkLive ≤
      mfr_fourSlotMainPeakOf
        initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak := by
    unfold mfr_fourSlotMainLiveOf mfr_fourSlotMainPeakOf
      cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  have hcap1G : cliOneGiB ≤ cliBudgetLimits.physCap := by
    unfold cliBudgetLimits cliOneGiB
    decide
  have hram :
      cliDecoupledRamNeed cliBudgetLimits.staticBytes
        (mfr_fourSlotMainCumOf initCum encCum decSigCum decPkCum)
        (mfr_fourSlotMainPeakOf
          initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (mfr_fourSlotMainReqOf initMaxReq encMaxReq decSigMaxReq decPkMaxReq)
        ((mfr_fourSlotMainGrpSOf initGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) /
          FineScale) ≤
      cliBudgetLimits.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  have hva :
      cliDecoupledVaNeed cliBudgetLimits.staticBytes cliBudgetLimits.staticCount
        (mfr_fourSlotMainCumOf initCum encCum decSigCum decPkCum)
        (mfr_fourSlotMainPeakOf
          initLive initPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (mfr_fourSlotMainReqOf initMaxReq encMaxReq decSigMaxReq decPkMaxReq)
        ((mfr_fourSlotMainGrpSOf initGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) /
          FineScale) ≤
      2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

/-! ## Specialized Reducers for `realCliMainBinaryKitEnvOfExact` -/

/-- 4-slot + 20-cap whole-`main` `FitsEnv` reducer for `realCliMainBinaryKitEnvOfExact`. -/
theorem mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_four_slots_caps [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (InitEnvOf : RunCall → List AllocEvent → Prop)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    {initCum initLive initPeak initMaxReq initGrpS
     encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hs_init : (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv) = InitEnvOf := by rfl)
    (hs_enc :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliEncryptBinaryKitSlotEnvExact W A B) = @EncSlot := by rfl)
    (hs_ds :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliDecryptSignalBinaryKitSlotEnvExact W A B) = @DecSigSlot := by rfl)
    (hs_dp : cliDecPkCanonSlotEnvExact X W = DecPkSlot := by rfl)
    (hInitCredit : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      g.i.stdin.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (InitEnvOf g) initCum initLive initPeak initMaxReq)
    (hInitLp : initLive ≤ initPeak)
    (hInitGrp : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      g.i.stdin.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (InitEnvOf g) initGrpS)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkCum decPkLive decPkPeak decPkMaxReq)
    (hDecPkLp : decPkLive ≤ decPkPeak)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkGrpS)
    (hFits : mfr_fourSlotMainFitsOneGiBOf
      initCum initLive initPeak initMaxReq initGrpS
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (mfr_realCliMainBinaryKitEnvOfExact img S X W i) := by
  have hmain :=
    mfr_fourSlotMain_fitsEnv_cliBudgetLimits_of_caps W i hi
      InitEnvOf EncSlot DecSigSlot DecPkSlot
      hInitCredit hInitLp hInitGrp
      hEncCredit hEncLp hEncGrp
      hDecSigCredit hDecSigLp hDecSigGrp
      hDecPkCredit hDecPkLp hDecPkGrp
      hFits
  subst hs_init
  subst hs_enc
  subst hs_ds
  subst hs_dp
  exact hmain

/-- 3-slot + 15-cap whole-`main` `FitsEnv` reducer discharging W3 (`initEnv`) and `PksmCanonSliceEnv` internally. -/
theorem mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_slots_caps [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hs_enc :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliEncryptBinaryKitSlotEnvExact W A B) = @EncSlot := by rfl)
    (hs_ds :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliDecryptSignalBinaryKitSlotEnvExact W A B) = @DecSigSlot := by rfl)
    (hs_dp : cliDecPkCanonSlotEnvExact X W = DecPkSlot := by rfl)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkCum decPkLive decPkPeak decPkMaxReq)
    (hDecPkLp : decPkLive ≤ decPkPeak)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkGrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (mfr_realCliMainBinaryKitEnvOfExact img S X W i) :=
  mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_four_slots_caps img S X W i hi
    (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
    EncSlot DecSigSlot DecPkSlot
    rfl hs_enc hs_ds hs_dp
    (fun g hi_g _ _ => mfr_w3InitFixed_phaseCredit img S X W g hi_g)
    mfr_w3InitExact_live_le_peak
    (fun g hi_g _ _ => mfr_w3InitFixed_groupSpec img S X W g hi_g)
    hEncCredit hEncLp hEncGrp
    hDecSigCredit hDecSigLp hDecSigGrp
    hDecPkCredit hDecPkLp hDecPkGrp
    hFits

/-- Specializes W1 and W2 to `w1EncExact*` and `w2DecSigExact*` while keeping W4 (`DecPkSlot` and its 5 caps) parametric. -/
theorem mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_w4_caps [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    {w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat}
    (hs_enc :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliEncryptBinaryKitSlotEnvExact W A B) = @EncSlot := by rfl)
    (hs_ds :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliDecryptSignalBinaryKitSlotEnvExact W A B) = @DecSigSlot := by rfl)
    (hs_dp : cliDecPkCanonSlotEnvExact X W = DecPkSlot := by rfl)
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
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        w4GrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (mfr_realCliMainBinaryKitEnvOfExact img S X W i) :=
  mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_slots_caps img S X W i hi
    EncSlot DecSigSlot DecPkSlot hs_enc hs_ds hs_dp
    (fun g peerV M A w1R hi_g hp _hin hgc hrep hdom =>
      hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom)
    (Nat.le_refl _)
    (fun g peerV M A w1R hi_g hp _hin hgc hrep hdom =>
      hEncGrp g peerV M A w1R hi_g hp hgc hrep hdom)
    (fun g peerV M A w2R hi_g hp _hin hgc hrep hdom =>
      hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom)
    (Nat.le_refl _)
    (fun g peerV M A w2R hi_g hp _hin hgc hrep hdom =>
      hDecSigGrp g peerV M A w2R hi_g hp hgc hrep hdom)
    hDecPkCredit hDecPkLp hDecPkGrp hFits

/-- Specializes `mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_w4_caps` to `w4DecPkExact*`, leaving the six curried W1/W2/W4 credit and group obligations. -/
theorem mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_curried [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (hs_enc :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliEncryptBinaryKitSlotEnvExact W A B) = @EncSlot := by rfl)
    (hs_ds :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliDecryptSignalBinaryKitSlotEnvExact W A B) = @DecSigSlot := by rfl)
    (hs_dp : cliDecPkCanonSlotEnvExact X W = DecPkSlot := by rfl)
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
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactCum w4DecPkExactLive w4DecPkExactPeak w4DecPkExactMaxReq)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactGrpS) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (mfr_realCliMainBinaryKitEnvOfExact img S X W i) :=
  mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_w4_caps img S X W i hi
    EncSlot DecSigSlot DecPkSlot hs_enc hs_ds hs_dp
    hEncCredit hEncGrp hDecSigCredit hDecSigGrp
    hDecPkCredit d3RecvW4Ext_live_le_peak hDecPkGrp
    mfr_slotMainFitsOneGiBOf_exactCeiling

/-- Variant accepting `SingleSlotFineSpec` witnesses for `encrypt`, `decryptSignal`, and `decryptPrekey`. -/
theorem mfr_realCliMainBinaryKitEnvOfExact_fitsEnv_of_singleSlots [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hs_enc :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliEncryptBinaryKitSlotEnvExact W A B) = @EncSlot := by rfl)
    (hs_ds :
      (fun {M : AllocCostModel} (A : RustCliAllocBudget M) (B : RunBudgets) =>
        cliDecryptSignalBinaryKitSlotEnvExact W A B) = @DecSigSlot := by rfl)
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
    (S_decPk : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
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
    (hDecPkCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sp := S_decPk g hi_g hparse
      sp.cum ≤ decPkCum ∧ sp.live ≤ decPkLive ∧ sp.peak ≤ decPkPeak ∧
      sp.maxReq ≤ decPkMaxReq ∧ sp.grpS ≤ decPkGrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS := by decide) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (mfr_realCliMainBinaryKitEnvOfExact img S X W i) := by
  obtain ⟨hinit_grp, hram0, hva0⟩ := hFits
  have hcap1G : cliOneGiB ≤ cliBudgetLimits.physCap := by
    unfold cliBudgetLimits cliOneGiB
    decide
  have hram :
      cliDecoupledRamNeed cliBudgetLimits.staticBytes
        (mfr_fourSlotMainCumOf w3InitExactCum encCum decSigCum decPkCum)
        (mfr_fourSlotMainPeakOf
          w3InitExactLive w3InitExactPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (mfr_fourSlotMainReqOf w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq)
        ((mfr_fourSlotMainGrpSOf w3InitExactGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) /
          FineScale) ≤
      cliBudgetLimits.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  have hva :
      cliDecoupledVaNeed cliBudgetLimits.staticBytes cliBudgetLimits.staticCount
        (mfr_fourSlotMainCumOf w3InitExactCum encCum decSigCum decPkCum)
        (mfr_fourSlotMainPeakOf
          w3InitExactLive w3InitExactPeak encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (mfr_fourSlotMainReqOf w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq)
        ((mfr_fourSlotMainGrpSOf w3InitExactGrpS encGrpS decSigGrpS decPkGrpS + FineScale - 1) /
          FineScale) ≤
      2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  have hslot :=
    LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact.realCliMainBinaryKitEnvOfSlot_fitsEnv_of_caps
      (lim := cliBudgetLimits) rfl EncSlot DecSigSlot img S X W S_enc S_decSig S_decPk
      hEncCaps hDecSigCaps hDecPkCaps hinit_grp hram hva i hi
  subst hs_enc
  subst hs_ds
  exact hslot

/-! ## Combined `RunEnv` Inclusion and Whole-`main` `FitsEnv` -/

/-- Combines whole-`main` `FitsEnv` on `realCliMainBinaryKitEnvOfSlot` with whole-`run` `RunEnv` inclusion. -/
theorem mfr_runEnv_sub_and_mainFits_of_hmxSlotEnvs [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (DecPkSlot : DecPkGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (sEnvs : RunSlotEnvs)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hs_sEnvs : sEnvs =
      hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
        (realCliInitBinarySlotEnvFixed W) DecPkSlot := by rfl)
    (hs_dp : cliDecPkCanonSlotEnvExact X W = DecPkSlot := by rfl)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkCum decPkLive decPkPeak decPkMaxReq)
    (hDecPkLp : decPkLive ≤ decPkPeak)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.i.stdin.length ≤ msgCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel (DecPkSlot (r3bDecPkGhost g meV peerV pm))
        decPkGrpS)
    (hFits : mfr_slotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS := by decide) :
    (∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i)) ∧
    (∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      ∀ evs,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs (CanonicalOrFallbackPksmEnv FallbackEnv) S)
          g evs →
        realCliRunBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W g evs) := by
  subst hs_dp
  subst hs_sEnvs
  refine ⟨fun i hi => ?_, fun g hi_g hparse hin evs hevs =>
    hmx_runEnvExact_sub_runBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W A B
      hi_g hparse hin hS_enc hS_pksm evs hevs⟩
  exact mfr_fourSlotMain_fitsEnv_cliBudgetLimits_of_caps W i hi
    (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv)
    EncSlot DecSigSlot (cliDecPkCanonSlotEnvExact X W)
    (fun g hi_g _ _ => mfr_w3InitFixed_phaseCredit img S X W g hi_g)
    mfr_w3InitExact_live_le_peak
    (fun g hi_g _ _ => mfr_w3InitFixed_groupSpec img S X W g hi_g)
    hEncCredit hEncLp hEncGrp
    hDecSigCredit hDecSigLp hDecSigGrp
    hDecPkCredit hDecPkLp hDecPkGrp
    hFits

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomMainFitsReduce
