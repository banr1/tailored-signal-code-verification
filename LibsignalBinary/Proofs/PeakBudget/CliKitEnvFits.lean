/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux

/-!
# Binary-Kit Callee `SingleSlotFineSpec` and Whole-`main` `FitsEnv` Closure

Discharges `SingleSlotFineSpec` across all four binary-kit `signal_session::run` callee slots
(`W1`, `W2`, `W3Fixed`, `W4Fixed`), over-cap `ReadFileRuleEnvFixed` `Dir::get` bounds (`Δlive = 0`
on over-cap `.error ()`), and whole-`main` `FitsEnv fineCostModel` on
`RealCliMainBinaryEnvOf (mkBinaryKitCalleeEnvsWithDecPk ...)` and `realCliMainBinaryKitEnvOfFixed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runFiles)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W3BinaryInitDom W3BinaryInitParams mkBinaryKitRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (w3InitRealCum w3InitRealGrpS w3InitRealLive w3InitRealMaxReq w3InitRealPeak
   w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed mkBinaryKitRealCalleeEnvsFixed realCliMainBinaryKitEnvOfFixed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq d3RecvW4ExtPeak
   d3RecvW4Ext_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq
   w1SendRealDcanPeak w1SendRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcan_live_le_peak)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)

/-- Mode-dispatched `CliRunCalleeEnvs` bundle coinciding definitionally (`rfl`) with
`mkBinaryKitRealCalleeEnvsFixed` on `initEnv`, `encEnv`, `decSigEnv`, and `pksmEnv`, and
parametric in `decPkEnv`. -/
def mkBinaryKitCalleeEnvsWithDecPk [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop) (g : RunCall) : CliRunCalleeEnvs :=
  { mkBinaryKitRealCalleeEnvsFixed img S X W g with decPkEnv := decPkEnv g }

/-! ## Over-Cap `Dir::get` Credit and Group Bounds -/

section S1Helpers

open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (MmapThresholdReq)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec phaseGroupSpec_append_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit (specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCap cliIoCapEvents_readCaps_pos cliIoCapSeq cliIoStepLiveBound
   cliIoStepPeakBound cliIoTightCumBound req_align_cliIoCapSeq stepEvents_cliIoCapSeq_tight)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (DeallocCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (allocBytes1_fine_phaseCredit_tight optLargeCost_fine_of_le)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (readFileOverCapEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
   pathEnv_fine_phaseCredit_tight seq_freeOnly_phaseCredit)

private theorem readFileOverCapEvents_eq_seq9 :
    readFileOverCapEvents = cliIoCapSeq 9 ++ rustDeallocEvents 2097152 1 := by
  unfold readFileOverCapEvents
  rw [specCliIoReadSchedule_events_eq 9 2097152,
      cliIoCapEvents_readCaps_pos (K := 9) (r := 2097152) (by decide)]
  rfl

private theorem cliIoCapSeq9_fine_phaseCredit :
    PhaseCreditSpec fineCostModel (· = cliIoCapSeq 9)
      573818 (0 + HasFineReallocCredit.largeCost fineCostModel 2097152) 3162118 2097152 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoCapSeq 9
  credit_le := by
    rintro st0 _ rfl
    have h := stepEvents_cliIoCapSeq_tight fineCostModel
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      fineCostModel_modelHyps.hSmallAff
      fineCostModel_modelHyps.hLargeAff
      fineCostModel_modelHyps.hMeta st0 9
    dsimp only at h
    have hsm9 : ¬ (cliIoCap 9 ≤ HasFineReallocCredit.smallMaxReq fineCostModel) := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    unfold cliIoStepLiveBound at h
    simp only [hsm9, ↓reduceIte] at h
    have hc9 : cliIoTightCumBound 9 = 573818 := rfl
    have hp9 : cliIoStepPeakBound 9 = 3162118 := rfl
    have hcap9 : cliIoCap 9 = 2097152 := rfl
    rw [hc9, hp9, hcap9] at h
    simpa [Nat.zero_add] using h

private theorem readFileOverCapEvents_fine_phaseCredit :
    PhaseCreditSpec fineCostModel (· = readFileOverCapEvents)
      573818 0 3162118 2097152 := by
  have hfree := DeallocCreditSpec.free_large fineCostModel
    (req := 2097152) (al := 1) (by decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
  exact (cliIoCapSeq9_fine_phaseCredit.concat_dealloc_cancel hfree).of_imp fun _ h => by
    rw [h, readFileOverCapEvents_eq_seq9]
    exact ⟨cliIoCapSeq 9, rustDeallocEvents 2097152 1, rfl, rfl, rfl⟩

private theorem dirGetEnv_fixed_or (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) {evs : List AllocEvent}
    (h : DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name evs) :
    DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name evs ∨
      SeqEnv (DirGetPathEnv PathEnv dir.path name)
        (SeqEnv (· = readFileOverCapEvents)
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name))) evs := by
  unfold DirGetEnv at h ⊢
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    rw [hfind] at h
    exact Or.inl h
  | none =>
    rw [hfind] at h
    unfold DirGetMissEnv at h ⊢
    rcases h with hp | ⟨e1, e2, rfl, hp, h2⟩
    · exact Or.inl (Or.inl hp)
    · rcases h2 with hr | ⟨e2a, e2b, rfl, hr, ha⟩
      · rcases hr with hr0 | ⟨_, _, heq⟩
        · exact Or.inl (Or.inr ⟨e1, e2, rfl, hp, Or.inl hr0⟩)
        · exact Or.inr (Or.inr ⟨e1, e2, rfl, hp, Or.inl heq⟩)
      · rcases hr with hr0 | ⟨_, _, heq⟩
        · exact Or.inl (Or.inr ⟨e1, e2a ++ e2b, rfl, hp, Or.inr ⟨e2a, e2b, rfl, hr0, ha⟩⟩)
        · exact Or.inr (Or.inr ⟨e1, e2a ++ e2b, rfl, hp, Or.inr ⟨e2a, e2b, rfl, heq, ha⟩⟩)

private theorem dirGetAfterReadEnv_fine_phaseCredit (rd : ReadRule) (F0 : FsFiles)
    (pth : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirGetAfterReadEnv rd F0 pth) 738 0 0 22 := by
  unfold DirGetAfterReadEnv DirGetErrAllocEnv
  cases rd F0 pth with
  | ok _ =>
    exact (seq_freeOnly_phaseCredit fineCostModel_freeNonInc
      (PhaseCreditSpec.nil fineCostModel)).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | error u =>
    cases u
    have ha22 := PhaseCreditSpec.rustAlloc_small fineCostModel
      (req := 22) (al := 1) (by decide) (by decide)
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
    have hc22 : HasFineReallocCredit.smallAllocCost fineCostModel 22 ≤ 738 := by
      have h738 := rustAllocTightCum_fine_le_738 (req := 22) (by decide)
      unfold rustAllocTightCum at h738
      rw [fineCostModel_smallMaxReq_eq] at h738
      simpa using h738
    exact seq_freeOnly_phaseCredit fineCostModel_freeNonInc
      (ha22.mono hc22 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22))

private theorem s1a_aux
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    let fc := max maxVal fileCap
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (21185 + max (573818 + 738) (fineReadFileCum fc))
      (fineReadFileLive fc)
      (max 3162118 (fineReadFilePeak fc))
      (max 2097152 (fineReadFileMaxReq fc)) := by
  dsimp only
  have hBase := dirGetEnv_path_readFile_fine_phaseCredit_tight rd F0 dir name hdc hname hcap
  dsimp only at hBase
  have hp : PhaseCreditSpec fineCostModel
      (DirGetPathEnv PathEnv dir.path name) 21185 0 0 256 := by
    unfold DirGetPathEnv
    split_ifs
    · have hab := allocBytes1_fine_phaseCredit_tight hname
      rw [optLargeCost_fine_of_le (by decide)] at hab
      exact hab.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · exact pathEnv_fine_phaseCredit_tight hdc.path_len_le hname
  have hOver : PhaseCreditSpec fineCostModel
      (SeqEnv (DirGetPathEnv PathEnv dir.path name)
        (SeqEnv (· = readFileOverCapEvents)
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name))))
      595741 0 3162118 2097152 :=
    (hp.seq (readFileOverCapEvents_fine_phaseCredit.seq
      (dirGetAfterReadEnv_fine_phaseCredit rd F0 (pathOf dir.path name)))).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (PhaseCreditSpec.or_of_imp (fun _ => dirGetEnv_fixed_or rd F0 dir name) hBase hOver).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem cliIoCapSeq_groupSpec_9 (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M (· = cliIoCapSeq 9) (20 * FineScale) := by
  have step_any : ∀ {j : Nat} {g : Nat},
      PhaseGroupSpec M (· = cliIoCapSeq j) g →
      PhaseGroupSpec M (· = cliIoCapSeq (j + 1)) (g + 3 * FineScale) := by
    intro j g hj
    exact phaseGroupSpec_append_eq M hj
      (PhaseGroupSpec.rustRealloc_any M (cliIoCap j) (cliIoCap (j + 1)) 1)
  have step_large : ∀ {j : Nat} {g : Nat},
      MmapThresholdReq < cliIoCap (j + 1) →
      PhaseGroupSpec M (· = cliIoCapSeq j) g →
      PhaseGroupSpec M (· = cliIoCapSeq (j + 1)) (g + FineScale) := by
    intro j g hgt hj
    have hre : PhaseGroupSpec M
        (· = rustReallocEvents (cliIoCap j) (cliIoCap (j + 1)) 1) FineScale :=
      { groups_le := by
          rintro st0 _ rfl
          have hge : 1 ≤ cliIoCap (j + 1) := by omega
          unfold rustReallocEvents
          simp only [show (1 : Nat) ≤ 16 by decide, hge, and_self, ↓reduceIte,
            AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
          exact HasFineGroupCredit.step_large_le (M := M) st0
            (by simp [eventStepAlign])
            (by simpa [eventStepReq] using hgt) }
    exact phaseGroupSpec_append_eq M hj hre
  have h0 : PhaseGroupSpec M (· = cliIoCapSeq 0) (3 * FineScale) :=
    PhaseGroupSpec.rustAlloc_any M (cliIoCap 0) 1
  have h1 := step_any h0
  have h2 := step_any h1
  have h3 := step_any h2
  have h4 := step_any h3
  have h5 := step_large (by unfold MmapThresholdReq cliIoCap; decide) h4
  have h6 := step_large (by unfold MmapThresholdReq cliIoCap; decide) h5
  have h7 := step_large (by unfold MmapThresholdReq cliIoCap; decide) h6
  have h8 := step_large (by unfold MmapThresholdReq cliIoCap; decide) h7
  have h9 := step_large (by unfold MmapThresholdReq cliIoCap; decide) h8
  exact h9.mono (by omega)

private theorem s1b_aux (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (42 * FineScale) := by
  have hBase := dirGetEnv_path_readFile_groupSpec M rd F0 dir name
  have hPath : PhaseGroupSpec M (DirGetPathEnv PathEnv dir.path name) (9 * FineScale) := by
    unfold DirGetPathEnv
    split
    · exact (allocBytes1Events_groupSpec M name).mono (by omega)
    · unfold PathEnv pathEvents
      have p1 : PhaseGroupSpec M (· = pathToOwnedEvents dir.path.length) (3 * FineScale) := by
        unfold pathToOwnedEvents
        split
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
      have p2 : PhaseGroupSpec M (· = pathPushSlashEvents dir.path.length) (3 * FineScale) := by
        unfold pathPushSlashEvents
        split
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
      have p3 : PhaseGroupSpec M
          (· = pathAppendNameEvents dir.path.length name.length) (3 * FineScale) := by
        unfold pathAppendNameEvents
        dsimp only
        split
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
      exact (p1.concat (p2.concat p3)).of_imp (fun _ heq =>
        ⟨_, _, heq, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩) |>.mono (by omega)
  have hOverEvs : PhaseGroupSpec M (· = readFileOverCapEvents) (20 * FineScale) := by
    have h9 := cliIoCapSeq_groupSpec_9 M
    have hfr : PhaseGroupSpec M (· = rustDeallocEvents 2097152 1) 0 :=
      (PhaseGroupSpec.freeOnly M).of_imp fun _ h => by
        subst h; intro ev hev; unfold rustDeallocEvents at hev
        rw [List.mem_singleton] at hev; exact ⟨1, 2097152, hev⟩
    exact (phaseGroupSpec_append_eq M h9 hfr).of_imp
      (fun _ h => by rw [h, readFileOverCapEvents_eq_seq9]) |>.mono (by omega)
  have hAfter : PhaseGroupSpec M
      (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) (3 * FineScale) := by
    unfold DirGetAfterReadEnv DirGetErrAllocEnv
    cases rd F0 (pathOf dir.path name) with
    | ok _ =>
      exact ((PhaseGroupSpec.nil M).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)
    | error u =>
      cases u
      exact ((PhaseGroupSpec.rustAlloc_any M 22 1).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)
  have hOver : PhaseGroupSpec M
      (SeqEnv (DirGetPathEnv PathEnv dir.path name)
        (SeqEnv (· = readFileOverCapEvents)
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name))))
      (32 * FineScale) :=
    (hPath.seq (hOverEvs.seq hAfter)).mono (by omega)
  exact ((hBase.or hOver).of_imp (fun _ => dirGetEnv_fixed_or rd F0 dir name)).mono (by omega)

end S1Helpers

/-- Tight `fineCostModel` `PhaseCreditSpec` for `DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd`
(`Δlive = 0` on over-cap `.error ()` reads, `cum = 21185 + max (573818 + 738) (fineReadFileCum fc)`). -/
theorem dirGetEnv_path_readFileFixed_fine_phaseCredit_tight
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    let fc := max maxVal fileCap
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (21185 + max (573818 + 738) (fineReadFileCum fc))
      (fineReadFileLive fc)
      (max 3162118 (fineReadFilePeak fc))
      (max 2097152 (fineReadFileMaxReq fc)) := by
  exact s1a_aux rd F0 dir name hdc hname hcap

/-- `PhaseGroupSpec M` (`42 * FineScale`: `9` path + `30` over-cap/ok read + `3` err alloc) for
`DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd`. -/
theorem dirGetEnv_path_readFileFixed_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (42 * FineScale) := by
  exact s1b_aux M rd F0 dir name

/-! ## W1 (`send`) Binary-Kit Slot Bounds -/

section S2Helpers

open CryptoGames.LibsignalSession
  (Crypto IdentityKey Mut OutgoingTripleRatchet PublicKey
   SessionState ShaCompress SignalMessage SignalProtocolError Spqr aesCbcEncrypt liftE
   serializeContent)
open CryptoGames.LibsignalSessionApi
  (Direction KyberPayload PendingPreKey PreKeySignalMessage ProtoPreKeySignalMessage Session
   SessionRecord execOk)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (RecordRepr encodeRecord)
open CryptoVerification.E2E.RecordX (RecordInScopeP SessionScopeP)
open CryptoVerification.LibsignalProtoCodec
  (WireType encode encodeBytesField encodeKey encodeUint32Field encodeVarint protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost serializeAddrVals)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost addrBytes serializeAddresses serviceIdParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (addressText)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn scopeKit)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (cliDirPutEnv_groupSpec fine_rustAlloc_le_44 phaseGroupSpec_exists_guarded
   recordSerializeDomFineGrpS recordSerializeSeqFreeEnv_dom_fine_groupSpec
   withStoresEncTightEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams W1SendBinaryKitSlotEnv
   W2BinaryWhisperDom W2BinaryWhisperParams W2RecvWhisperBinaryKitSlotEnv
   decBinaryIdKitPlacedBudget decBinarySessKitPlacedBudget
   w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliDirPutEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (dirPut_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (optLargeCost rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
  (msgCapBytes sessionCapBytes spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
  (scopeIn_of_scopeKit_and_recordSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendTightCapEnv spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightMaxReq spqrSend_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
  (spqrSendTightCap_groupSpec spqrSendTightGroupS)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 RecordSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv
   peerSpqrStateTight640_of_cliPqInputs_send recordSpqrStateTight640_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_send topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (OtrEncryptStepEnv otrEncryptStep_creditSpec_small32)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (WithStoresEncTightEnv otrAfterNone otrAfterSome withStoresEncTight_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (peer_and_rem_name_le_40_of_send w1CtLenCap w1PkCumCap w1PkLiveCap w1PkOutCap w1PkPeakCap
   w1PkReqCap w1PostPqCap w1SigCumCap w1SigLiveCap w1SigPeakCap w1SigReqCap w1SmSerCap
   w1StoreEncCap)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordDecrypt_dom_phaseCredit_tight
   recordDecrypt_dom_phaseGroup recordSerializeMaxReq_le_of_dom recordSerializePeak_fine_le_of_dom
   recordSerializeTightCum_fine_le_of_dom sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
  (decryptRecord_post_caps_of_scopeIn encodeRecord_length_le_of_scopeKit
   opened_scopeAt_encodeRecord_le withStoresDec_fine_creditSpec_tight withStoresDec_phaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (W2RealTdEnv idPeers_rd_length_le_64_of_cliPqInputs_recv peer_and_rem_name_le_40_of_recv
   w2RealTdCum w2RealTdLive w2RealTdMaxReq w2RealTdPeak w2RealTd_fine_groupSpec
   w2RealTd_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewRawEnv fineCostModel_wireGroupHyps kyberPayloadLen preKeyMsgNewDeltaGrpS
   preKeyMsgNewRawDeltaCum preKeyMsgNewRawDeltaLive preKeyMsgNewRawDeltaPeak preKeyMsgNewRawMaxReq
   preKeyMsgNewRaw_phaseCredit preKeyMsgNewRaw_phaseGroup signalMessageNewDeltaCum
   signalMessageNewDeltaGrpS signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq signalMessageNewSerLen signalMessageNew_phaseCredit
   signalMessageNew_phaseGroup)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (pendingKyberPayload preKeyMsgFromItems)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (defaultLoadPollCancel2MiBCum defaultLoadPollCancelGrpS
   defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight
   defaultLoadPollEnv_dcan_byBytes_fine_groupSpec loadPollCancel2MiBLive
   loadPollCancel2MiBMaxReq loadPollCancel2MiBPeak)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_groupSpec addrTextValEnv_decimal_fine_phaseCredit_tight
   dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (OtrEncryptCoreEnv otrSignalMsgGhost)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv recordTryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

private theorem phaseCreditSpec_exists_guarded_local {α : Sort _}
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, P a → PhaseCreditSpec fineCostModel (E a) c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => ∃ a, P a ∧ E a evs) c l p r where
  req_align := fun evs ⟨a, ha, he⟩ => (h a ha).req_align evs he
  credit_le := fun st0 _ ⟨a, ha, he⟩ => (h a ha).credit_le st0 he

private theorem optLargeCost_fine_eq (n : Nat) :
    optLargeCost fineCostModel n = if n ≤ 135167 then 0 else n + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]

private theorem dirPutTailEnv_imp_cliDirPutEnv_of_empty {dir : DirGhost}
    (hch : dir.changed = []) (name bytes : List (BitVec 8)) {evs : List AllocEvent}
    (h : DirPutTailEnv dir name evs) :
    CliDirPutEnv dir name bytes evs := by
  unfold DirPutTailEnv at h
  rw [hch] at h
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte, List.length_nil] at h
  rcases h with rfl | rfl
  · exact Or.inl FreeOnlyEvs.nil
  · refine Or.inr ⟨⟨0#64, 0#64, 0#64, []⟩, ?_, rfl⟩
    rw [hch]
    decide

private theorem dirPutEnv_empty_credit_and_group {dir : DirGhost}
    (hch : dir.changed = []) (hdc : DirDomainCaps 64 0 0 dir)
    (name bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutEnv dir name bytes) 9085 0 0 384 ∧
    PhaseGroupSpec fineCostModel (DirPutEnv dir name bytes) (3 * FineScale) := by
  constructor
  · have hcr := dirPut_fine_phaseCredit_tight dir name bytes hdc
    exact hcr.of_imp (fun _ h => dirPutTailEnv_imp_cliDirPutEnv_of_empty hch name bytes h)
  · exact (cliDirPutEnv_groupSpec fineCostModel dir name bytes).of_imp
      (fun _ h => dirPutTailEnv_imp_cliDirPutEnv_of_empty hch name bytes h)

private theorem rustAlloc_small_40_credit {n : Nat} (hpos : 0 < n) (hn : n ≤ 40) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents n 1) 738 0 0 40 := by
  have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
    (req := n) (al := 1) (by decide) hpos
    (by rw [fineCostModel_smallMaxReq_eq]; omega)
  have hc : HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 738 := by
    have h1 := rustAllocTightCum_fine_le_738 (req := n) (Nat.le_trans hn (by decide))
    unfold rustAllocTightCum at h1
    rw [fineCostModel_smallMaxReq_eq] at h1
    have hle : n ≤ 135167 := Nat.le_trans hn (by decide)
    simpa [hle] using h1
  exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) hn

private theorem smallAllocCost_fine_le_9619_of_le_40 :
    ∀ n, 0 < n → n ≤ 40 → HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 9619 := by
  intro n _ hn
  have h1 := rustAllocTightCum_fine_le_738 (req := n) (Nat.le_trans hn (by decide))
  unfold rustAllocTightCum at h1
  rw [fineCostModel_smallMaxReq_eq] at h1
  have hle : n ≤ 135167 := Nat.le_trans hn (by decide)
  have h738 : HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 738 := by
    simpa [hle] using h1
  exact Nat.le_trans h738 (by decide)

private theorem dirPutStrEnv_empty_credit_and_group {dir : DirGhost}
    (hch : dir.changed = []) (hdc : DirDomainCaps 64 0 0 dir)
    (name bytes : List (BitVec 8)) (hname : name.length ≤ 40) :
    PhaseCreditSpec fineCostModel (DirPutStrEnv dir name bytes) 9823 0 0 384 ∧
    PhaseGroupSpec fineCostModel (DirPutStrEnv dir name bytes) (6 * FineScale) := by
  obtain ⟨hputCr, hputGrp⟩ := dirPutEnv_empty_credit_and_group hch hdc name bytes
  unfold DirPutStrEnv
  split_ifs with hnil
  · exact ⟨hputCr.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 384),
      hputGrp.mono (by decide)⟩
  · have hpos : 0 < name.length := List.length_pos_of_ne_nil hnil
    constructor
    · exact ((rustAlloc_small_40_credit hpos hname).seq hputCr).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact ((fine_rustAlloc_le_44 (by decide) (Nat.le_trans hname (by decide))).seq hputGrp).mono
        (by decide)

private theorem publicKeySerialize_credit_and_group :
    PhaseCreditSpec fineCostModel PublicKeySerializeEnv 738 0 0 33 ∧
    PhaseGroupSpec fineCostModel PublicKeySerializeEnv 16659 := by
  have heq : publicKeySerializeEvents = rustAllocEvents 33 1 := rfl
  unfold PublicKeySerializeEnv
  rw [heq]
  refine ⟨?_, fine_rustAlloc_le_44 (by decide) (by decide)⟩
  have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
    (req := 33) (al := 1) (by decide) (by decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
  have hc : HasFineReallocCredit.smallAllocCost fineCostModel 33 ≤ 738 := by
    change fineSmallAllocCost 33 ≤ 738
    decide
  exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)

private theorem dirDomainCaps_opened_peers_64 :
    DirDomainCaps 64 0 0 StoresGhost.opened.identity.peers := by
  have h := dirDomainCaps_opened_peers
  exact ⟨Nat.le_trans h.path_len_le (by decide), h.changed_len_le, h.changed_val_le⟩

private theorem dirDomainCaps_opened_sess_64 :
    DirDomainCaps 64 0 0 StoresGhost.opened.sessions := by
  have h := dirDomainCaps_opened_sess
  exact ⟨Nat.le_trans h.path_len_le (by decide), h.changed_len_le, h.changed_val_le⟩

private theorem fineReadFileLive_le_peak_of_any (fc : Nat) :
    fineReadFileLive fc ≤ fineReadFilePeak fc := by
  unfold fineReadFileLive fineReadFilePeak
  rw [optLargeCost_fine_eq]
  split_ifs <;> omega

private theorem binaryIdTrust_credit_and_group
    (F0 : FsFiles) (rem : AddrVal) (k : IdentityKey) (d : Direction)
    {fc : Nat} (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ fc) :
    PhaseCreditSpec fineCostModel
      (cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        F0 StoresGhost.opened.identity rem k d)
      (21185 + max 738 (fineReadFileCum (max 0 fc)))
      (fineReadFileLive (max 0 fc))
      (fineReadFilePeak (max 0 fc))
      (max 256 (fineReadFileMaxReq (max 0 fc))) ∧
    PhaseGroupSpec fineCostModel
      (cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        F0 StoresGhost.opened.identity rem k d)
      (39 * FineScale) := by
  unfold cliIdentityKitTrustPollEnv
  have hgetCr := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0
    StoresGhost.opened.identity.peers rem.name dirDomainCaps_opened_peers_64
    (Nat.le_trans hrem (by decide)) hcap
  have hgetGrp := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0
    StoresGhost.opened.identity.peers rem.name
  exact ⟨seq_freeOnly_phaseCredit fineCostModel_freeNonInc hgetCr,
    (hgetGrp.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))⟩

private theorem binaryIdSave_credit_and_group
    (F0 : FsFiles) (rem : AddrVal) (k : IdentityKey)
    {fc : Nat} (hrem : rem.name.length ≤ 40)
    (hcap : ∀ bs, cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ fc) :
    PhaseCreditSpec fineCostModel
      (cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv F0 StoresGhost.opened.identity rem k)
      ((21185 + max 738 (fineReadFileCum (max 0 fc))) + 10561)
      (fineReadFileLive (max 0 fc))
      (fineReadFilePeak (max 0 fc))
      (max (max 256 (fineReadFileMaxReq (max 0 fc))) 384) ∧
    PhaseGroupSpec fineCostModel
      (cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv F0 StoresGhost.opened.identity rem k)
      (48 * FineScale) := by
  unfold cliIdentityKitSavePollEnv
  have hgetCr := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0
    StoresGhost.opened.identity.peers rem.name dirDomainCaps_opened_peers_64
    (Nat.le_trans hrem (by decide)) hcap
  have hgetGrp := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0
    StoresGhost.opened.identity.peers rem.name
  obtain ⟨hpkCr, hpkGrp⟩ := publicKeySerialize_credit_and_group
  obtain ⟨hputCr, hputGrp⟩ :=
    dirPutStrEnv_empty_credit_and_group rfl dirDomainCaps_opened_peers_64 rem.name k.serialize hrem
  have htailCr : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      10561 0 0 384 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    | ok _ =>
      exact ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).seq (hpkCr.seq hputCr)).mono
        (by decide) (by decide) (by decide) (by decide)
  have htailGrp : PhaseGroupSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      (9 * FineScale) := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseGroupSpec.nil fineCostModel).mono (by decide)
    | ok _ =>
      exact ((PhaseGroupSpec.freeOnly fineCostModel).seq (hpkGrp.seq hputGrp)).mono (by decide)
  constructor
  · refine (hgetCr.seq htailCr).mono (Nat.le_refl _) ?_ ?_ (Nat.le_refl _)
    · rw [Nat.add_zero]
    · rw [Nat.add_zero]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, fineReadFileLive_le_peak_of_any (max 0 fc)⟩
  · exact (hgetGrp.seq htailGrp).mono (by decide)

private theorem binarySessStore_credit_and_group
    (rem : AddrVal) (r' : SessionRecord (List (BitVec 8)))
    {pqCap encCap : Nat}
    (hrem : rem.name.length ≤ 40)
    (hDom : ∀ ses, r'.currentSession = some ses → SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r').length ≤ encCap) :
    let serPeak := 1080975 + optLargeCost fineCostModel pqCap + optLargeCost fineCostModel encCap
    PhaseCreditSpec fineCostModel
      (cliSessionKitStorePollEnv (AddrTextValEnv DecimalEnv) RecordSerializeSeqFreeValidEnv
        DirPutEnv StoresGhost.opened.sessions rem r')
      (11265 + 8420940 + 9085)
      serPeak
      serPeak
      (max 384 (max (max 208000 pqCap) encCap)) ∧
    PhaseGroupSpec fineCostModel
      (cliSessionKitStorePollEnv (AddrTextValEnv DecimalEnv) RecordSerializeSeqFreeValidEnv
        DirPutEnv StoresGhost.opened.sessions rem r')
      (9 * FineScale + recordSerializeDomFineGrpS) := by
  intro serPeak
  have hadCr := addrTextValEnv_decimal_fine_phaseCredit_tight rem hrem
  have hadGrp := addrTextValEnv_decimal_fine_groupSpec rem hrem
  obtain ⟨hputCr, hputGrp⟩ :=
    dirPutEnv_empty_credit_and_group rfl dirDomainCaps_opened_sess_64 (addressText rem) (encodeRecord r')
  have hserCr : PhaseCreditSpec fineCostModel (RecordSerializeSeqFreeValidEnv r')
      8420940 serPeak serPeak (max (max 208000 pqCap) encCap) := by
    unfold RecordSerializeSeqFreeValidEnv
    refine phaseCreditSpec_exists_guarded_local fun g hgv => ?_
    have hValid : ∀ G ses, g.cur = some G → r'.currentSession = some ses →
        SessionGhostValid G ses ∧ SessionCloneDom pqCap ses :=
      fun G ses hg hr => ⟨by simpa [RecordGhostValid, hg, hr] using hgv, hDom ses hr⟩
    exact (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.PhaseCreditSpec.recordSerialize_seqFree_tight
      fineCostModel_modelHyps g r').mono
      (recordSerializeTightCum_fine_le_of_dom hValid)
      (recordSerializePeak_fine_le_of_dom hValid hEnc)
      (recordSerializePeak_fine_le_of_dom hValid hEnc)
      (recordSerializeMaxReq_le_of_dom hValid hEnc)
  have hserGrp : PhaseGroupSpec fineCostModel (RecordSerializeSeqFreeValidEnv r')
      recordSerializeDomFineGrpS := by
    unfold RecordSerializeSeqFreeValidEnv
    exact phaseGroupSpec_exists_guarded fineCostModel fun g hgv =>
      recordSerializeSeqFreeEnv_dom_fine_groupSpec hgv hDom
  unfold cliSessionKitStorePollEnv
  constructor
  · refine (hadCr.seq (hserCr.seq hputCr)).mono ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · exact Nat.max_le.mpr
        ⟨Nat.le_trans (by decide : 80 ≤ 384) (Nat.le_max_left _ _),
         Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_max_left _ _⟩⟩
  · exact (hadGrp.seq (hserGrp.seq hputGrp)).mono (by decide)

private theorem recordSpqrStateTight640_of_placedScopeAt [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {files : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hScAt : (CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.cliSessionStoreSpecPlaced
      A cliIo.rd files pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hState : PeerSpqrStateTight640 F K files rem) :
    RecordSpqrStateTight640 F K r :=
  recordSpqrStateTight640_of_cliSessionStoreSpec
    (A := A) (b := 0#64) (pathOk := pathOk) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) hScAt hState

private theorem encodeVarintAux_len_le_s2 : ∀ (fuel : Nat) (v : BitVec 64),
    (CryptoVerification.LibsignalProtoCodec.encodeVarintAux fuel v).length ≤ fuel
  | 0, _ => by simp [CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le_s2 k (v >>> 7)) 1

private theorem encodeVarint_len_le_s2 (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_len_le_s2 10 v

private theorem encodeKey_len_le_s2 (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_len_le_s2 _

private theorem encodeUint32Field_len_le_s2 (tag : Nat) (ov : Option (BitVec 32)) :
    (encodeUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := encodeKey_len_le_s2 tag .varint
    have h2 := encodeVarint_len_le_s2 (v.zeroExtend 64)
    omega

private theorem encodeBytesField_some_len_le_s2 (tag : Nat) (bs : List (BitVec 8)) :
    (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
  simp only [encodeBytesField, List.length_append]
  have h1 := encodeKey_len_le_s2 tag .lengthDelimited
  have h2 := encodeVarint_len_le_s2 (BitVec.ofNat 64 bs.length)
  omega

private theorem serializeAddresses_len_36_s2 {loc rem : AddrGhost} {ad : List (BitVec 8)}
    (h : serializeAddresses (serviceIdParse uuidTryParse) loc rem = some ad) :
    ad.length = 36 := by
  unfold serializeAddresses at h
  rcases hs : serviceIdParse uuidTryParse loc.name.bytes with _ | vs <;> rw [hs] at h
  · cases h
  · dsimp only [bind, Option.bind] at h
    rcases hr : serviceIdParse uuidTryParse rem.name.bytes with _ | vr <;> rw [hr] at h
    · cases h
    · simp only [pure, Option.some.injEq] at h
      subst h
      simp only [addrBytes, List.length_append, List.length_cons, List.Vector.toList_length,
        List.length_nil]

private theorem exec_pure_s2 {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

private theorem exec_throw_s2 {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem exec_get_s2 {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem exec_set_s2 {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

private theorem exec_modifyGet_s2 {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

private theorem exec_liftE_s2 {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

private theorem exec_map_s2 {σ α β : Type} (f : α → β) (m : Mut σ α) (s : σ) :
    Mut.exec (f <$> m) s = (f <$> (Mut.exec m s).1, (Mut.exec m s).2) := by
  unfold Mut.exec
  change (ExceptT.run (f <$> m)).run s = _
  rw [ExceptT.run_map]
  simp only [StateT.run_map]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem exec_bind_s2 {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

private theorem spqr_encodeVarintLoop_len_le_s2 :
    ∀ (fuel : Nat) (a : BitVec 64),
      (CryptoVerification.LibsignalSpqrV1.encodeVarintLoop fuel a).length ≤ fuel
  | 0, _ => by simp [CryptoVerification.LibsignalSpqrV1.encodeVarintLoop]
  | k + 1, a => by
    unfold CryptoVerification.LibsignalSpqrV1.encodeVarintLoop
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (spqr_encodeVarintLoop_len_le_s2 k (a >>> 7)) 1

private theorem spqr_encode_varint_len_le_s2 (a : BitVec 64) (into : List (BitVec 8)) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint a into).length ≤ into.length + 10 := by
  unfold CryptoVerification.LibsignalSpqrV1.encode_varint
    CryptoVerification.LibsignalSpqrV1.MAX_VARINT_BYTES_LEN
  rw [List.length_append]
  exact Nat.add_le_add_left (spqr_encodeVarintLoop_len_le_s2 10 a) into.length

private theorem spqr_msgSerialize_len_le_64_s2
    (m : CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi)
    (index : BitVec 32) :
    (m.serialize index).length ≤ 64 := by
  rcases m with ⟨epoch, payload⟩
  unfold CryptoVerification.LibsignalSpqrV1.Message.serialize
  dsimp only
  set tag : BitVec 8 := (CryptoVerification.LibsignalSpqrV1.MessageType.from_payload payload).toU8
  have h1 := spqr_encode_varint_len_le_s2 epoch [1#8]
  have h2 := spqr_encode_varint_len_le_s2 (index.zeroExtend 64)
    (CryptoVerification.LibsignalSpqrV1.encode_varint epoch [1#8])
  have hlen1 : ([1#8] : List (BitVec 8)).length = 1 := rfl
  cases payload with
  | none | ct1Ack _ =>
    simp only [List.length_append, List.length_singleton]
    omega
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    unfold CryptoVerification.LibsignalSpqrV1.encode_chunk
    have h3 := spqr_encode_varint_len_le_s2
      ((CryptoVerification.LibsignalSpqrV1.spqrPolyApi.chunkIndex c).zeroExtend 64)
      (CryptoVerification.LibsignalSpqrV1.encode_varint (index.zeroExtend 64)
        (CryptoVerification.LibsignalSpqrV1.encode_varint epoch [1#8]) ++ [tag])
    have hc : (CryptoVerification.LibsignalSpqrV1.spqrPolyApi.chunkData c).toList.length = 32 :=
      List.Vector.toList_length _
    simp only [List.length_append, List.length_singleton, hc] at h3 ⊢
    omega

private theorem spqrV1Send_msg_len_le_s2 (F : ShaCompress) (K : MlKem)
    (st tape st' : List (BitVec 8)) (salt : CryptoGames.HKDF.Salt) (pm : List (BitVec 8))
    (h : (spqrV1 F K).send st tape = some (st', salt, pm)) :
    pm.length ≤ 64 := by
  rw [CryptoVerification.LibsignalSpqrV1.spqrV1_eq] at h
  simp only [CryptoVerification.LibsignalSpqrV1.toSpqrModel] at h
  rcases hs : (CryptoVerification.LibsignalSpqrV1.send
      (CryptoVerification.LibsignalSpqrV1.spqrDeps F K)
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) st tape).1 with _ | s
  · rw [hs] at h; cases h
  · rw [hs] at h; dsimp only at h
    rcases hk : CryptoVerification.LibsignalSpqrV1.messageKeyToSalt? s.key with _ | salt'
    · rw [hk] at h; cases h
    · rw [hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      unfold CryptoVerification.LibsignalSpqrV1.send at hs
      rcases hdec : CryptoVerification.LibsignalSpqrV1.decodeState
          (CryptoVerification.LibsignalSpqrV1.spqrDeps F K) st with _ | statePb <;>
        rw [hdec] at hs
      · cases hs
      · dsimp only at hs
        rcases hinner : statePb.inner with _ | pb <;> rw [hinner] at hs
        · simp only [Except.ok.injEq] at hs; subst hs; simp
        · dsimp only at hs
          rcases hst0 : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).statesFromPb pb
              with _ | st0 <;> rw [hst0] at hs
          · cases hs
          · dsimp only at hs
            rcases hsendRes : ((CryptoVerification.LibsignalSpqrV1.spqrDeps F K).8 st0 tape).1
                with _ | ⟨msg, key, st1⟩ <;> rw [hsendRes] at hs
            · cases hs
            · dsimp only at hs
              unfold CryptoVerification.LibsignalSpqrV1.sendAfterStates at hs
              rcases hch : statePb.chain with _ | pbChain <;> rw [hch] at hs
              · rcases hvn : statePb.versionNegotiation with _ | vn <;> rw [hvn] at hs
                · dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
                  cases hs
                · dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
                  split at hs
                  · rcases hcv : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError
                        (CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
                          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) vn)
                      with _ | c <;> rw [hcv] at hs
                    · cases hs
                    · try dsimp only at hs
                      rcases key with _ | es <;> try dsimp only at hs
                      · split at hs
                        · cases hs
                        · rcases hsk : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
                              (CryptoVerification.LibsignalSpqrV1.Chain.sendKey
                                (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c
                                ((CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgEpoch msg - 1#64))
                            with _ | v <;> rw [hsk] at hs
                          · cases hs
                          · try dsimp only at hs
                            rcases hser : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgSerialize msg v.2.1
                              with _ | ⟨b0, tl⟩ <;> rw [hser] at hs
                            · cases hs
                            · try dsimp only at hs
                              split at hs
                              · cases hs
                              · simp only [Except.ok.injEq] at hs; subst hs; dsimp only; rw [← hser]
                                exact spqr_msgSerialize_len_le_64_s2 msg v.2.1
                      · rcases hae : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic
                            (CryptoVerification.LibsignalSpqrV1.Chain.addEpoch
                              (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c es)
                          with _ | c1 <;> rw [hae] at hs
                        · cases hs
                        · try dsimp only at hs
                          split at hs
                          · cases hs
                          · rcases hsk : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
                                (CryptoVerification.LibsignalSpqrV1.Chain.sendKey
                                  (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c1
                                  ((CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgEpoch msg - 1#64))
                              with _ | v <;> rw [hsk] at hs
                            · cases hs
                            · try dsimp only at hs
                              rcases hser : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgSerialize msg v.2.1
                                with _ | ⟨b0, tl⟩ <;> rw [hser] at hs
                              · cases hs
                              · try dsimp only at hs
                                split at hs
                                · cases hs
                                · simp only [Except.ok.injEq] at hs; subst hs; dsimp only; rw [← hser]
                                  exact spqr_msgSerialize_len_le_64_s2 msg v.2.1
                  · split at hs
                    · try dsimp only at hs
                      rcases hser : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgSerialize msg 0#32
                        with _ | ⟨b0, tl⟩ <;> rw [hser] at hs
                      · cases hs
                      · try dsimp only at hs
                        split at hs
                        · cases hs
                        · simp only [Except.ok.injEq] at hs; subst hs; dsimp only; rw [← hser]
                          exact spqr_msgSerialize_len_le_64_s2 msg 0#32
                    · cases hs
              · dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
                rcases hfp : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofError
                    (CryptoVerification.LibsignalSpqrV1.Chain.fromPb pbChain)
                  with _ | c <;> rw [hfp] at hs
                · cases hs
                · try dsimp only at hs
                  rcases key with _ | es <;> try dsimp only at hs
                  · split at hs
                    · cases hs
                    · rcases hsk : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
                          (CryptoVerification.LibsignalSpqrV1.Chain.sendKey
                            (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c
                            ((CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgEpoch msg - 1#64))
                        with _ | v <;> rw [hsk] at hs
                      · cases hs
                      · try dsimp only at hs
                        rcases hser : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgSerialize msg v.2.1
                          with _ | ⟨b0, tl⟩ <;> rw [hser] at hs
                        · cases hs
                        · try dsimp only at hs
                          split at hs
                          · cases hs
                          · simp only [Except.ok.injEq] at hs; subst hs; dsimp only; rw [← hser]
                            exact spqr_msgSerialize_len_le_64_s2 msg v.2.1
                  · rcases hae : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainPanic
                        (CryptoVerification.LibsignalSpqrV1.Chain.addEpoch
                          (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c es)
                      with _ | c1 <;> rw [hae] at hs
                    · cases hs
                    · try dsimp only at hs
                      split at hs
                      · cases hs
                      · rcases hsk : CryptoVerification.LibsignalSpqrV1.SpqrApiResult.ofChainResult
                            (CryptoVerification.LibsignalSpqrV1.Chain.sendKey
                              (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) c1
                              ((CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgEpoch msg - 1#64))
                          with _ | v <;> rw [hsk] at hs
                        · cases hs
                        · try dsimp only at hs
                          rcases hser : (CryptoVerification.LibsignalSpqrV1.spqrDeps F K).msgSerialize msg v.2.1
                            with _ | ⟨b0, tl⟩ <;> rw [hser] at hs
                          · cases hs
                          · try dsimp only at hs
                            split at hs
                            · cases hs
                            · simp only [Except.ok.injEq] at hs; subst hs; dsimp only; rw [← hser]
                              exact spqr_msgSerialize_len_le_64_s2 msg v.2.1

private theorem aesCbcEncrypt_len_eq_s2 (C : Crypto)
    (k : BitVec 256) (iv : BitVec 128) (ptext : List (BitVec 8)) :
    (aesCbcEncrypt C.E k iv ptext).length = 16 * (ptext.length / 16 + 1) := by
  have hblk : ∀ l : List (BitVec 128),
      (l.flatMap CryptoGames.CBC.blockToBytesLE).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons b t ih =>
      have hb : (CryptoGames.CBC.blockToBytesLE b).length = 16 := by
        simp [CryptoGames.CBC.blockToBytesLE]
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]
      omega
  unfold aesCbcEncrypt
  rw [hblk, List.Vector.toList_length]
  rfl

private theorem otrSignalMsgGhost_bounds_s2 (P : PEParams)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pqrKey : CryptoGames.HKDF.Salt) (pqrMsg ptext : List (BitVec 8))
    (loc? : Option AddrGhost) (rem : AddrGhost) (rest : List (BitVec 8))
    (hptext : ptext.length ≤ msgCapBytes)
    (hsend : (pqxdhSpqrModel P).spqr.send otr.pqrState rest = some (pq', pqrKey, pqrMsg)) :
    (otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext loc? rem).ciphertext.length ≤ w1CtLenCap ∧
    (otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext loc? rem).pqRatchet.length ≤ 4096 ∧
    signalMessageNewSerLen uuidTryParse
      (otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext loc? rem) ≤ w1SmSerCap := by
  set g := otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext loc? rem
  have hct_eq : g.ciphertext.length = 16 * (ptext.length / 16 + 1) := by
    dsimp only [g, otrSignalMsgGhost]
    exact aesCbcEncrypt_len_eq_s2 P.C
      ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F pqrKey).cipherKey
      ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F pqrKey).iv ptext
  have hct_le : g.ciphertext.length ≤ w1CtLenCap := by
    rw [hct_eq]
    unfold w1CtLenCap
    have hdiv : ptext.length / 16 ≤ msgCapBytes / 16 := Nat.div_le_div_right hptext
    omega
  have hpq64 : pqrMsg.length ≤ 64 :=
    spqrV1Send_msg_len_le_s2 P.C.F P.Q.K otr.pqrState rest pq' pqrKey pqrMsg hsend
  have hpqr_eq : g.pqRatchet = pqrMsg := rfl
  have hpq_le : g.pqRatchet.length ≤ 4096 := by
    rw [hpqr_eq]
    exact Nat.le_trans hpq64 (by decide)
  refine ⟨hct_le, hpq_le, ?_⟩
  unfold signalMessageNewSerLen CryptoVerification.LibsignalTripleRatchet.SignalMessageNewGhost.protoMsg encode
  simp only [List.length_append]
  have hrk : g.senderRatchetKey.serialize.length = 33 := by
    simp [PublicKey.serialize]
  have h1 := encodeBytesField_some_len_le_s2 1 g.senderRatchetKey.serialize
  have h2 := encodeUint32Field_len_le_s2 2 (some g.counter)
  have h3 := encodeUint32Field_len_le_s2 3 (some g.previousCounter)
  have h4 := encodeBytesField_some_len_le_s2 4 g.ciphertext
  have h5 : (encodeBytesField 5 (if g.pqRatchet.isEmpty then none else some g.pqRatchet)).length ≤
      20 + g.pqRatchet.length := by
    split <;> [simp [encodeBytesField]; exact encodeBytesField_some_len_le_s2 5 g.pqRatchet]
  have h6 : (encodeBytesField 6 (g.addresses uuidTryParse)).length ≤ 56 := by
    cases had : g.addresses uuidTryParse with
    | none => simp [encodeBytesField]
    | some ad =>
      have had36 : ad.length ≤ 36 := by
        dsimp only [g, otrSignalMsgGhost] at had
        unfold CryptoVerification.LibsignalTripleRatchet.SignalMessageNewGhost.addresses at had
        cases loc? with
        | none => cases had
        | some loc => exact Nat.le_of_eq (serializeAddresses_len_36_s2 had)
      have hb := encodeBytesField_some_len_le_s2 6 ad
      omega
  rw [hpqr_eq] at h5 ⊢
  unfold w1SmSerCap
  omega

private theorem otrEncryptCore_imp_step_s2 (P : PEParams)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (loc? : Option AddrGhost) (rem : AddrGhost) (rest : List (BitVec 8))
    (hptext : ptext.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : OtrEncryptCoreEnv P.C (pqxdhSpqrModel P) SpqrSendTightCapEnv uuidTryParse
      otr ptext loc? rem rest evs) :
    OtrEncryptStepEnv (SpqrSendTightCapEnv otr.pqrState rest) ptext.length
      (fun evs' =>
        ∃ g : SignalMessageNewGhost,
          (g.ciphertext.length ≤ w1CtLenCap ∧
            g.pqRatchet.length ≤ 4096 ∧
            signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap) ∧
          SignalMessageNewEnv uuidTryParse g evs') evs := by
  unfold OtrEncryptCoreEnv at h
  unfold OtrEncryptStepEnv
  rcases h with h1 | ⟨e1, e2, rfl, he1, he2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨e1, e2, rfl, he1, ?_⟩
    rcases hsend : (pqxdhSpqrModel P).send otr.pqrState rest with _ | ⟨pq', pqrKey, pqrMsg⟩ <;>
      rw [hsend] at he2
    · exact Or.inl (by rw [he2]; exact FreeOnlyEvs.nil)
    · refine Or.inr ?_
      rcases he2 with h2a | ⟨ea, eb, rfl, hea, heb⟩
      · exact Or.inl h2a
      · refine Or.inr ⟨ea, eb, rfl, hea, ?_⟩
        rcases heb with h2b | ⟨ec, ed, rfl, hec, hed⟩
        · exact Or.inl h2b
        · refine Or.inr ⟨ec, ed, rfl, hec, ?_⟩
          rcases hed with h2c | ⟨ee, ef, rfl, hee, hef⟩
          · exact Or.inl ⟨_, otrSignalMsgGhost_bounds_s2 P otr pq' pqrKey pqrMsg ptext loc? rem
              rest hptext hsend, h2c⟩
          · exact Or.inr ⟨ee, ef, rfl, ⟨_, otrSignalMsgGhost_bounds_s2 P otr pq' pqrKey pqrMsg ptext
              loc? rem rest hptext hsend, hee⟩, hef⟩

private theorem otrEncrypt_serialized_len_le_s2 (P : PEParams)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr otr' : OutgoingTripleRatchet (List (BitVec 8))) (msg : SignalMessage)
    (haddrs : ∀ ad, addrs = some ad → ad.length ≤ 36)
    (he : Mut.exec (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr
      ptext addrs coins) otr = (.ok msg, otr')) :
    msg.serialized.length ≤ ptext.length + 300 := by
  have heOk : execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr
      ptext addrs coins) otr = .ok (msg, otr') := by
    unfold execOk; rw [he]
  unfold OutgoingTripleRatchet.encrypt execOk at heOk
  simp only [exec_bind_s2, exec_get_s2] at heOk
  cases hpan : (pqxdhSpqrModel P).spqr.sendPanics otr.pqrState coins
  case true => simp [hpan, exec_throw_s2] at heOk
  simp only [hpan, Bool.false_eq_true, ↓reduceIte] at heOk
  rcases hs : (pqxdhSpqrModel P).spqr.send otr.pqrState coins with _ | ⟨pq', key, pm⟩
  · simp [hs, exec_throw_s2] at heOk
  · have hpmlen : pm.length ≤ 64 :=
      spqrV1Send_msg_len_le_s2 P.C.F P.Q.K otr.pqrState coins pq' key pm hs
    simp only [hs, exec_pure_s2, exec_bind_s2] at heOk
    rcases hn : otr.senderChainKey.nextChainKey P.C.F with _ | next
    · simp [hn, exec_liftE_s2] at heOk
    · simp only [hn, exec_liftE_s2, exec_set_s2,
        Except.ok.injEq, Prod.mk.injEq] at heOk
      rcases heOk with ⟨rfl, rfl⟩
      have had6 : (encodeBytesField 6 addrs).length ≤ 56 := by
        cases h_a : addrs with
        | none => simp [encodeBytesField]
        | some ad =>
          have h1 := encodeBytesField_some_len_le_s2 6 ad
          have h2 := haddrs ad h_a
          omega
      have hrk : otr.senderRatchetKey.publicKey.serialize.length = 33 := by
        simp [PublicKey.serialize]
      have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
          20 + pm.length := by
        split <;> [simp [encodeBytesField]; exact encodeBytesField_some_len_le_s2 5 pm]
      dsimp only [SignalMessage.new]
      rw [List.length_append]
      refine Nat.le_trans (Nat.add_le_add_left (List.length_take_le 8 _) _) ?_
      dsimp only [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode]
      simp only [List.length_append, List.length_cons]
      have h1 := encodeBytesField_some_len_le_s2 1 otr.senderRatchetKey.publicKey.serialize
      have h2 := encodeUint32Field_len_le_s2 2 (some otr.senderChainKey.index)
      have h3 := encodeUint32Field_len_le_s2 3 (some otr.previousCounter)
      have h4 := encodeBytesField_some_len_le_s2 4 (aesCbcEncrypt P.C.E
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv ptext)
      have h4' := aesCbcEncrypt_len_eq_s2 P.C
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv ptext
      omega

private theorem prost_varint_len_le_s2 (k : Nat) :
    ∀ n : Nat, n < 128 ^ (k + 1) →
      (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp [show n < 128 by omega]
  | succ k ih =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 * 128 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have := ih (n / 128) hdiv
      omega

private theorem prost_uint32Field_len_le_s2 {tag : Nat} (ht : tag ≤ 8) (v? : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag v?).length ≤ 10 := by
  cases v? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le_s2 0 (8 * tag + 0) (by omega)
    have h2 := prost_varint_len_le_s2 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_opt_len_le_s2 {tag : Nat} (ht : tag ≤ 8)
    (bs? : Option (List (BitVec 8))) (B : Nat)
    (hB : ∀ bs, bs? = some bs → bs.length ≤ B ∧ bs.length < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag bs?).length ≤ 10 + B := by
  cases hbs : bs? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]
  | some bs =>
    obtain ⟨hle, hlt⟩ := hB bs hbs
    simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le_s2 0 (8 * tag + 2) (by omega)
    have h2 := prost_varint_len_le_s2 4 bs.length (by omega)
    omega

private theorem preKeyMsgNew_serialized_len_le_s2
    (ver : BitVec 8) (regId : BitVec 32) (preKeyId : Option (BitVec 32)) (spk : BitVec 32)
    (kp : Option KyberPayload) (baseKey : PublicKey) (ik : IdentityKey) (msg : SignalMessage)
    (hkp : ∀ k, kp = some k → k.ciphertext.length ≤ 1569)
    (hmsg : msg.serialized.length < 2 ^ 32) :
    (PreKeySignalMessage.new ver regId preKeyId spk kp baseKey ik msg).serialized.length ≤
      msg.serialized.length + 1717 := by
  have hbk : baseKey.serialize.length = 33 := by
    simp [PublicKey.serialize]
  have hik : ik.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hf1 := prost_uint32Field_len_le_s2 (tag := 1) (by omega) preKeyId
  have hf2 := prost_bytesField_opt_len_le_s2 (tag := 2) (by omega)
    (some baseKey.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf3 := prost_bytesField_opt_len_le_s2 (tag := 3) (by omega)
    (some ik.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf4 := prost_bytesField_opt_len_le_s2 (tag := 4) (by omega)
    (some msg.serialized) msg.serialized.length (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; exact ⟨Nat.le_refl _, hmsg⟩)
  have hf5 := prost_uint32Field_len_le_s2 (tag := 5) (by omega) (some regId)
  have hf6 := prost_uint32Field_len_le_s2 (tag := 6) (by omega) (some spk)
  have hf7 := prost_uint32Field_len_le_s2 (tag := 7) (by omega) (kp.map (·.preKeyId))
  have hf8 := prost_bytesField_opt_len_le_s2 (tag := 8) (by omega)
    (kp.map (·.ciphertext)) 1569 (by
      intro bs hbs
      rcases h_k : kp with _ | k <;> rw [h_k] at hbs
      · cases hbs
      · simp only [Option.map_some, Option.some.injEq] at hbs
        subst hbs
        have hlen := hkp k h_k
        omega)
  simp only [PreKeySignalMessage.new, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  omega

private abbrev W1OtrStepLocal (_P : PEParams) (x : WithStoresEncGhost)
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8))) :
    List AllocEvent → Prop :=
  OtrEncryptStepEnv (SpqrSendTightCapEnv otr.pqrState x.rest) x.ptext.length
    (fun evs' =>
      ∃ g : SignalMessageNewGhost,
        (g.ciphertext.length ≤ w1CtLenCap ∧
          g.pqRatchet.length ≤ 4096 ∧
          signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap) ∧
        SignalMessageNewEnv uuidTryParse g evs')

private abbrev W1PkRawLocal
    (_r : SessionRecord (List (BitVec 8))) (_sess : Session (List (BitVec 8)))
    (_otr : OutgoingTripleRatchet (List (BitVec 8))) (_taken : SessionState (List (BitVec 8)))
    (evs' : List AllocEvent) : Prop :=
  ∃ kp : Option KyberPayload, ∃ smLen outLen : Nat,
    (kyberPayloadLen kp ≤ 1569 ∧ smLen ≤ w1SmSerCap ∧ outLen ≤ w1PkOutCap) ∧
    PreKeyMsgNewRawEnv kp smLen outLen evs'

private theorem w1SendBinaryKitSlotEnv_imp_tight [LibsignalPlacement]
    (P : PEParams) (R : W1BinarySendParams)
    (hptext : (w1EncGhost R.x).ptext.length ≤ msgCapBytes) {evs : List AllocEvent}
    (h : W1SendBinaryKitSlotEnv P R evs) :
    WithStoresEncTightEnv scopeKit
      (w1SessKitPlaced R.repAlloc R.B R.x.F R.x.peer)
      (w1BinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
      StoresGhost.opened.sessions
      (w1IdKitPlaced R.repAlloc R.B R.x.F R.x.peer)
      (w1BinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
      StoresGhost.opened.identity
      P.C (pqxdhSpqrModel P) uuidTryParse (w1EncGhost R.x)
      (W1OtrStepLocal P (w1EncGhost R.x))
      (W1OtrStepLocal P (w1EncGhost R.x))
      W1PkRawLocal evs := by
  set x := w1EncGhost R.x
  unfold W1SendBinaryKitSlotEnv at h
  unfold LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.WithStoresEncEnv at h
  unfold WithStoresEncTightEnv LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments.WithStoresEncSegEnv
  rcases h with hL | ⟨eL, eR, rfl, heL, heR⟩
  · exact Or.inl hL
  · refine Or.inr ⟨eL, eR, rfl, heL, ?_⟩
    rcases heR with hF | hSc | hCur
    · exact Or.inl hF
    · exact Or.inr (Or.inl hSc)
    · refine Or.inr (Or.inr ?_)
      rcases hCur with hF1 | ⟨eF, eO, rfl, heF, heO⟩
      · exact Or.inl hF1
      · refine Or.inr ⟨eF, eO, rfl, heF, ?_⟩
        rcases heO with hF2 | ⟨r, sess, otr, taken, hsc, hcur, hfrom, hFromOtr⟩
        · exact Or.inl hF2
        · refine Or.inr ⟨r, sess, otr, taken, hsc, hcur, hfrom, ?_⟩
          rcases hFromOtr with hF3 | ⟨k, hk, hFromKey⟩
          · exact Or.inl hF3
          · refine Or.inr ⟨k, hk, ?_⟩
            obtain ⟨_, s0, hs0, hSessP⟩ := hsc.1
            have hs_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
            subst s0
            rcases hFromKey with ⟨hnone, hSeqNone⟩ | ⟨items, hsome, hClone | hPkSeq⟩
            · refine Or.inl ⟨hnone, ?_⟩
              rcases hSeqNone with hO1 | ⟨ea, eb, rfl, hea, heb⟩
              · exact Or.inl (otrEncryptCore_imp_step_s2 P otr x.ptext none x.rem x.rest hptext hO1)
              · exact Or.inr ⟨ea, eb, rfl,
                  otrEncryptCore_imp_step_s2 P otr x.ptext none x.rem x.rest hptext hea, heb⟩
            · refine Or.inr ⟨by simp [hsome], Or.inl hClone⟩
            · refine Or.inr ⟨by simp [hsome], Or.inr ?_⟩
              have hkybEq : ∀ evsK,
                  LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.KyberOptEnv
                    (sess.pendingKyberPreKey.map (·.ciphertext)) evsK →
                  LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments.KyberOptStepEnv
                    (sess.pendingKyberPreKey.map (·.ciphertext)) evsK := by
                intro evsK
                cases sess.pendingKyberPreKey with
                | none => exact fun hk0 => hk0
                | some _ => exact fun hk0 => hk0
              rcases hPkSeq with hK0 | ⟨ek, eRest, rfl, hek, heRest⟩
              · exact Or.inl (hkybEq _ hK0)
              · refine Or.inr ⟨ek, eRest, rfl, hkybEq _ hek, ?_⟩
                have hPostImp : ∀ evsP,
                    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv
                      P.C (pqxdhSpqrModel P) uuidTryParse
                      (w1SessKitPlaced R.repAlloc R.B R.x.F R.x.peer)
                      (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
                        (w1BinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer))
                      StoresGhost.opened.sessions
                      (w1IdKitPlaced R.repAlloc R.B R.x.F R.x.peer)
                      (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
                        (w1BinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer))
                      StoresGhost.opened.identity x sess otr taken k items evsP →
                    FreeOnlyEvs evsP ∨
                    SeqEnv (W1PkRawLocal r sess otr taken)
                      (fun evs'' =>
                        FreeOnlyEvs evs'' ∨
                        LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak.FromCmTightEnv
                          (w1SessKitPlaced R.repAlloc R.B R.x.F R.x.peer)
                          (w1BinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
                          StoresGhost.opened.sessions
                          (w1IdKitPlaced R.repAlloc R.B R.x.F R.x.peer)
                          (w1BinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer)
                          StoresGhost.opened.identity x.rem.val x.rem.name sess
                          (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr) taken k evs'')
                      evsP := by
                  intro evsP hp
                  unfold LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv at hp
                  dsimp only at hp
                  rcases hp with hfp | hp2
                  · exact Or.inl hfp
                  · rcases hres : Mut.exec (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                        (pqxdhSpqrModel P).spqr x.ptext
                        (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest) otr
                      with ⟨err | sm, otr'⟩ <;> rw [hres] at hp2
                    · exact False.elim hp2
                    · dsimp only at hp2
                      have hkpCap : ∀ k0, pendingKyberPayload sess = some k0 →
                          k0.ciphertext.length ≤ 1569 := by
                        intro k0 hk0
                        unfold pendingKyberPayload at hk0
                        rcases hsk : sess.pendingKyberPreKey with _ | kp0 <;> rw [hsk] at hk0
                        · cases hk0
                        · simp only [Option.map_some, Option.some.injEq] at hk0
                          subst hk0
                          exact Nat.le_trans (Nat.le_of_eq (hSessP.2.2.1 kp0 hsk)) (by decide)
                      have hkpLen : kyberPayloadLen (pendingKyberPayload sess) ≤ 1569 := by
                        cases hpkp : pendingKyberPayload sess with
                        | none => decide
                        | some k0 => exact hkpCap k0 hpkp
                      have hsm300 : sm.serialized.length ≤ x.ptext.length + 300 :=
                        otrEncrypt_serialized_len_le_s2 P x.ptext
                          (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest
                          otr otr' sm (fun ad had => Nat.le_of_eq (serializeAddresses_len_36_s2 had))
                          hres
                      have hsmCap : sm.serialized.length ≤ w1SmSerCap := by
                        unfold w1SmSerCap w1CtLenCap
                        omega
                      have hsmLt32 : sm.serialized.length < 2 ^ 32 := by
                        have : w1SmSerCap < 2 ^ 32 := by
                          unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
                        omega
                      have hout1717 :
                          (preKeyMsgFromItems sess items otr' sm).serialized.length ≤
                            sm.serialized.length + 1717 :=
                        preKeyMsgNew_serialized_len_le_s2 otr'.sessionVersion
                          sess.localRegistrationId items.preKeyId items.signedPreKeyId
                          (pendingKyberPayload sess) items.baseKey otr'.localIdentityKey sm
                          hkpCap hsmLt32
                      have houtCap :
                          (preKeyMsgFromItems sess items otr' sm).serialized.length ≤ w1PkOutCap := by
                        unfold w1PkOutCap
                        omega
                      have hotrAfter : otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr = otr' := by
                        unfold otrAfterSome
                        rw [hres]
                      refine Or.inr ?_
                      rw [hotrAfter]
                      rcases hp2 with hpL | ⟨ep1, ep2, rfl, hep1, hep2⟩
                      · exact Or.inl ⟨pendingKyberPayload sess, sm.serialized.length,
                          (preKeyMsgFromItems sess items otr' sm).serialized.length,
                          ⟨hkpLen, hsmCap, houtCap⟩, hpL⟩
                      · exact Or.inr ⟨ep1, ep2, rfl,
                          ⟨pendingKyberPayload sess, sm.serialized.length,
                            (preKeyMsgFromItems sess items otr' sm).serialized.length,
                            ⟨hkpLen, hsmCap, houtCap⟩, hep1⟩,
                          hep2⟩
                rcases heRest with hO2 | ⟨eo, ep, rfl, heo, hep⟩
                · exact Or.inl (otrEncryptCore_imp_step_s2 P otr x.ptext (some x.loc) x.rem x.rest
                    hptext hO2)
                · exact Or.inr ⟨eo, ep, rfl,
                    otrEncryptCore_imp_step_s2 P otr x.ptext (some x.loc) x.rem x.rest hptext heo,
                    hPostImp ep hep⟩

private theorem fromSessionState_pqr_and_taken_s2
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    otr.pqrState = st.pqRatchetState ∧ taken = { st with pqRatchetState := [] } := by
  unfold execOk OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc, exec_bind_s2, exec_get_s2, exec_throw_s2] at h
  · simp only [hsc, exec_bind_s2, exec_get_s2, exec_modifyGet_s2] at h
    split_ifs at h
    · simp [exec_throw_s2] at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem, exec_throw_s2] at h
      · simp only [hrem, exec_pure_s2, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        cases st
        dsimp only at hsc hrem
        subst hsc hrem
        rfl

private theorem otr_encrypt_topStateTight_s2
    {F : ShaCompress} {K : MlKem} (C : Crypto) (hF : C.F = F)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight F K otr.pqrState) :
    TopStateTight F K
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 F K).spqr
        ptext addrs coins) otr).2.pqrState := by
  subst hF
  have hcases :
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 C.F K).spqr
        ptext addrs coins) otr).2.pqrState = otr.pqrState ∨
      ∃ newPqr pqrKey pqrMsg,
        (spqrV1 C.F K).spqr.send otr.pqrState coins = some (newPqr, pqrKey, pqrMsg) ∧
        (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 C.F K).spqr
          ptext addrs coins) otr).2.pqrState = newPqr := by
    unfold OutgoingTripleRatchet.encrypt
    simp only [exec_bind_s2, exec_get_s2]
    cases (spqrV1 C.F K).spqr.sendPanics otr.pqrState coins
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases (spqrV1 C.F K).spqr.send otr.pqrState coins with _ | ⟨newPqr, pqrKey, pqrMsg⟩
      · left; simp [exec_throw_s2]
      · dsimp only [exec_pure_s2, exec_bind_s2]
        rcases otr.senderChainKey.nextChainKey C.F with _ | _
        · left; simp [exec_liftE_s2, exec_bind_s2]
        · right; refine ⟨newPqr, pqrKey, pqrMsg, rfl, ?_⟩
          simp [exec_liftE_s2, exec_bind_s2, exec_map_s2, exec_set_s2]
    · left; simp [exec_throw_s2]
  rcases hcases with heq | ⟨newPqr, _, _, hs, heq⟩
  · rw [heq]; exact hTop
  · rw [heq]; exact topStateTight_spqrV1_send hTop hs

private theorem storedRecord_bounds_s2
    {F : ShaCompress} {K : MlKem}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (hKit : scopeKit r)
    (hcur : r.currentSession = some sess)
    (htaken : taken = { sess.state with pqRatchetState := [] })
    (hTop' : TopStateTight F K otr'.pqrState) :
    (∀ ses, (storedRecord sess otr' taken).currentSession = some ses →
      SessionCloneDom w1PostPqCap ses) ∧
    (encodeRecord (storedRecord sess otr' taken)).length ≤ w1StoreEncCap := by
  subst htaken
  have hpqCap : otr'.pqrState.length ≤ w1PostPqCap := by
    have hle := topStateTight_length_le hTop'
    have heq : spqrStateTightCapBytes = w1PostPqCap := by
      unfold spqrStateTightCapBytes w1PostPqCap spqrSendTightMaxReq; decide
    rwa [heq] at hle
  have hotr'_lt32 : otr'.pqrState.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hpqCap (by unfold w1PostPqCap spqrSendTightMaxReq; decide)
  obtain ⟨⟨hInP, _, hRepr⟩, s0, hs0, hSessP⟩ := hKit
  have hsess_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
  subst hsess_eq
  have hInSess := hInP s0 hcur
  have hReprSess := hRepr s0 hcur
  have hRecIn' :
      RecordInScopeP (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    unfold OutgoingTripleRatchet.applyToSessionState
    exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
  have hRepr' :
      RecordRepr (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
    · intro sc' hsc'
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
      obtain ⟨sc, hsc0, rfl⟩ := hsc'
      exact hReprSess.2.1 sc hsc0
    · simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using hReprSess.2.2.1
  have hSessP' :
      SessionScopeP
        { s0 with state := otr'.applyToSessionState { s0.state with pqRatchetState := [] } } :=
    ⟨hSessP.1, hSessP.2.1, hSessP.2.2.1, hSessP.2.2.2⟩
  have hScope' :
      scopeKit (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    refine ⟨⟨hRecIn', ?_, hRepr'⟩, _, rfl, hSessP'⟩
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    exact hotr'_lt32
  have hPq' : ∀ ses,
      (storedRecord s0 otr' { s0.state with pqRatchetState := [] }).currentSession = some ses →
      ses.state.pqRatchetState.length ≤ w1PostPqCap := by
    intro ses hses
    simp only [storedRecord, Option.some.injEq] at hses
    subst hses
    exact hpqCap
  exact ⟨fun ses hses => sessionCloneDom_of_scopeKit_pq hScope' hses (hPq' ses hses),
    encodeRecord_length_le_of_scopeKit hScope' hPq'⟩

private theorem w1SigNew_guarded_credit_and_group :
    PhaseCreditSpec fineCostModel
      (fun evs' =>
        ∃ g : SignalMessageNewGhost,
          (g.ciphertext.length ≤ w1CtLenCap ∧
            g.pqRatchet.length ≤ 4096 ∧
            signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap) ∧
          SignalMessageNewEnv uuidTryParse g evs')
      w1SigCumCap w1SigLiveCap w1SigPeakCap w1SigReqCap ∧
    PhaseGroupSpec fineCostModel
      (fun evs' =>
        ∃ g : SignalMessageNewGhost,
          (g.ciphertext.length ≤ w1CtLenCap ∧
            g.pqRatchet.length ≤ 4096 ∧
            signalMessageNewSerLen uuidTryParse g ≤ w1SmSerCap) ∧
          SignalMessageNewEnv uuidTryParse g evs')
      signalMessageNewDeltaGrpS := by
  constructor
  · refine phaseCreditSpec_exists_guarded_local fun g ⟨hct, hpq, hser⟩ => ?_
    have h36 : 36 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
    have hct_sm : w1CtLenCap ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
    have hpq_sm : 4096 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
    refine (signalMessageNew_phaseCredit fineCostModel_modelHyps uuidTryParse g).mono ?_ ?_ ?_ ?_
    · unfold signalMessageNewDeltaCum w1SigCumCap
      omega
    · unfold signalMessageNewDeltaLive w1SigLiveCap
      omega
    · unfold signalMessageNewDeltaPeak w1SigPeakCap
      omega
    · unfold signalMessageNewMaxReq w1SigReqCap
      exact Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨h36, Nat.le_trans hct hct_sm⟩,
         Nat.max_le.mpr ⟨Nat.le_trans hpq hpq_sm, hser⟩⟩
  · exact phaseGroupSpec_exists_guarded fineCostModel
      (fun g _ => signalMessageNew_phaseGroup fineCostModel_wireGroupHyps uuidTryParse g)

private theorem w1PkRaw_guarded_credit_and_group :
    PhaseCreditSpec fineCostModel
      (fun evs' =>
        ∃ kp : Option KyberPayload, ∃ smLen outLen : Nat,
          (kyberPayloadLen kp ≤ 1569 ∧ smLen ≤ w1SmSerCap ∧ outLen ≤ w1PkOutCap) ∧
          PreKeyMsgNewRawEnv kp smLen outLen evs')
      w1PkCumCap w1PkLiveCap w1PkPeakCap w1PkReqCap ∧
    PhaseGroupSpec fineCostModel
      (fun evs' =>
        ∃ kp : Option KyberPayload, ∃ smLen outLen : Nat,
          (kyberPayloadLen kp ≤ 1569 ∧ smLen ≤ w1SmSerCap ∧ outLen ≤ w1PkOutCap) ∧
          PreKeyMsgNewRawEnv kp smLen outLen evs')
      preKeyMsgNewDeltaGrpS := by
  have hiff : ∀ evs',
      (∃ kp : Option KyberPayload, ∃ smLen outLen : Nat,
        (kyberPayloadLen kp ≤ 1569 ∧ smLen ≤ w1SmSerCap ∧ outLen ≤ w1PkOutCap) ∧
        PreKeyMsgNewRawEnv kp smLen outLen evs') →
      ∃ t : Option KyberPayload × Nat × Nat,
        (kyberPayloadLen t.1 ≤ 1569 ∧ t.2.1 ≤ w1SmSerCap ∧ t.2.2 ≤ w1PkOutCap) ∧
        PreKeyMsgNewRawEnv t.1 t.2.1 t.2.2 evs' :=
    fun _ ⟨kp, smLen, outLen, hb, he⟩ => ⟨⟨kp, smLen, outLen⟩, hb, he⟩
  have h33 : 33 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hkp_pk : 1569 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hsm_pk : w1SmSerCap ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  constructor
  · refine (phaseCreditSpec_exists_guarded_local fun t ⟨hkp, hsm, hout⟩ => ?_).of_imp hiff
    refine (preKeyMsgNewRaw_phaseCredit fineCostModel_modelHyps t.1 t.2.1 t.2.2).mono ?_ ?_ ?_ ?_
    · unfold preKeyMsgNewRawDeltaCum w1PkCumCap; omega
    · unfold preKeyMsgNewRawDeltaLive w1PkLiveCap; omega
    · unfold preKeyMsgNewRawDeltaPeak w1PkPeakCap; omega
    · unfold preKeyMsgNewRawMaxReq w1PkReqCap
      exact Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨Nat.le_trans hkp hkp_pk, h33⟩,
         Nat.max_le.mpr ⟨Nat.le_trans hsm hsm_pk, hout⟩⟩
  · exact (phaseGroupSpec_exists_guarded fineCostModel
      (fun t _ => preKeyMsgNewRaw_phaseGroup fineCostModel_wireGroupHyps t.1 t.2.1 t.2.2)).of_imp hiff

private theorem w1BinarySend_credit_and_groups [LibsignalPlacement]
    (P : PEParams) (i : Inputs) (peerAddr : AddrV) (R : W1BinarySendParams)
    (hi : CliPqxdhInputs P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peerAddr))
    (hdom : W1BinarySendDom (.send peerAddr) i R) :
    PhaseCreditSpec fineCostModel (W1SendBinaryKitSlotEnv P R)
      w1SendRealDcanCum w1SendRealDcanPeak w1SendRealDcanPeak
      w1SendRealDcanMaxReq ∧
    PhaseGroupSpec fineCostModel (W1SendBinaryKitSlotEnv P R)
      w1SendRealDcanGrpS := by
  obtain ⟨hpeerVal, _hxpeer, hrem, hptext, hF⟩ := hdom peerAddr rfl
  let x := w1EncGhost R.x
  obtain ⟨_hpeer40, hremName40⟩ := peer_and_rem_name_le_40_of_send hparse hpeerVal hrem
  have hremLen : x.rem.val.name.length ≤ 40 := hremName40
  have hTopRem : PeerSpqrStateTight640 P.C.F P.Q.K R.x.F x.rem.val := by
    rw [hF, hrem, hpeerVal]
    exact peerSpqrStateTight640_of_cliPqInputs_send hi hparse
  let kit := w1SessKitPlaced R.repAlloc R.B R.x.F R.x.peer
  let kitEnv := w1BinarySessKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer
  let ikit := w1IdKitPlaced R.repAlloc R.B R.x.F R.x.peer
  let ikitEnv := w1BinaryIdKitPlacedBudget R.repAlloc R.B R.x.F R.x.peer
  have hLoadCr : PhaseCreditSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val)
      defaultLoadPollCancel2MiBCum loadPollCancel2MiBLive
      loadPollCancel2MiBPeak loadPollCancel2MiBMaxReq :=
    defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight
      dirDomainCaps_opened_sess (by decide) hremLen
      (fun bs hbs => cliIo_rd_ok_length_le_sessionCapBytes R.x.F _ bs hbs)
      (by unfold sessionCapBytes; decide)
  have hLoadGrp : PhaseGroupSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val)
      defaultLoadPollCancelGrpS :=
    defaultLoadPollEnv_dcan_byBytes_fine_groupSpec hremLen
  have hIdCap : ∀ bs,
      cliIo.rd R.x.F (pathOf StoresGhost.opened.identity.peers.path x.rem.val.name) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hbs => cliIo_rd_ok_length_le_sessionCapBytes R.x.F _ bs hbs
  have hTrust := binaryIdTrust_credit_and_group R.x.F x.rem.val (fc := sessionCapBytes)
  have hSave := binaryIdSave_credit_and_group R.x.F x.rem.val (fc := sessionCapBytes)
  obtain ⟨hSigCr, hSigGrp⟩ := w1SigNew_guarded_credit_and_group
  obtain ⟨hPkCr, hPkGrp⟩ := w1PkRaw_guarded_credit_and_group
  have hct_le : (x.ptext.length / 16 + 1) * 16 ≤ w1CtLenCap := by
    unfold w1CtLenCap
    have hdiv : x.ptext.length / 16 ≤ msgCapBytes / 16 := Nat.div_le_div_right hptext
    omega
  have hOtrBoth : ∀ r sess otr taken,
      kit.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec fineCostModel (W1OtrStepLocal P x r sess otr taken)
        (spqrSendTightDeltaCum + (2 * 32 + 9539) + (2 * w1CtLenCap + 9539) + w1SigCumCap)
        (spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigLiveCap)
        (max spqrSendTightDeltaPeak (spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigPeakCap))
        (max spqrSendTightMaxReq (max 32 (max w1CtLenCap w1SigReqCap))) ∧
      PhaseGroupSpec fineCostModel (W1OtrStepLocal P x r sess otr taken)
        (spqrSendTightGroupS + 6 * FineScale + signalMessageNewDeltaGrpS) := by
    intro r sess otr taken hScAt hcur hfrom
    obtain ⟨hpqr, _⟩ := fromSessionState_pqr_and_taken_s2 hfrom
    have hTopOtr : TopStateTight P.C.F P.Q.K otr.pqrState := by
      rw [hpqr]
      exact recordSpqrStateTight640_of_placedScopeAt hScAt hTopRem sess hcur
    obtain ⟨hPts, hChain, _⟩ := topStateTight_to_tightValid640 hTopOtr
    have hSendCr := spqrSend_phaseCreditSpec_tight (ptext := x.rest) hPts hChain
    have hStepCr := otrEncryptStep_creditSpec_small32 fineCostModel_modelHyps
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (ptextLen := x.ptext.length) hSendCr hSigCr
    dsimp only at hStepCr
    constructor
    · refine hStepCr.mono ?_ ?_ ?_ ?_
      · omega
      · omega
      · exact Nat.max_le.mpr
          ⟨Nat.le_max_left _ _,
           Nat.le_trans (by omega) (Nat.le_max_right _ _)⟩
      · exact Nat.max_le.mpr
          ⟨Nat.le_max_left _ _,
           Nat.le_trans
             (Nat.max_le.mpr
               ⟨Nat.le_max_left _ _,
                Nat.le_trans
                  (Nat.max_le.mpr
                    ⟨Nat.le_trans hct_le (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
                  (Nat.le_max_right _ _)⟩)
             (Nat.le_max_right _ _)⟩
    · have hSendGrp := spqrSendTightCap_groupSpec fineCostModel otr.pqrState x.rest
      have hMkgGrp : PhaseGroupSpec fineCostModel
          LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments.OtrApplyEnvTight (3 * FineScale) :=
        ((fine_rustAlloc_le_44 (by decide) (by decide)).seq
          (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)
      have hCtGrp := PhaseGroupSpec.rustAlloc_any fineCostModel ((x.ptext.length / 16 + 1) * 16) 1
      have hTailGrp := (PhaseGroupSpec.freeOnly fineCostModel).or
        (hMkgGrp.seq (hCtGrp.seq (hSigGrp.seq (PhaseGroupSpec.freeOnly fineCostModel))))
      exact (hSendGrp.seq hTailGrp).mono (by omega)
  have hKyber1569 : ∀ r sess otr taken,
      kit.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length = 1569 := by
    intro r sess _ _ hsc hcur _ ct hct0
    obtain ⟨_, s0, hs0, hSessP⟩ := hsc.1
    have hs_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
    subst hs_eq
    rcases hsk : s0.pendingKyberPreKey with _ | k0 <;> rw [hsk] at hct0
    · cases hct0
    · simp only [Option.map_some, Option.some.injEq] at hct0
      subst hct0
      exact hSessP.2.2.1 k0 hsk
  let serPeakW1 := 1080975 + optLargeCost fineCostModel w1PostPqCap +
    optLargeCost fineCostModel w1StoreEncCap
  have hStoreNone : ∀ r sess otr taken (k : IdentityKey),
      kit.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone P.C (pqxdhSpqrModel P) x otr) taken))
        (11265 + 8420940 + 9085) serPeakW1 serPeakW1
        (max 384 (max (max 208000 w1PostPqCap) w1StoreEncCap)) ∧
      PhaseGroupSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone P.C (pqxdhSpqrModel P) x otr) taken))
        (9 * FineScale + recordSerializeDomFineGrpS) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := fromSessionState_pqr_and_taken_s2 hfrom
    have hTopOtr : TopStateTight P.C.F P.Q.K otr.pqrState := by
      rw [hpqr]
      exact recordSpqrStateTight640_of_placedScopeAt hScAt hTopRem sess hcur
    have hTop' : TopStateTight P.C.F P.Q.K (otrAfterNone P.C (pqxdhSpqrModel P) x otr).pqrState :=
      otr_encrypt_topStateTight_s2 P.C rfl x.ptext none x.rest otr hTopOtr
    obtain ⟨hDom, hEnc⟩ := storedRecord_bounds_s2 hScAt.1 hcur htaken hTop'
    exact binarySessStore_credit_and_group x.rem.val _ hremLen hDom hEnc
  have hStoreSome : ∀ r sess otr taken (k : IdentityKey),
      kit.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr) taken))
        (11265 + 8420940 + 9085) serPeakW1 serPeakW1
        (max 384 (max (max 208000 w1PostPqCap) w1StoreEncCap)) ∧
      PhaseGroupSpec fineCostModel
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr) taken))
        (9 * FineScale + recordSerializeDomFineGrpS) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := fromSessionState_pqr_and_taken_s2 hfrom
    have hTopOtr : TopStateTight P.C.F P.Q.K otr.pqrState := by
      rw [hpqr]
      exact recordSpqrStateTight640_of_placedScopeAt hScAt hTopRem sess hcur
    have hTop' :
        TopStateTight P.C.F P.Q.K
          (otrAfterSome P.C (pqxdhSpqrModel P) uuidTryParse x otr).pqrState :=
      otr_encrypt_topStateTight_s2 P.C rfl x.ptext _ x.rest otr hTopOtr
    obtain ⟨hDom, hEnc⟩ := storedRecord_bounds_s2 hScAt.1 hcur htaken hTop'
    exact binarySessStore_credit_and_group x.rem.val _ hremLen hDom hEnc
  have hImp : ∀ evs, W1SendBinaryKitSlotEnv P R evs →
      WithStoresEncTightEnv scopeKit kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity P.C (pqxdhSpqrModel P) uuidTryParse x
        (W1OtrStepLocal P x) (W1OtrStepLocal P x) W1PkRawLocal evs :=
    fun _ hevs => w1SendBinaryKitSlotEnv_imp_tight P R hptext hevs
  constructor
  · have hcr := withStoresEncTight_creditSpec_tight fineCostModel_modelHyps
      scopeKit kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity
      P.C (pqxdhSpqrModel P) uuidTryParse x
      (nameCap := 40) (nameCum := 9619) (kyberLen := 1569)
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by change 24 ≤ _; rw [fineCostModel_smallMaxReq_eq]; decide)
      (by change 32 ≤ _; rw [fineCostModel_smallMaxReq_eq]; decide)
      (by change 32 ≤ _; rw [fineCostModel_smallMaxReq_eq]; decide)
      (by change 32 ≤ _; rw [fineCostModel_smallMaxReq_eq]; decide)
      hremName40
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      smallAllocCost_fine_le_9619_of_le_40
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
      hLoadCr hKyber1569
      (fun r sess otr taken hsc hcur hfrom => (hOtrBoth r sess otr taken hsc hcur hfrom).1)
      (fun r sess otr taken hsc hcur hfrom => (hOtrBoth r sess otr taken hsc hcur hfrom).1)
      (fun _ _ _ _ _ _ _ => hPkCr)
      (fun _ _ _ _ k _ _ _ _ => (hTrust k .sending hremLen hIdCap).1)
      (fun _ _ _ _ k _ _ _ _ => (hSave k hremLen hIdCap).1)
      (fun r sess otr taken k hsc hcur hfrom hk => (hStoreNone r sess otr taken k hsc hcur hfrom hk).1)
      (fun r sess otr taken k hsc hcur hfrom hk => (hStoreSome r sess otr taken k hsc hcur hfrom hk).1)
    dsimp only [serPeakW1] at hcr
    have hbox1 : kit.loadBoxSize = 24 := rfl
    have hbox2 : ikit.trustBoxSize = 32 := rfl
    have hbox3 : ikit.saveBoxSize = 32 := rfl
    have hbox4 : kit.storeBoxSize = 32 := rfl
    rw [hbox1, hbox2, hbox3, hbox4] at hcr
    change PhaseCreditSpec fineCostModel _
      ((fineSmallAllocCost 24 + _) + max 9619
        (max 9619 (fineSmallAllocCost 1569 + _ + _ +
          ((fineSmallAllocCost 32 + _) + max 9619
            ((fineSmallAllocCost 32 + _) +
              (fineSmallAllocCost 32 + fineSmallAllocCost 32 + _))))))
      _ _ _ at hcr
    rw [show max 0 sessionCapBytes = sessionCapBytes from Nat.zero_max sessionCapBytes] at hcr
    unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
      loadPollCancel2MiBMaxReq at hcr
    unfold w1SendRealDcanCum w1SendRealDcanPeak w1SendRealDcanMaxReq
      LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot.w1SendRealCum
      LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot.w1SendRealPeak
      LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot.w1SendRealMaxReq
    simp only [optLargeCost_fine_eq] at hcr ⊢
    exact (hcr.mono (by decide) (by decide) (by decide) (by decide)).of_imp hImp
  · have hgrp := withStoresEncTightEnv_groupSpec fineCostModel
      scopeKit kit kitEnv StoresGhost.opened.sessions
      ikit ikitEnv StoresGhost.opened.identity
      P.C (pqxdhSpqrModel P) uuidTryParse x
      hLoadGrp
      (fun r sess otr taken hsc hcur hfrom => (hOtrBoth r sess otr taken hsc hcur hfrom).2)
      (fun r sess otr taken hsc hcur hfrom => (hOtrBoth r sess otr taken hsc hcur hfrom).2)
      (fun _ _ _ _ _ _ _ => hPkGrp)
      (fun _ _ _ _ k _ _ _ _ => (hTrust k .sending hremLen hIdCap).2)
      (fun _ _ _ _ k _ _ _ _ => (hSave k hremLen hIdCap).2)
      (fun r sess otr taken k hsc hcur hfrom hk => (hStoreNone r sess otr taken k hsc hcur hfrom hk).2)
      (fun r sess otr taken k hsc hcur hfrom hk => (hStoreSome r sess otr taken k hsc hcur hfrom hk).2)
    exact (hgrp.mono (by decide)).of_imp hImp

private theorem binaryKitW1_credit_and_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel ((mkBinaryKitRealCalleeEnvs img S X W g).encEnv)
      w1SendRealDcanCum w1SendRealDcanPeak w1SendRealDcanPeak
      w1SendRealDcanMaxReq ∧
    PhaseGroupSpec fineCostModel ((mkBinaryKitRealCalleeEnvs img S X W g).encEnv)
      w1SendRealDcanGrpS := by
  unfold mkBinaryKitRealCalleeEnvs
  dsimp only
  cases hc : g.c with
  | send peerAddr =>
    rw [hc] at hparse
    exact ⟨phaseCreditSpec_exists_guarded_local fun R hdom =>
        (w1BinarySend_credit_and_groups ⟨W.C, W.Q⟩ g.i peerAddr R hi hparse hdom).1,
      phaseGroupSpec_exists_guarded fineCostModel fun R hdom =>
        (w1BinarySend_credit_and_groups ⟨W.C, W.Q⟩ g.i peerAddr R hi hparse hdom).2⟩
  | keygen =>
    exact ⟨((PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h),
      ((PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h)⟩
  | init _ _ =>
    exact ⟨((PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h),
      ((PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h)⟩
  | recv _ =>
    exact ⟨((PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h),
      ((PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)).of_imp
        (fun _ h => False.elim h)⟩

end S2Helpers

/-- Binary-kit W1 (`send`) `SingleSlotFineSpec` on `(mkBinaryKitRealCalleeEnvs img S X W g).encEnv`.
`live = peak`: `RecordSerializeSeqFreeValidEnv` admits `e_free = []` (no `dropClonedSessionEvents`),
so `segCloneLarge` may stay live after the slot. -/
def binaryKitW1_fineSpec [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    SingleSlotFineSpec ((mkBinaryKitRealCalleeEnvs img S X W g).encEnv) where
  cum := w1SendRealDcanCum
  live := w1SendRealDcanPeak
  peak := w1SendRealDcanPeak
  maxReq := w1SendRealDcanMaxReq
  grpS := w1SendRealDcanGrpS
  credit := by exact (binaryKitW1_credit_and_groups img S X W g hi hparse).1
  live_le_peak := Nat.le_refl _
  groups := by exact (binaryKitW1_credit_and_groups img S X W g hi hparse).2

/-! ## W2 (`recv` Whisper) Binary-Kit Slot Bounds -/

private theorem s2b_dirPutTail_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv dir name)
      9789 0 0 192 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv
  split
  · have hgrow :
        LibsignalBinary.Heap.RustStdAllocBudgetBridge.rawVecGrowEvents 48 4 8
          (BitVec.ofNat 64 dir.changed.length) =
        LibsignalBinary.Heap.rustAllocEvents 192 8 := by
      rw [hch]; rfl
    rw [hgrow]
    have h192 : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents 192 8) 9789 0 0 192 :=
      (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 192) (al := 8)
        (by decide) (by decide)
        (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide)).mono
        (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_9789_of_le_192
          (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
    exact ((PhaseCreditSpec.nil fineCostModel).or h192).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (PhaseCreditSpec.freeOnly
      LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc).mono
      (by decide) (by decide) (by decide) (by decide)

private theorem s2b_dirPutTail_opened_group {dir : DirGhost} (hch : dir.changed = [])
    (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv dir name)
      (3 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv
  split
  · have hgrow :
        LibsignalBinary.Heap.RustStdAllocBudgetBridge.rawVecGrowEvents 48 4 8
          (BitVec.ofNat 64 dir.changed.length) =
        LibsignalBinary.Heap.rustAllocEvents 192 8 := by
      rw [hch]; rfl
    rw [hgrow]
    exact ((PhaseGroupSpec.nil fineCostModel).or
      (PhaseGroupSpec.rustAlloc_any fineCostModel 192 8)).mono (by decide)
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (by decide)

private theorem s2b_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) (hname : name.length ≤ 40) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        dir name bytes)
      11396 0 0 192 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
  have ht := s2b_dirPutTail_opened_credit hch name
  split_ifs with hz
  · exact ht.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have hpos : 0 < name.length := Nat.pos_of_ne_zero (List.length_eq_zero_iff.not.mpr hz)
    have hn64 : name.length ≤ 64 := Nat.le_trans hname (by decide)
    have hsm : name.length ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans hname (by decide)
    have ha : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents name.length 1) 1607 0 0 192 :=
      (PhaseCreditSpec.rustAlloc_small fineCostModel (req := name.length) (al := 1)
        (by decide) hpos hsm).mono
        (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_1607_of_le_64 hn64)
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_trans hname (by decide))
    exact (ha.seq ht).mono (by decide) (by decide) (by decide) (by decide)

private theorem s2b_dirPutStr_opened_group {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        dir name bytes)
      (6 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
  have ht := s2b_dirPutTail_opened_group hch name
  split
  · exact ht.mono (by decide)
  · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel name.length 1).seq ht).mono (by decide)

private abbrev s2b_idGet64Cum : Nat :=
  21185 + max 738 (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.fineReadFileCum (max 0 64))

private abbrev s2b_idGet64MaxReq : Nat :=
  max 256 (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.fineReadFileMaxReq (max 0 64))

private theorem s2b_idTrustPoll_credit (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey)
    (hrem40 : rem.name.length ≤ 40)
    (hcap64 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ 64) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        F0 StoresGhost.opened.identity rem k .receiving)
      s2b_idGet64Cum 0 0 s2b_idGet64MaxReq := by
  have hget :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
      (LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_peers.mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0))
      (Nat.le_trans hrem40 (by decide)) hcap64
  exact (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.seq_freeOnly_phaseCredit
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc hget).mono
    (Nat.le_refl _) (by decide) (by decide) (Nat.le_refl _)

private theorem s2b_idTrustPoll_group (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        F0 StoresGhost.opened.identity rem k .receiving)
      (39 * FineScale) :=
  ((LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_groupSpec
      fineCostModel cliIo.rd F0 StoresGhost.opened.identity.peers rem.name).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)

private theorem s2b_idSavePoll_credit (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey)
    (hrem40 : rem.name.length ≤ 40)
    (hcap64 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ 64) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
        cliIo.rd
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        F0 StoresGhost.opened.identity rem k)
      (s2b_idGet64Cum + 13003) 0 0 s2b_idGet64MaxReq := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
  have hget : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
        cliIo.rd F0 StoresGhost.opened.identity.peers rem.name)
      s2b_idGet64Cum 0 0 s2b_idGet64MaxReq :=
    (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
      (LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_peers.mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0))
      (Nat.le_trans hrem40 (by decide)) hcap64).mono
      (Nat.le_refl _) (by decide) (by decide) (Nat.le_refl _)
  have htail : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      13003 0 0 256 := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    | ok _ =>
      have hfr := PhaseCreditSpec.freeOnly
        LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc
      have hpk : PhaseCreditSpec fineCostModel
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
          1607 0 0 256 :=
        (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 33) (al := 1)
          (by decide) (by decide)
          (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide)).mono
          (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_1607_of_le_64
            (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
      have hput := s2b_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        rem.name k.serialize hrem40
      exact (hfr.seq (hpk.seq hput)).mono (by decide) (by decide) (by decide) (by decide)
  exact (hget.seq htail).mono (Nat.le_refl _) (by decide) (by decide) (by decide)

private theorem s2b_idSavePoll_group (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
        cliIo.rd
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        F0 StoresGhost.opened.identity rem k)
      (48 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
  have hget :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_groupSpec
      fineCostModel cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
  have htail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      (9 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseGroupSpec.nil fineCostModel).mono (by decide)
    | ok _ =>
      have hfr := PhaseGroupSpec.freeOnly fineCostModel
      have hpk : PhaseGroupSpec fineCostModel
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
          (3 * FineScale) :=
        PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
      have hput := s2b_dirPutStr_opened_group (dir := StoresGhost.opened.identity.peers) rfl
        rem.name k.serialize
      exact (hfr.seq (hpk.seq hput)).mono (by decide)
  exact (hget.seq htail).mono (by decide)

private abbrev s2b_w2StoreLivePeak : Nat :=
  1080975 +
    LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.optLargeCost fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) +
    LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.optLargeCost fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192)

private theorem s2b_storePoll_credit
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (rec' : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (hrem40 : rem.name.length ≤ 40)
    (hDom : ∀ ses, rec'.currentSession = some ses →
      LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
        (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses)
    (hEnc : (CryptoVerification.E2E.Record.encodeRecord rec').length ≤
      LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.AddrTextValEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv)
        LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutEnv
        StoresGhost.opened.sessions rem rec')
      8441994 s2b_w2StoreLivePeak s2b_w2StoreLivePeak 5322344 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
  have had :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_fine_phaseCredit_tight
      rem hrem40
  have hser : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv rec')
      8420940 s2b_w2StoreLivePeak s2b_w2StoreLivePeak 5322344 :=
    { req_align := fun evs ⟨g, hgv, hs⟩ => by
        have hValid : ∀ G ses, g.cur = some G → rec'.currentSession = some ses →
            LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
            LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses := by
          intro G ses hg hr
          unfold LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.RecordGhostValid at hgv
          rw [hg, hr] at hgv
          exact ⟨hgv, hDom ses hr⟩
        have hm := (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.PhaseCreditSpec.recordSerialize_seqFree_tight
          LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_modelHyps g rec').mono
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeTightCum_fine_le_of_dom hValid)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (Nat.le_trans
            (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeMaxReq_le_of_dom hValid hEnc)
            (by decide : max (max 208000 (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000))
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) ≤ 5322344))
        exact hm.req_align evs hs
      credit_le := fun st0 {_} ⟨g, hgv, hs⟩ => by
        have hValid : ∀ G ses, g.cur = some G → rec'.currentSession = some ses →
            LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
            LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses := by
          intro G ses hg hr
          unfold LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.RecordGhostValid at hgv
          rw [hg, hr] at hgv
          exact ⟨hgv, hDom ses hr⟩
        have hm := (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.PhaseCreditSpec.recordSerialize_seqFree_tight
          LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_modelHyps g rec').mono
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeTightCum_fine_le_of_dom hValid)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (Nat.le_trans
            (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeMaxReq_le_of_dom hValid hEnc)
            (by decide : max (max 208000 (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000))
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) ≤ 5322344))
        exact hm.credit_le st0 hs }
  have hput := s2b_dirPutTail_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (CryptoVerification.SignalSession.Cli.addressText rem)
  exact (had.seq (hser.seq hput)).mono (by decide) (by decide) (by decide) (by decide)

private theorem s2b_storePoll_group
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (rec' : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (hrem40 : rem.name.length ≤ 40)
    (hDom : ∀ ses, rec'.currentSession = some ses →
      LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
        (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.AddrTextValEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv)
        LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutEnv
        StoresGhost.opened.sessions rem rec')
      (9 * FineScale +
        LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
  have had :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_fine_groupSpec
      rem hrem40
  have hser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv rec')
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS :=
    { groups_le := fun st0 {_} ⟨g, hgv, hs⟩ =>
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeSeqFreeEnv_dom_fine_groupSpec
          hgv hDom).groups_le st0 hs }
  have hput := s2b_dirPutTail_opened_group (dir := StoresGhost.opened.sessions) rfl
    (CryptoVerification.SignalSession.Cli.addressText rem)
  exact (had.seq (hser.seq hput)).mono (by decide)

private theorem s2b_w2Slot_credit [LibsignalPlacement]
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    {peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    (hi : CliPqxdhInputs P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w2R : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2BinaryWhisperParams)
    (hw2 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2BinaryWhisperDom
      (.recv peerAddr) i w2R) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2RecvWhisperBinaryKitSlotEnv P w2R)
      w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanPeak
      w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcanMaxReq := by
  obtain ⟨hpeerVal, hxpeer, hrem, hct, hF⟩ := hw2 peerAddr rfl
  unfold LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2RecvWhisperBinaryKitSlotEnv
  rw [hF, hxpeer]
  set x := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost w2R.x
  have ⟨_, hremName, _⟩ :=
    LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.peer_and_rem_name_le_40_of_recv
      hparse hpeerVal hrem
  have hrem40 : x.rem.val.name.length ≤ 40 := hremName
  have hSessFileCap : ∀ bs,
      cliIo.rd (runFiles i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText w2R.peer.val)) = .ok bs →
      bs.length ≤ LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles i) _ bs hbs
  have hSessRemCap : ∀ bs,
      cliIo.rd (runFiles i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText x.rem.val)) = .ok bs →
      bs.length ≤ LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles i) _ bs hbs
  have hIdCap64 : ∀ bs,
      cliIo.rd (runFiles i)
        (pathOf StoresGhost.opened.identity.peers.path x.rem.val.name) = .ok bs →
      bs.length ≤ 64 := by
    have h0 :=
      LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.idPeers_rd_length_le_64_of_cliPqInputs_recv
        hi hparse hpeerVal
    have hnm : x.rem.val.name = w2R.peer.name.bytes := congrArg (·.name) hrem
    rw [hnm]
    exact h0
  have hStateTight :
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        P.C.F P.Q.K (runFiles i) x.rem.val := by
    rw [hrem, hpeerVal]
    exact
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliPqInputs_recv
        hi hparse
  have hLoad :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight
      (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit)
      LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_sess
      (by decide) hrem40 hSessRemCap (by decide)
  let kit0 :=
    CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec w2R.repAlloc 0#64 cliIo.rd
      (runFiles i) CryptoVerification.SignalSession.Cli.MainHops.cliWrOk
      CryptoVerification.SignalSession.Cli.Slots.scopeKit w2R.peer
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed
      (CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed w2R.B.readFile)
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX
  have hcr :=
    LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.withStoresDec_fine_creditSpec_tight
      (kit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decSessKitPlaced
        w2R.repAlloc (runFiles i) w2R.peer w2R.B)
      (kitEnv := LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.decBinarySessKitPlacedBudget
        w2R.repAlloc w2R.B (runFiles i) w2R.peer)
      (st0 := StoresGhost.opened.sessions)
      (ikit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decIdKitPlaced
        w2R.repAlloc (runFiles i) w2R.peer w2R.B)
      (ikitEnv := LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.decBinaryIdKitPlacedBudget
        w2R.repAlloc w2R.B (runFiles i) w2R.peer)
      (ist0 := StoresGhost.opened.identity)
      (C := P.C) (S := CryptoVerification.E2E.pqxdhSpqrModel P) (parse := uuidTryParse)
      (tdEnv := LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.W2RealTdEnv P.C.F P.Q.K)
      (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (x := x)
      (nameCap := 40)
      rfl rfl rfl rfl hremName (by decide)
      hLoad
      (fun rec ses G hsc hcur hgv => by
        have hsc0 : kit0.ScopeAt CryptoVerification.SignalSession.Cli.Slots.scopeKit
            StoresGhost.opened.sessions x.rem.val rec := hsc
        obtain ⟨_, hDom⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_sessionCloneDom
            hrem hSessFileCap hsc0 hcur
        have hTop :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hcur rfl hStateTight
        exact LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordDecrypt_dom_phaseCredit_tight
          (x := CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf x 0#64 G ses.state)
          (ses := ses) rfl hgv hDom
          (fun G₁ _ =>
            LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.w2RealTd_phaseCredit P.C.F P.Q.K
              (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
                (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf x 0#64 G ses.state) G₁)
              hTop hct))
      (fun _ _ _ _ k _ _ _ _ => s2b_idTrustPoll_credit (runFiles i) x.rem.val k hrem40 hIdCap64)
      (fun _ _ _ _ k _ _ _ _ => s2b_idSavePoll_credit (runFiles i) x.rem.val k hrem40 hIdCap64)
      (fun rec _ rec' ses' _ hsc hdec hc' _ => by
        have hsc0 : kit0.ScopeAt CryptoVerification.SignalSession.Cli.Slots.scopeKit
            StoresGhost.opened.sessions x.rem.val rec := hsc
        have hRecTight :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hStateTight
        have hIn :=
          LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers.scopeIn_of_scopeKit_and_recordSpqrStateTight640
            hsc0.1 hRecTight
        have hEncPre :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_encodeRecord_le
            hrem hSessFileCap hsc0
        obtain ⟨_, hPostDom, hEncPost⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.decryptRecord_post_caps_of_scopeIn
            hIn hEncPre hdec
        obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
        exact s2b_storePoll_credit x.rem.val rec' hrem40
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)
          hEncPost)
  exact hcr.mono (by decide) (by decide) (by decide) (by decide)

private theorem s2b_w2Slot_group [LibsignalPlacement]
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    {peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    (hi : CliPqxdhInputs P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w2R : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2BinaryWhisperParams)
    (hw2 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2BinaryWhisperDom
      (.recv peerAddr) i w2R) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2RecvWhisperBinaryKitSlotEnv P w2R)
      w2RecvWhisperRealDcanGrpS := by
  obtain ⟨hpeerVal, hxpeer, hrem, _, hF⟩ := hw2 peerAddr rfl
  unfold LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W2RecvWhisperBinaryKitSlotEnv
  rw [hF, hxpeer]
  set x := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost w2R.x
  have ⟨_, hremName, _⟩ :=
    LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.peer_and_rem_name_le_40_of_recv
      hparse hpeerVal hrem
  have hrem40 : x.rem.val.name.length ≤ 40 := hremName
  have hSessFileCap : ∀ bs,
      cliIo.rd (runFiles i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText w2R.peer.val)) = .ok bs →
      bs.length ≤ LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles i) _ bs hbs
  have hStateTight :
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        P.C.F P.Q.K (runFiles i) x.rem.val := by
    rw [hrem, hpeerVal]
    exact
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliPqInputs_recv
        hi hparse
  have hLoad :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.defaultLoadPollEnv_dcan_byBytes_fine_groupSpec
      (rd := cliIo.rd) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit)
      (F0 := runFiles i) (dir := StoresGhost.opened.sessions) (rem := x.rem.val) hrem40
  let kit0 :=
    CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec w2R.repAlloc 0#64 cliIo.rd
      (runFiles i) CryptoVerification.SignalSession.Cli.MainHops.cliWrOk
      CryptoVerification.SignalSession.Cli.Slots.scopeKit w2R.peer
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed
      (CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed w2R.B.readFile)
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX
  have hgrp :=
    LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.withStoresDec_phaseGroupSpec
      (kit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decSessKitPlaced
        w2R.repAlloc (runFiles i) w2R.peer w2R.B)
      (kitEnv := LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.decBinarySessKitPlacedBudget
        w2R.repAlloc w2R.B (runFiles i) w2R.peer)
      (st0 := StoresGhost.opened.sessions)
      (ikit := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.decIdKitPlaced
        w2R.repAlloc (runFiles i) w2R.peer w2R.B)
      (ikitEnv := LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.decBinaryIdKitPlacedBudget
        w2R.repAlloc w2R.B (runFiles i) w2R.peer)
      (ist0 := StoresGhost.opened.identity)
      (C := P.C) (S := CryptoVerification.E2E.pqxdhSpqrModel P) (parse := uuidTryParse)
      (tdEnv := LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.W2RealTdEnv P.C.F P.Q.K)
      (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (x := x)
      hLoad
      (fun rec ses G hsc hcur hgv => by
        have hsc0 : kit0.ScopeAt CryptoVerification.SignalSession.Cli.Slots.scopeKit
            StoresGhost.opened.sessions x.rem.val rec := hsc
        obtain ⟨_, hDom⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_sessionCloneDom
            hrem hSessFileCap hsc0 hcur
        have hTop :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hcur rfl hStateTight
        exact LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordDecrypt_dom_phaseGroup
          (x := CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf x 0#64 G ses.state)
          (ses := ses) rfl hgv hDom
          (fun G₁ _ =>
            LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.w2RealTd_fine_groupSpec
              P.C.F P.Q.K
              (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
                (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf x 0#64 G ses.state) G₁)
              hTop))
      (fun _ _ _ _ k _ _ _ _ => s2b_idTrustPoll_group (runFiles i) x.rem.val k)
      (fun _ _ _ _ k _ _ _ _ => s2b_idSavePoll_group (runFiles i) x.rem.val k)
      (fun rec _ rec' ses' _ hsc hdec hc' _ => by
        have hsc0 : kit0.ScopeAt CryptoVerification.SignalSession.Cli.Slots.scopeKit
            StoresGhost.opened.sessions x.rem.val rec := hsc
        have hRecTight :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hStateTight
        have hIn :=
          LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers.scopeIn_of_scopeKit_and_recordSpqrStateTight640
            hsc0.1 hRecTight
        have hEncPre :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_encodeRecord_le
            hrem hSessFileCap hsc0
        obtain ⟨_, hPostDom, _⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.decryptRecord_post_caps_of_scopeIn
            hIn hEncPre hdec
        obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
        exact s2b_storePoll_group x.rem.val rec' hrem40
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost))
  exact hgrp.mono (by decide)

/-- Binary-kit W2 (`recv` whisper) `SingleSlotFineSpec` on
`(mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv`.
`live = peak`: `RecordSerializeSeqFreeValidEnv` admits `e_free = []` (no `dropClonedSessionEvents`),
so `segCloneLarge` may stay live after the slot. -/
def binaryKitW2_fineSpec [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    SingleSlotFineSpec ((mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv) where
  cum := w2RecvWhisperRealDcanCum
  live := w2RecvWhisperRealDcanPeak
  peak := w2RecvWhisperRealDcanPeak
  maxReq := w2RecvWhisperRealDcanMaxReq
  grpS := w2RecvWhisperRealDcanGrpS
  credit := by
    rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
    cases c'
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseCreditSpec _ _ _ _
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseCreditSpec _ _ _ _
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseCreditSpec _ _ _ _
    · exact
        { req_align := fun evs ⟨w2R, hw2, he⟩ =>
            (s2b_w2Slot_credit hi hparse w2R hw2).req_align evs he
          credit_le := fun st0 {_} ⟨w2R, hw2, he⟩ =>
            (s2b_w2Slot_credit hi hparse w2R hw2).credit_le st0 he }
  live_le_peak := Nat.le_refl _
  groups := by
    rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
    cases c'
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseGroupSpec _
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseGroupSpec _
    · exact LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal.emptyPhaseGroupSpec _
    · exact
        { groups_le := fun st0 {_} ⟨w2R, hw2, he⟩ =>
            (s2b_w2Slot_group hi hparse w2R hw2).groups_le st0 he }

/-! ## W3 (`init`) Binary-Kit Slot Bounds -/

section S3aHelpers

open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (addressText_length_le dirDomainCaps_opened_own dirDomainCaps_opened_peers
   dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec cliIoReadFileEnv_nonFreeBound initialStateEnv_groupSpec
   optTailCloneEvents_groupSpec readFileRuleEnv_nonFreeBound recordSerializeDomFineGrpS
   serializeSomeSeqFreeEnv_groupSpec vecCloneEvents_groupSpec w3BoxedStoreStepEnv_groupSpec
   w3InitiateFullEnv_groupSpec w3InitiateFullEnvWide_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit (specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCapEvents cliIoReadCaps phaseCreditSpec_cliIoReadFile_tight)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound nonFreeCount nonFreeCount_append nonFreeCount_nil nonFreeCount_rustAllocEvents
   nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec ModelHyps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (allocBytes1_fine_phaseCredit_tight optLargeCost_fine_of_le)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight RecordSerializeSeqFreeEnv
   recordSerializeMaxReq recordSerializeTightCum)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (w3BoxedStoreStep_phaseCredit w3SpqrInit32_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (phaseCreditSpec_seq_freeOnly phaseCreditSpec_w3InitiateFull_small
   phaseCreditSpec_w3InitiateFullWide_small)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (AliceInitiatedAnyCkBounds RecordAliceInitiatedAnyCkBounds
   recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820
   recordSerializeTightCum_aliceInitiatedAnyCk_le_32485)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv IkpSubEnv RecordCodecErrStep RecordCodecLoopEnv
   ikpSubEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (OverCapFile cliRd_ok_le_fileCap readFileOverCapEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight addrTextValEnv_decimal_groupSpec
   dirGetEnv_path_readFile_fine_phaseCredit_tight pathEnv_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainAsProtoGhost senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SegCloneEnv segCloneEvents)

private theorem s3_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem s3_utf8_length (s : String) :
    (utf8 s).length = (s.toList.flatMap String.utf8EncodeChar).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, List.utf8Encode, s3_byteArray_toList_eq_data]

private theorem s3_seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (hA : ∀ evs, A₁ evs → A₂ evs) (hB : ∀ evs, B₁ evs → B₂ evs) :
    ∀ {evs}, SeqEnv A₁ B₁ evs → SeqEnv A₂ B₂ evs
  | _, Or.inl ha => Or.inl (hA _ ha)
  | _, Or.inr ⟨e1, e2, rfl, ha, hb⟩ => Or.inr ⟨e1, e2, rfl, hA _ ha, hB _ hb⟩

private theorem s3_phaseGroupSpec_append_eq (M : AllocCostModel) [HasFineGroupCredit M]
    {e₁ e₂ : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = e₁) g₁) (h₂ : PhaseGroupSpec M (· = e₂) g₂) :
    PhaseGroupSpec M (· = e₁ ++ e₂) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨e₁, e₂, h, rfl, rfl⟩

private theorem s3_dirGetFixed_credit
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    let fc := max maxVal fileCap
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (21185 + max (573818 + 738) (fineReadFileCum fc))
      (fineReadFileLive fc)
      (max 3162118 (fineReadFilePeak fc))
      (max 2097152 (fineReadFileMaxReq fc)) := by
  dsimp only
  have hbase := dirGetEnv_path_readFile_fine_phaseCredit_tight rd F0 dir name hdc hname hcap
  dsimp only at hbase
  unfold DirGetEnv at hbase ⊢
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    rw [hfind] at hbase
    exact hbase.mono (by omega) (Nat.le_refl _) (Nat.le_max_right _ _)
      (by have := Nat.le_max_right 256 (fineReadFileMaxReq (max maxVal fileCap)); omega)
  | none =>
    rw [hfind] at hbase
    cases hrd : rd F0 (pathOf dir.path name) with
    | ok bs =>
      have himp : ∀ evs,
          DirGetMissEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name evs →
          DirGetMissEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name evs := by
        intro evs hm
        unfold DirGetMissEnv at hm ⊢
        exact s3_seqEnv_mono (fun _ h => h)
          (fun _ hr => s3_seqEnv_mono
            (fun _ hrf => hrf.elim id fun ⟨herr, _, _⟩ => by rw [hrd] at herr; cases herr)
            (fun _ h => h) hr) hm
      exact (hbase.of_imp himp).mono (by omega) (Nat.le_refl _) (Nat.le_max_right _ _)
        (by have := Nat.le_max_right 256 (fineReadFileMaxReq (max maxVal fileCap)); omega)
    | error u =>
      cases u
      unfold DirGetMissEnv
      have hp : PhaseCreditSpec fineCostModel
          (DirGetPathEnv PathEnv dir.path name) 21185 0 0 256 := by
        unfold DirGetPathEnv
        split_ifs
        · have hab := allocBytes1_fine_phaseCredit_tight hname
          rw [optLargeCost_fine_of_le (by decide)] at hab
          exact hab.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
        · exact pathEnv_fine_phaseCredit_tight hdc.path_len_le hname
      have hrFix : PhaseCreditSpec fineCostModel
          (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name)) 573818 0 3162118 2097152 := by
        have hr0 : PhaseCreditSpec fineCostModel
            (ReadFileRuleEnv rd F0 (pathOf dir.path name)) 0 0 0 0 :=
          PhaseCreditSpec.of_eq_nil (fun _ h => by unfold ReadFileRuleEnv at h; rw [hrd] at h; exact h)
        have hlc2M : 2105347 ≤ 0 + HasFineReallocCredit.largeCost fineCostModel 2097152 := by
          rw [fineCostModel_largeCost_eq]
        have hcio : PhaseCreditSpec fineCostModel
            (· = cliIoCapEvents (cliIoReadCaps 9 2097152))
            573818 (0 + HasFineReallocCredit.largeCost fineCostModel 2097152) 3162118 2097152 :=
          (phaseCreditSpec_cliIoReadFile_tight fineCostModel_modelHyps
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            2097152).mono (Nat.le_refl _) hlc2M (Nat.le_refl _) (Nat.le_refl _)
        have hfree : DeallocCreditSpec fineCostModel
            (· = rustDeallocEvents 2097152 1)
            (HasFineReallocCredit.largeCost fineCostModel 2097152) :=
          DeallocCreditSpec.free_large fineCostModel (req := 2097152) (al := 1)
            (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hover : PhaseCreditSpec fineCostModel
            (fun evs => rd F0 (pathOf dir.path name) = .error () ∧
              OverCapFile F0 (pathOf dir.path name) ∧ evs = readFileOverCapEvents)
            573818 0 3162118 2097152 :=
          (hcio.concat_dealloc_cancel hfree).of_imp fun _ ⟨_, _, heq⟩ => by
            rw [heq]; unfold readFileOverCapEvents
            rw [specCliIoReadSchedule_events_eq 9 2097152]
            exact ⟨_, _, rfl, rfl, rfl⟩
        exact (hr0.or hover).mono (by decide) (Nat.le_refl 0) (by decide) (by decide)
      have herr22 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) 738 0 0 22 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        have ha22 := PhaseCreditSpec.rustAlloc_small fineCostModel
          (req := 22) (al := 1) (by decide) (by decide)
          (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hc22 : HasFineReallocCredit.smallAllocCost fineCostModel 22 ≤ 738 := by
          have h738 := rustAllocTightCum_fine_le_738 (req := 22) (by decide)
          unfold rustAllocTightCum at h738
          rw [fineCostModel_smallMaxReq_eq] at h738
          simpa using h738
        exact phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps
          (ha22.mono hc22 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22))
      exact (hp.seq (hrFix.seq herr22)).mono
        (by omega) (Nat.zero_le _) (Nat.le_max_left 3162118 _)
        (Nat.max_le.mpr ⟨Nat.le_trans (by decide : 256 ≤ 2097152) (Nat.le_max_left 2097152 _),
          Nat.le_trans (by decide : max 2097152 22 ≤ 2097152) (Nat.le_max_left 2097152 _)⟩)

private theorem s3_dirGetFixed_groups (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (42 * FineScale) := by
  have hPath : PhaseGroupSpec M (DirGetPathEnv PathEnv dir.path name) (9 * FineScale) := by
    unfold DirGetPathEnv
    split_ifs
    · exact (allocBytes1Events_groupSpec M name).mono (by omega)
    · unfold PathEnv pathEvents
      have p1 : PhaseGroupSpec M (· = pathToOwnedEvents dir.path.length) (3 * FineScale) := by
        unfold pathToOwnedEvents
        split
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
      have p2 : PhaseGroupSpec M (· = pathPushSlashEvents dir.path.length) (3 * FineScale) := by
        unfold pathPushSlashEvents
        split
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
      have p3 : PhaseGroupSpec M
          (· = pathAppendNameEvents dir.path.length name.length) (3 * FineScale) := by
        unfold pathAppendNameEvents
        dsimp only
        split
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
      exact (s3_phaseGroupSpec_append_eq M p1 (s3_phaseGroupSpec_append_eq M p2 p3)).mono (by omega)
  have hRead : PhaseGroupSpec M (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name))
      (30 * FineScale) := by
    have hnf : NonFreeBound (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name)) 10 := by
      rintro evs (h1 | ⟨_, _, rfl⟩)
      · exact readFileRuleEnv_nonFreeBound rd F0 (pathOf dir.path name) evs h1
      · unfold readFileOverCapEvents
        rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero,
            specCliIoReadSchedule_events_eq 9 2097152]
        exact cliIoReadFileEnv_nonFreeBound 2097152 _ rfl
    exact (PhaseGroupSpec.of_nonFreeBound M hnf).mono (by omega)
  have hAfter : PhaseGroupSpec M (DirGetAfterReadEnv rd F0 (pathOf dir.path name))
      (3 * FineScale) := by
    unfold DirGetAfterReadEnv DirGetErrAllocEnv
    cases rd F0 (pathOf dir.path name) with
    | ok _ =>
      exact ((PhaseGroupSpec.nil M).seq (PhaseGroupSpec.freeOnly M)).mono (Nat.zero_le _)
    | error u =>
      cases u
      exact ((PhaseGroupSpec.rustAlloc_any M 22 1).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)
  unfold DirGetEnv
  cases dir.changed.find? (fun e => e.1 == name) with
  | some e => exact (allocBytes1Events_groupSpec M e.2).mono (by omega)
  | none =>
    unfold DirGetMissEnv
    exact (hPath.seq (hRead.seq hAfter)).mono (by omega)

private theorem s3_stepEvents_small_live_peak_nonInc
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {maxReq : Nat} (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | ev :: tl, st, ha => by
    have hev := ha ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => ha e (List.mem_cons_of_mem _ he)
    have h1 :
        HasFineReallocCredit.liveLarge (M.step ev st) ≤ HasFineReallocCredit.liveLarge st ∧
        HasFineReallocCredit.peakLarge (M.step ev st) ≤ HasFineReallocCredit.peakLarge st := by
      cases ev with
      | free al sz =>
        obtain ⟨_, hl, hp⟩ := hM.freeNonInc al sz st
        exact ⟨hl, hp⟩
      | alloc req =>
        simp only [eventStepReq] at hev
        obtain ⟨_, hl, hp⟩ := hM.step_alloc_small_any st (Nat.le_trans hev.1 hsmall)
        exact ⟨hl, hp⟩
      | aligned al req =>
        simp only [eventStepReq, eventStepAlign] at hev
        obtain ⟨_, hl, hp⟩ := hM.step_aligned_small_any st hev.2 (Nat.le_trans hev.1 hsmall)
        exact ⟨hl, hp⟩
      | realloc al old new =>
        simp only [eventStepReq, eventStepAlign] at hev
        have hnew : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hev.1 hsmall
        by_cases hold : old ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨_, hl, hp⟩ := hM.step_realloc_small_small_any st hev.2 hold hnew
          exact ⟨hl, hp⟩
        · have hold' : HasFineReallocCredit.smallMaxReq M < old := Nat.lt_of_not_le hold
          obtain ⟨_, hl, hp⟩ := hM.step_realloc_large_small_any st hev.2 hold' hnew
          exact ⟨by omega, hp⟩
    obtain ⟨hl₂, hp₂⟩ := s3_stepEvents_small_live_peak_nonInc hM hsmall tl (M.step ev st) htl
    simp only [AllocCostModel.stepEvents_cons]
    exact ⟨Nat.le_trans hl₂ h1.1, Nat.le_trans hp₂ h1.2⟩

private theorem s3_phaseCreditSpec_zero_live_peak_of_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (hspec : PhaseCreditSpec M E c l p r)
    (hsmall : r ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M E c 0 0 r where
  req_align := hspec.req_align
  credit_le st0 {evs} hE := by
    obtain ⟨hc, _, _⟩ := hspec.credit_le st0 hE
    obtain ⟨hl, hp⟩ :=
      s3_stepEvents_small_live_peak_nonInc hM hsmall evs st0 (hspec.req_align evs hE)
    exact ⟨hc, by omega, by omega⟩

private theorem s3_phaseCreditSpec_exists {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, P a → PhaseCreditSpec M (E a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, P a ∧ E a evs) c l p r where
  req_align evs := fun ⟨a, ha, hE⟩ => (h a ha).req_align evs hE
  credit_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).credit_le st0 hE

private theorem s3_phaseGroupSpec_exists {α : Type}
    {M : AllocCostModel} [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).groups_le st0 hE

private theorem s3_dirDomainCaps_64 {maxDir maxEntries maxVal : Nat} {dir : DirGhost}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hle : maxDir ≤ 64) :
    DirDomainCaps 64 maxEntries maxVal dir :=
  ⟨Nat.le_trans hdc.path_len_le hle, hdc.changed_len_le, hdc.changed_val_le⟩

private theorem s3_rustAlloc_small_credit {req al : Nat}
    (hal : al ≤ 16) (hsmall : req ≤ 3820) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents req al) 9789 0 0 req := by
  by_cases hpos : 0 < req
  · have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
      (req := req) (al := al) hal hpos
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 :=
      LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.fineSmallAllocCost_le_9789_of_le_3820
        hsmall
    exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)
  · have hz : req = 0 := by omega
    subst hz
    refine ⟨?_, ?_⟩
    · intro evs h ev hev
      rw [h] at hev; unfold rustAllocEvents at hev
      split at hev
      · simp only [List.mem_singleton] at hev; subst hev
        simp [eventStepReq, eventStepAlign]
      · simp only [List.mem_singleton] at hev; subst hev
        simp [eventStepReq, eventStepAlign]; omega
    · intro st0 evs h
      rw [h]; unfold rustAllocEvents
      have hc0 : HasFineReallocCredit.smallAllocCost fineCostModel 0 ≤ 9789 :=
        LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.fineSmallAllocCost_le_9789_of_le_3820
          (Nat.zero_le _)
      split
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st0 (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st0
          (by omega : max al 8 ≤ 16) (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩

private theorem s3_dirPut_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutEnv dir name bytes) 9789 0 0 192 := by
  have himp : ∀ evs, DirPutEnv dir name bytes evs →
      evs = [] ∨ evs = rustAllocEvents 192 8 := by
    intro evs h
    unfold DirPutEnv DirPutTailEnv at h
    simp only [hch, List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte,
      List.length_nil] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (s3_rustAlloc_small_credit (req := 192) (al := 8) (by decide) (by decide))).of_imp himp
    |>.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem s3_dirPut_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutEnv dir name bytes) (3 * FineScale) := by
  have himp : ∀ evs, DirPutEnv dir name bytes evs →
      evs = [] ∨ evs = rustAllocEvents 192 8 := by
    intro evs h
    unfold DirPutEnv DirPutTailEnv at h
    simp only [hch, List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte,
      List.length_nil] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact ((PhaseGroupSpec.nil M).or (PhaseGroupSpec.rustAlloc_any M 192 8)).of_imp himp
    |>.mono (by omega)

private theorem s3_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    {name : List (BitVec 8)} (hname : name.length ≤ 64) (bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutStrEnv dir name bytes) 19578 0 0 192 := by
  unfold DirPutStrEnv
  split_ifs with hnil
  · exact (s3_dirPut_opened_credit hch name bytes).mono (by decide)
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have ha := s3_rustAlloc_small_credit (req := name.length) (al := 1)
      (by decide) (Nat.le_trans hname (by decide))
    exact (ha.seq (s3_dirPut_opened_credit hch name bytes)).mono
      (by decide : 9789 + 9789 ≤ 19578) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_trans hname (by decide), Nat.le_refl 192⟩)

private theorem s3_dirPutStr_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutStrEnv dir name bytes) (6 * FineScale) := by
  unfold DirPutStrEnv
  split_ifs
  · exact (s3_dirPut_opened_groups M hch name bytes).mono (by omega)
  · exact ((PhaseGroupSpec.rustAlloc_any M name.length 1).seq
      (s3_dirPut_opened_groups M hch name bytes)).mono (by omega)

private theorem s3_recordCodecLoop_nonFree {budget maxLen : Nat} {evs : List AllocEvent}
    (h : RecordCodecLoopEnv budget maxLen evs) : nonFreeCount evs ≤ budget := by
  induction h with
  | nil => exact Nat.zero_le _
  | @step budget _ evs₁ evs₂ h1 _ ih =>
    have hc1 : nonFreeCount evs₁ ≤ 1 := by
      cases h1 with
      | nil => simp [nonFreeCount_nil]
      | fromErr => simp [nonFreeCount_rustAllocEvents]
      | push0 hp =>
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
        · simp [nonFreeCount_nil]
        · simp [nonFreeCount_rustAllocEvents]
        · omega
    rw [nonFreeCount_append]
    omega
  | @bytesStep budget _ wt valCap bs v rest evs₁ evs₂ hm _ heq _ ih =>
    subst heq
    have hc1 : nonFreeCount (bytesMergeEventsCore wt valCap bs) ≤ 2 * v.length + 1 := by
      unfold bytesMergeEventsCore
      rw [hm]
      by_cases hv0 : v.length = 0
      · simp [hv0, nonFreeCount_nil]
      · simp only [hv0, ↓reduceIte, List.append_assoc, nonFreeCount_append]
        have h1 : nonFreeCount (rustAllocEvents v.length 1) = 1 :=
          nonFreeCount_rustAllocEvents v.length 1
        have h2' : nonFreeCount (doReserveClearEvents valCap.toNat v.length) ≤ 1 := by
          unfold doReserveClearEvents
          split
          · simp [nonFreeCount_nil]
          · split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
        have h3 : nonFreeCount (rustDeallocEvents v.length 1) = 0 :=
          nonFreeCount_rustDeallocEvents v.length 1
        omega
    rw [nonFreeCount_append]
    omega

private theorem s3_ikpTryFrom_credit {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 4070430 0 0 218 := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hsub : ∀ evs, IdentityKeyPairTryFromEnv bs.length evs → IkpSubEnv 213 105 evs := by
      rintro evs ⟨evsL, evsC, hL, hC, rfl⟩
      exact ⟨evsL, evsC, (hL.mono_fuel (by omega)).mono_maxLen hbs, hC, rfl⟩
    have hcr := (ikpSubEnv_phaseCreditSpec fineCostModel_modelHyps 213 105).of_imp hsub
    have hzero := s3_phaseCreditSpec_zero_live_peak_of_small fineCostModel_modelHyps hcr
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
    exact hzero.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem s3_ikpTryFrom_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseGroupSpec M (OptIkpTryFromEnv gr) (639 * FineScale) := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hnf : NonFreeBound (IdentityKeyPairTryFromEnv bs.length) 213 := by
      rintro evs ⟨evsL, evsC, hL, hC, rfl⟩
      have hcL : nonFreeCount evsL ≤ 2 * bs.length + 3 := s3_recordCodecLoop_nonFree hL
      have hcC : nonFreeCount evsC = 0 := by
        rcases hC with ⟨e1, e2, h1, h2, rfl⟩ | ⟨_, eD, ⟨e1, e2, h1, h2, rfl⟩, hD, rfl⟩
        · have f1 : nonFreeCount e1 = 0 := by
            rcases h1 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have f2 : nonFreeCount e2 = 0 := by
            rcases h2 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          simp [nonFreeCount_append, f1, f2]
        · have f1 : nonFreeCount e1 = 0 := by
            rcases h1 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have f2 : nonFreeCount e2 = 0 := by
            rcases h2 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have fD : nonFreeCount eD = 0 := by
            rcases hD with rfl | ⟨_, _, _, rfl⟩ <;>
              simp [nonFreeCount_append, nonFreeCount_rustDeallocEvents]
          simp [nonFreeCount_append, f1, f2, fD]
      rw [nonFreeCount_append, hcC]
      omega
    exact (PhaseGroupSpec.of_nonFreeBound M hnf).mono (by omega)

private theorem s3_segClone_aliceInitiated_groups
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedAnyCkBounds G sess) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G sess.state) (42 * FineScale) := by
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, sess.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      (9 * FineScale) := by
    cases G.sender <;> cases sess.state.senderChain
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rename_i gs sc
      unfold senderChainCloneEvents chainCloneEvents senderChainAsProtoGhost
      dsimp only
      have c1 := vecCloneEvents_groupSpec fineCostModel gs.srk
      have c2 := vecCloneEvents_groupSpec fineCostModel gs.priv
      have c3 := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
      have c4 : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
        PhaseGroupSpec.nil fineCostModel
      exact (s3_phaseGroupSpec_append_eq fineCostModel
        (s3_phaseGroupSpec_append_eq fineCostModel
          (s3_phaseGroupSpec_append_eq fineCostModel c1 c2) c3) c4).mono (by decide)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if sess.state.receiverChains = [] then []
           else rustAllocEvents (104 * sess.state.receiverChains.length) 8 ++
             (G.chains.zip sess.state.receiverChains).flatMap chainCloneEvents)
      (12 * FineScale) := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hmks⟩
    · simp only [hnil, ↓reduceIte]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hrc1]
      simp only [List.cons_ne_self, ↓reduceIte, List.length_singleton, Nat.mul_one]
      have hbuf := PhaseGroupSpec.rustAlloc_any fineCostModel 104 8
      cases G.chains with
      | nil =>
        simp only [List.zip_nil_left, List.flatMap_nil, List.append_nil]
        exact hbuf.mono (by decide)
      | cons gc0 gcs =>
        simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        unfold chainCloneEvents
        dsimp only
        rw [hmks]
        simp only [↓reduceIte]
        have c1 := vecCloneEvents_groupSpec fineCostModel gc0.srk
        have c2 := vecCloneEvents_groupSpec fineCostModel gc0.priv
        have c3 : PhaseGroupSpec fineCostModel
            (· = match rc0.chainKey with | none => [] | some _ => rustAllocEvents 32 1)
            (3 * FineScale) := by
          cases rc0.chainKey
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
        have c4 : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
          PhaseGroupSpec.nil fineCostModel
        have hch := s3_phaseGroupSpec_append_eq fineCostModel
          (s3_phaseGroupSpec_append_eq fineCostModel
            (s3_phaseGroupSpec_append_eq fineCostModel c1 c2) c3) c4
        exact (s3_phaseGroupSpec_append_eq fineCostModel hbuf hch).mono (by decide)
  have hpend := optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if sess.state.pqRatchetState.length = 0 then []
           else rustAllocEvents sess.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel sess.state.pqRatchetState.length 1
  have s1 := s3_phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := s3_phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := s3_phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := s3_phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := s3_phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := s3_phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := s3_phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := s3_phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents
  exact s8.mono (by decide)

private theorem s3_recordSerializeSeqFree_aliceInitiated_groups
    {g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost}
    {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedAnyCkBounds g r) :
    PhaseGroupSpec fineCostModel (RecordSerializeSeqFreeEnv g r) (45 * FineScale) := by
  unfold RecordSerializeSeqFreeEnv
  cases hgc : g.cur <;> cases hrc : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G sess
    exact serializeSomeSeqFreeEnv_groupSpec fineCostModel
      (s3_segClone_aliceInitiated_groups (hb G sess hgc hrc))

private theorem s3_w3Fixed_credit {peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    {dir : List (BitVec 8)} {i : Inputs} {w : W3BinaryInitParams}
    (hdom : W3BinaryInitDom (.init peerAddr dir) i w)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (W3InitBinaryKitSlotEnvFixed w)
      (w3InitRealCum + 4500000)
      (w3InitRealLive + 65536)
      (w3InitRealPeak + 65536)
      (w3InitRealMaxReq + 65536) := by
  obtain ⟨_, hpeer, hF, hspqr, _, halice⟩ := hdom peerAddr dir rfl
  have hpeerVal : w.x.peer.val.name.length ≤ 40 := hpeer
  have haddrLen : (addressText w.x.peer.val).length ≤ 64 := by
    have h51 := addressText_length_le w.x.peer.val
    omega
  have hdcOwn := s3_dirDomainCaps_64 dirDomainCaps_opened_own (by decide)
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hdcSess := s3_dirDomainCaps_64 dirDomainCaps_opened_sess (by decide)
  have hGetPeers := s3_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.peers w.x.peer.val.name hdcPeers
    (Nat.le_trans hpeerVal (by decide)) (fun _ h => cliRd_ok_le_fileCap h)
  have htrust := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32
    (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hGetPeers)
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight w.x.peer.val hpeerVal
  have hGetSess := s3_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.sessions (addressText w.x.peer.val) hdcSess
    haddrLen (fun _ h => cliRd_ok_le_fileCap h)
  have hOptDeser : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val)))
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        have hlen : (b0 :: bsRest).length ≤ 2097152 := by
          change cliIo.rd w.x.F _ = .ok (b0 :: bsRest) at hget
          exact cliRd_ok_le_fileCap hget
        exact s3_phaseCreditSpec_exists fun r henc => by
          unfold ofBytesEnv
          have hlen' : (encodeRecord r).length ≤ 2097152 := by rw [henc]; exact hlen
          exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen').of_imp fun _ h => h.2
  have hload := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 24
    (hAddr.seq (hGetSess.seq (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hOptDeser)))
  have hikp_w : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair") = .ok bs →
        bs.length ≤ 105 := by
    rw [hF]; exact hikp
  have hkpName : (utf8 "identity-key-pair").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hGetKp := s3_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair") hdcOwn
    hkpName hikp_w
  have hIkp := phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps (s3_ikpTryFrom_credit hikp_w)
  have hkp := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 16 (hGetKp.seq hIkp)
  have hspqrSpec := w3SpqrInit32_phaseCredit fineCostModel_modelHyps w.F w.x_spqr hspqr
  have hregName : (utf8 "registration-id").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hGetReg := s3_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "registration-id") hdcOwn
    hregName (fun _ h => cliRd_ok_le_fileCap h)
  have hRegMal : PhaseCreditSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
      9789 0 0 14 := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id") with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      · exact s3_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide)
  have hreg := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 16
    (hGetReg.seq (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hRegMal))
  have hSaveTail : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity w.x.peer.val w.peerKey
        (StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name))
      29367 0 0 192 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 9789 0 0 33 := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
      have hput := s3_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        (Nat.le_trans hpeerVal (by decide)) w.peerKey.serialize
      have hbody := hpks.seq hput
      have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (hf.seq hbody).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hsave := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32 (hGetPeers.seq hSaveTail)
  have hSer0 := PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps w.g_rec w.r_rec
  have hSerReq := recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820 halice
  have hSerCum := recordSerializeTightCum_aliceInitiatedAnyCk_le_32485 halice
  have hSer := (s3_phaseCreditSpec_zero_live_peak_of_small fineCostModel_modelHyps hSer0
    (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
    hSerCum (Nat.le_refl 0) (Nat.le_refl 0) hSerReq
  have hPutSess := s3_dirPut_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText w.x.peer.val) (encodeRecord w.r_rec)
  have hstore := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32
    (hAddr.seq (hSer.seq hPutSess))
  have hfull := phaseCreditSpec_w3InitiateFullWide_small fineCostModel_modelHyps hpeer
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    htrust hload hkp hspqrSpec hreg hsave hstore
  exact hfull.mono (by decide) (by decide) (by decide) (by decide)

private theorem s3_w3Fixed_groups {peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV}
    {dir : List (BitVec 8)} {i : Inputs} {w : W3BinaryInitParams}
    (hdom : W3BinaryInitDom (.init peerAddr dir) i w)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    PhaseGroupSpec fineCostModel (W3InitBinaryKitSlotEnvFixed w)
      (w3InitRealGrpS + 1500 * FineScale) := by
  obtain ⟨_, hpeer, hF, _, _, halice⟩ := hdom peerAddr dir rfl
  have hpeerVal : w.x.peer.val.name.length ≤ 40 := hpeer
  have hikp_w : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair") = .ok bs →
        bs.length ≤ 105 := by
    rw [hF]; exact hikp
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  have hGetPeersG := s3_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.peers w.x.peer.val.name
  have hGetSessG := s3_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.sessions (addressText w.x.peer.val)
  have hGetKpG := s3_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair")
  have hGetRegG := s3_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "registration-id")
  have htrust := w3BoxedStoreStepEnv_groupSpec fineCostModel 32
    (hGetPeersG.seq hf)
  have hAddrG := addrTextValEnv_decimal_groupSpec fineCostModel w.x.peer.val hpeerVal
  have hOptDeserG : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val)))
      deserCancelFineGrpS := by
    unfold OptLoadDeserEnv
    cases StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        exact s3_phaseGroupSpec_exists fun r _ => by
          unfold ofBytesEnv
          exact (recordDeserializeCancelEnv_fine_groupSpec (encodeRecord r)).of_imp fun _ h => h.2
  have hload := w3BoxedStoreStepEnv_groupSpec fineCostModel 24
    (hAddrG.seq (hGetSessG.seq (hOptDeserG.seq hf)))
  have hkp := w3BoxedStoreStepEnv_groupSpec fineCostModel 16
    (hGetKpG.seq ((s3_ikpTryFrom_groups fineCostModel hikp_w).seq hf))
  have hspqrG := initialStateEnv_groupSpec fineCostModel w.F w.x_spqr
  have hRegMalG : PhaseGroupSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
      (3 * FineScale) := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id") with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      · exact PhaseGroupSpec.rustAlloc_any fineCostModel 14 1
  have hreg := w3BoxedStoreStepEnv_groupSpec fineCostModel 16
    (hGetRegG.seq (hRegMalG.seq hf))
  have hSaveTailG : PhaseGroupSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity w.x.peer.val w.peerKey
        (StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name))
      (9 * FineScale) := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseGroupSpec fineCostModel PublicKeySerializeEnv (3 * FineScale) := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
      have hput := s3_dirPutStr_opened_groups fineCostModel
        (dir := StoresGhost.opened.identity.peers) rfl w.x.peer.val.name w.peerKey.serialize
      exact (hf.seq (hpks.seq hput)).mono (by omega)
  have hsave := w3BoxedStoreStepEnv_groupSpec fineCostModel 32 (hGetPeersG.seq hSaveTailG)
  have hSerG := s3_recordSerializeSeqFree_aliceInitiated_groups halice
  have hPutSessG := s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
    (addressText w.x.peer.val) (encodeRecord w.r_rec)
  have hstore := w3BoxedStoreStepEnv_groupSpec fineCostModel 32 (hAddrG.seq (hSerG.seq hPutSessG))
  have hfull := w3InitiateFullEnvWide_groupSpec fineCostModel w.x.peer.name.bytes.length
    htrust hload hkp hspqrG hreg hsave hstore
  exact hfull.mono (by decide)

end S3aHelpers

/-- Binary-kit W3 (`init`) `SingleSlotFineSpec` at `W3InitBinaryKitSlotEnvFixed` under the
`105`-byte `identity-key-pair` cap. -/
def binaryKitW3Fixed_fineSpec (g : RunCall)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    SingleSlotFineSpec
      (match g.c with
       | .init _ _ => fun evs =>
         ∃ w : W3BinaryInitParams,
           W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
       | _ => fun _ => False) where
  cum := w3InitRealCum + 4500000
  live := w3InitRealLive + 65536
  peak := w3InitRealPeak + 65536
  maxReq := w3InitRealMaxReq + 65536
  grpS := w3InitRealGrpS + 1500 * FineScale
  credit := by
    cases g.c with
    | keygen | send _ | recv _ =>
      exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | init peerAddr dir =>
      exact s3_phaseCreditSpec_exists fun w hdom => s3_w3Fixed_credit hdom hikp
  live_le_peak := Nat.add_le_add_right w3InitReal_caps_le.2.2.1 65536
  groups := by
    cases g.c with
    | keygen | send _ | recv _ =>
      exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _)
    | init peerAddr dir =>
      exact s3_phaseGroupSpec_exists fun w hdom => s3_w3Fixed_groups hdom hikp

/-! ## W4 (`recv` PreKey) Binary-Kit Slot Bounds -/

def binaryKitW4FixedCum : Nat := d3RecvW4ExtCum + 2000000
def binaryKitW4FixedLive : Nat := d3RecvW4ExtLive
def binaryKitW4FixedPeak : Nat := d3RecvW4ExtPeak
def binaryKitW4FixedMaxReq : Nat := 4194368
def binaryKitW4FixedGrpS : Nat := d3RecvW4ExtGrpS + 2000 * FineScale

private def s3a_spkRank (c : Nat) : Nat :=
  if 4900 ≤ c then 0
  else if 4096 ≤ c then 1
  else if 2048 ≤ c then 2
  else if 1024 ≤ c then 3
  else if 512 ≤ c then 4
  else if 256 ≤ c then 5
  else if 128 ≤ c then 6
  else if 64 ≤ c then 7
  else if 32 ≤ c then 8
  else if 16 ≤ c then 9
  else if 8 ≤ c then 10
  else if 4 ≤ c then 11
  else if 2 ≤ c then 12
  else if 1 ≤ c then 13
  else 14

private theorem s3a_spkRank_spec (c : Nat) :
    (4900 ≤ c ∧ s3a_spkRank c = 0) ∨
    (4096 ≤ c ∧ c < 4900 ∧ s3a_spkRank c = 1) ∨
    (2048 ≤ c ∧ c < 4096 ∧ s3a_spkRank c = 2) ∨
    (1024 ≤ c ∧ c < 2048 ∧ s3a_spkRank c = 3) ∨
    (512 ≤ c ∧ c < 1024 ∧ s3a_spkRank c = 4) ∨
    (256 ≤ c ∧ c < 512 ∧ s3a_spkRank c = 5) ∨
    (128 ≤ c ∧ c < 256 ∧ s3a_spkRank c = 6) ∨
    (64 ≤ c ∧ c < 128 ∧ s3a_spkRank c = 7) ∨
    (32 ≤ c ∧ c < 64 ∧ s3a_spkRank c = 8) ∨
    (16 ≤ c ∧ c < 32 ∧ s3a_spkRank c = 9) ∨
    (8 ≤ c ∧ c < 16 ∧ s3a_spkRank c = 10) ∨
    (4 ≤ c ∧ c < 8 ∧ s3a_spkRank c = 11) ∨
    (2 ≤ c ∧ c < 4 ∧ s3a_spkRank c = 12) ∨
    (1 ≤ c ∧ c < 2 ∧ s3a_spkRank c = 13) ∨
    (c = 0 ∧ s3a_spkRank c = 14) := by
  by_cases h0 : 4900 ≤ c; · left; exact ⟨h0, by simp [s3a_spkRank, h0]⟩
  right; by_cases h1 : 4096 ≤ c; · left; exact ⟨h1, by omega, by simp [s3a_spkRank, h0, h1]⟩
  right; by_cases h2 : 2048 ≤ c; · left; exact ⟨h2, by omega, by simp [s3a_spkRank, h0, h1, h2]⟩
  right; by_cases h3 : 1024 ≤ c; · left; exact ⟨h3, by omega, by simp [s3a_spkRank, h0, h1, h2, h3]⟩
  right; by_cases h4 : 512 ≤ c; · left; exact ⟨h4, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4]⟩
  right; by_cases h5 : 256 ≤ c; · left; exact ⟨h5, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5]⟩
  right; by_cases h6 : 128 ≤ c; · left; exact ⟨h6, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6]⟩
  right; by_cases h7 : 64 ≤ c; · left; exact ⟨h7, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7]⟩
  right; by_cases h8 : 32 ≤ c; · left; exact ⟨h8, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8]⟩
  right; by_cases h9 : 16 ≤ c; · left; exact ⟨h9, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]⟩
  right; by_cases h10 : 8 ≤ c; · left; exact ⟨h10, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩
  right; by_cases h11 : 4 ≤ c; · left; exact ⟨h11, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]⟩
  right; by_cases h12 : 2 ≤ c; · left; exact ⟨h12, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]⟩
  right; by_cases h13 : 1 ≤ c
  · left; exact ⟨h13, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]⟩
  · right; exact ⟨by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]⟩

private theorem s3a_spkRank_le_14 (c : Nat) : s3a_spkRank c ≤ 14 := by
  have := s3a_spkRank_spec c
  omega

private theorem s3a_spkRank_step {c v nc : Nat}
    (hcv : c < v) (hv : v ≤ 4900) (h2c : 2 * c ≤ nc) (hvn : v ≤ nc) :
    s3a_spkRank nc + 1 ≤ s3a_spkRank c := by
  have := s3a_spkRank_spec c
  have := s3a_spkRank_spec nc
  omega

private def s3a_spkPot (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
  s3a_spkRank caps.pub + s3a_spkRank caps.priv + s3a_spkRank caps.sig

private theorem s3a_spkPot_zero :
    s3a_spkPot LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 42 := by
  decide

private theorem s3a_spkPot_set_step
    {caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps}
    {f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField}
    {v nc : Nat}
    (hcv : caps.get f < v) (hv : v ≤ 4900) (h2c : 2 * caps.get f ≤ nc) (hvn : v ≤ nc) :
    s3a_spkPot (caps.set f nc) + 1 ≤ s3a_spkPot caps := by
  have hstep := s3a_spkRank_step hcv hv h2c hvn
  cases f <;> simp only [s3a_spkPot,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at hstep ⊢ <;> omega

private theorem s3a_optByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.OptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · intro _ hm; nomatch hm
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨1, cap, hm⟩

private theorem s3a_twoOptByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.TwoOptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, h1, h2, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hm1 | hm2
  · exact s3a_optByteFree_freeOnly h1 ev hm1
  · exact s3a_optByteFree_freeOnly h2 ev hm2

private theorem s3a_dropDecodeError_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DropDecodeErrorEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨8, 72, hm⟩
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_append, List.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨8, c * 32, rfl⟩
    · exact ⟨8, 72, rfl⟩

private theorem s3a_signedOptByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.OptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · intro _ hm; nomatch hm
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨1, cap, hm⟩

private theorem s3a_spkEpilogue_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkEpilogueFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hm12 | hm3
  · rcases List.mem_append.mp hm12 with hm1 | hm2
    · exact s3a_signedOptByteFree_freeOnly h1 ev hm1
    · exact s3a_signedOptByteFree_freeOnly h2 ev hm2
  · exact s3a_signedOptByteFree_freeOnly h3 ev hm3

private theorem s3a_errCleanup_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨eF, eD, hF, hD, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hmF | hmD
  · exact s3a_twoOptByteFree_freeOnly hF ev hmF
  · exact s3a_dropDecodeError_freeOnly hD ev hmD

private theorem s3a_ikpPostCleanup_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with h1 | h2
  · exact s3a_twoOptByteFree_freeOnly h1
  · exact s3a_errCleanup_freeOnly h2

section S3aHoleAHelpers

open CryptoVerification.SignalSession.Cli (keyName)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams
   W4BinaryRecvPrekeyPathBWideEnv W4BinaryStageP1UntrustedEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryKpkMarkStepEnvFixed W4BinaryRecvPrekeyPathAWideEnvFixed
   W4BinaryRecvPrekeyPathCWideEnvFixed W4BinaryRecvPrekeyWideSlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)

private def s3a_spkFuel4900 (c : Nat) : Nat :=
  if c < 8 then 11
  else if c < 16 then 10
  else if c < 32 then 9
  else if c < 64 then 8
  else if c < 128 then 7
  else if c < 256 then 6
  else if c < 512 then 5
  else if c < 1024 then 4
  else if c < 2048 then 3
  else if c < 4096 then 2
  else if c < 4900 then 1
  else 0

private theorem s3a_spkFuel4900_spec (c : Nat) :
    (c < 8 ∧ s3a_spkFuel4900 c = 11) ∨
    (8 ≤ c ∧ c < 16 ∧ s3a_spkFuel4900 c = 10) ∨
    (16 ≤ c ∧ c < 32 ∧ s3a_spkFuel4900 c = 9) ∨
    (32 ≤ c ∧ c < 64 ∧ s3a_spkFuel4900 c = 8) ∨
    (64 ≤ c ∧ c < 128 ∧ s3a_spkFuel4900 c = 7) ∨
    (128 ≤ c ∧ c < 256 ∧ s3a_spkFuel4900 c = 6) ∨
    (256 ≤ c ∧ c < 512 ∧ s3a_spkFuel4900 c = 5) ∨
    (512 ≤ c ∧ c < 1024 ∧ s3a_spkFuel4900 c = 4) ∨
    (1024 ≤ c ∧ c < 2048 ∧ s3a_spkFuel4900 c = 3) ∨
    (2048 ≤ c ∧ c < 4096 ∧ s3a_spkFuel4900 c = 2) ∨
    (4096 ≤ c ∧ c < 4900 ∧ s3a_spkFuel4900 c = 1) ∨
    (4900 ≤ c ∧ s3a_spkFuel4900 c = 0) := by
  by_cases h0 : c < 8; · left; exact ⟨h0, by simp [s3a_spkFuel4900, h0]⟩
  right; by_cases h1 : c < 16; · left; exact ⟨by omega, h1, by simp [s3a_spkFuel4900, h0, h1]⟩
  right; by_cases h2 : c < 32; · left; exact ⟨by omega, h2, by simp [s3a_spkFuel4900, h0, h1, h2]⟩
  right; by_cases h3 : c < 64; · left; exact ⟨by omega, h3, by simp [s3a_spkFuel4900, h0, h1, h2, h3]⟩
  right; by_cases h4 : c < 128; · left; exact ⟨by omega, h4, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4]⟩
  right; by_cases h5 : c < 256; · left; exact ⟨by omega, h5, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5]⟩
  right; by_cases h6 : c < 512; · left; exact ⟨by omega, h6, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6]⟩
  right; by_cases h7 : c < 1024; · left; exact ⟨by omega, h7, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7]⟩
  right; by_cases h8 : c < 2048; · left; exact ⟨by omega, h8, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8]⟩
  right; by_cases h9 : c < 4096; · left; exact ⟨by omega, h9, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]⟩
  right; by_cases h10 : c < 4900
  · left; exact ⟨by omega, h10, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩
  · right; exact ⟨by omega, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩

private theorem s3a_spkFuel4900_le_12 (c : Nat) : s3a_spkFuel4900 c ≤ 12 := by
  have := s3a_spkFuel4900_spec c
  omega

private theorem s3a_spkFuel4900_step_raw {c nc v : Nat}
    (hv : v ≤ 4900) (hlt : c < v) (hnc : nc = max (max v (2 * c)) 8) :
    s3a_spkFuel4900 nc + 1 ≤ s3a_spkFuel4900 c ∧ nc ≤ 9808 ∧ 1 ≤ nc := by
  have := s3a_spkFuel4900_spec c
  have := s3a_spkFuel4900_spec nc
  omega

private def s3a0_EntriesFromNorm (files : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, Arm64.normalizePath p = k ∧ (p, bs) ∈ files

private theorem s3a0_entriesFromNorm_empty (files : List (String × List (BitVec 8))) :
    s3a0_EntriesFromNorm files ({} : Arm64.FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem s3a0_entriesFromNorm_setEntry_dir {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) (pref : Arm64.FsPath) :
    s3a0_EntriesFromNorm files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem s3a0_entriesFromNorm_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List Arm64.FsPath) {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) :
    s3a0_EntriesFromNorm files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (s3a0_entriesFromNorm_setEntry_dir h hd)

private theorem s3a0_entriesFromNorm_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) :
    s3a0_EntriesFromNorm files
      (dirs.foldl
        (fun acc d => (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (s3a0_entriesFromNorm_foldl_dirs _ h)

private theorem s3a0_entriesFromNorm_setFile {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    s3a0_EntriesFromNorm files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold Arm64.FsState.setFile Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i heq
    have hk_eq : Arm64.normalizePath p = k := (beq_iff_eq.mp heq).symm
    injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, hk_eq, hmem⟩
  · exact h k bs' hk

private theorem s3a0_entriesFromNorm_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm allFiles fs) :
    s3a0_EntriesFromNorm allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc :=
            ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
              (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := s3a0_entriesFromNorm_foldl_dirs
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast) h
    have hset := s3a0_entriesFromNorm_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem s3a0_initFsState_files_mem_norm {inputs : Arm64.Process.ProcessInputs} {q : String}
    {bs : List (BitVec 8)}
    (h : (Arm64.Process.initFsState inputs).files q = some (.file bs)) :
    ∃ p, Arm64.normalizePath p = Arm64.normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := s3a0_entriesFromNorm_foldl_outer_dirs inputs.dirs
    (s3a0_entriesFromNorm_empty inputs.files)
  have hf := s3a0_entriesFromNorm_foldl_files inputs.files (fun _ hx => hx) hd
  unfold Arm64.FsState.files Arm64.FsState.getEntry at h
  split at h
  · cases h
  · exact hf (Arm64.normalizePath q) bs h

private theorem s3a0_cliIo_rd_eq_ok_nil_or_files_some {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
        (CryptoVerification.SignalSession.Cli.MainHops.pathStr path) = some (.file bs) := by
  change CryptoVerification.SignalSession.Cli.MainHops.cliRd
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files path =
        .ok bs at hrd
  unfold CryptoVerification.SignalSession.Cli.MainHops.cliRd at hrd; split at hrd
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

private theorem s3a0_splitSlash_go_append_slash (cur a b : List Char) :
    Arm64.splitSlash.go cur (a ++ ('/' :: b)) =
      Arm64.splitSlash.go cur a ++ Arm64.splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, Arm64.splitSlash.go, ih []]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        Arm64.splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem s3a0_normalizePath_append_slash (a b : String) :
    Arm64.normalizePath (a ++ "/" ++ b) = Arm64.normalizePath a ++ Arm64.normalizePath b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [htl, s3a0_splitSlash_go_append_slash [] a.toList b.toList, List.filter_append]

private theorem s3a0_splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    rw [Arm64.splitSlash.go.eq_3 cur c cs hc,
      s3a0_splitSlash_go_no_slash cs (c :: cur) (fun hm => h (List.Mem.tail _ hm))]
    simp [List.reverse_cons, List.append_assoc]

private theorem s3a0_ofList_toList (s : String) : String.ofList s.toList = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp

private theorem s3a0_normalizePath_single {s : String}
    (hns : '/' ∉ s.toList) (hne : s.toList ≠ []) (hnd : s ≠ ".") :
    Arm64.normalizePath s = [s] := by
  have hsp : Arm64.splitSlash s = [s] := by
    unfold Arm64.splitSlash
    rw [s3a0_splitSlash_go_no_slash s.toList [] hns, List.reverse_nil, List.nil_append,
      s3a0_ofList_toList]
  have hne_str : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have hs : s = "" := by simpa [String.isEmpty_iff] using he
    subst hs; exact hne (by decide)
  have hnd_b : (s != ".") = true := bne_iff_ne.mpr hnd
  unfold Arm64.normalizePath
  rw [hsp]
  simp [hne_str, hnd_b]

private theorem s3a0_cons_head_ne {a b : String} {xs ys : List String}
    (hne : a ≠ b) : a :: xs ≠ b :: ys := by
  intro h; injection h with hab _; exact hne hab

private theorem s3a0_singleton_ne_pair {a d s : String} : ([a] : List String) ≠ [d, s] := by
  intro h; injection h with _ h2; cases h2

private theorem s3a0_norm_subdir_ne_ikp {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ "identity-key-pair") :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ ["identity-key-pair"] := by
  rw [s3a0_normalizePath_append_slash dir sub, hdir, List.singleton_append]
  intro h; injection h with hd _; exact hne hd

private theorem s3a0_norm_subdir_eq {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) :
    Arm64.normalizePath ((dir ++ "/") ++ sub) = dir :: Arm64.normalizePath sub := by
  rw [s3a0_normalizePath_append_slash dir sub, hdir, List.singleton_append]

private theorem s3a0_norm_subdir_ne_pair {dir sub d s : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ d) :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ [d, s] := by
  rw [s3a0_norm_subdir_eq hdir]
  exact s3a0_cons_head_ne hne

private def s3a0_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem s3a0_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem s3a0_utf8_eq_kutf8 (s : String) : utf8 s = s3a0_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, s3a0_kutf8, List.utf8Encode, s3a0_byteArray_toList_eq_data]

private theorem s3a0_ofList_append (l₁ l₂ : List Char) :
    String.ofList (l₁ ++ l₂) = String.ofList l₁ ++ String.ofList l₂ := by
  apply String.ext
  simp [String.toList_append]

private theorem s3a0_pathStr_append (a b : List (BitVec 8)) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (a ++ b) =
      CryptoVerification.SignalSession.Cli.MainHops.pathStr a ++
        CryptoVerification.SignalSession.Cli.MainHops.pathStr b := by
  unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
  rw [List.map_append, s3a0_ofList_append]

private theorem s3a0_decimalText_bytes (n : Nat) :
    CryptoVerification.SignalSession.Cli.decimalText n ≠ [] ∧
      ∀ b ∈ CryptoVerification.SignalSession.Cli.decimalText n,
        0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  refine Nat.strongRecOn n fun n ih => ?_
  by_cases hn : n < 10
  · rw [CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit n hn]
    refine ⟨List.cons_ne_nil _ _, fun b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    rw [BitVec.toNat_ofNat]
    omega
  · rw [CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_ge10 n (by omega)]
    obtain ⟨hne, hmem⟩ := ih (n / 10) (by omega)
    refine ⟨fun h => hne (List.append_eq_nil_iff.mp h).1, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb1 | hb2
    · exact hmem b hb1
    · rw [List.mem_singleton] at hb2; subst hb2
      rw [BitVec.toNat_ofNat]
      omega

private theorem s3a0_pathStr_keyName_props (id : BitVec 32) :
    let s := CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id)
    Arm64.normalizePath s = [s] ∧ '.' ∉ s.toList := by
  intro s
  obtain ⟨hne_b, hdig_b⟩ := s3a0_decimalText_bytes id.toNat
  have hs_list : s.toList =
      (CryptoVerification.SignalSession.Cli.decimalText id.toNat).map
        (fun b => Char.ofNat b.toNat) := by
    simp [s, CryptoVerification.SignalSession.Cli.MainHops.pathStr, keyName]
  have hne : s.toList ≠ [] := by
    rw [hs_list]
    intro h
    exact hne_b (List.map_eq_nil_iff.mp h)
  have hchars : ∀ c ∈ s.toList, c ≠ '/' ∧ c ≠ '.' := by
    rw [hs_list]
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hlo, hhi⟩ := hdig_b b hb
    have h10 :
        b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨ b.toNat = 52 ∨
          b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨ b.toNat = 56 ∨ b.toNat = 57 := by
      omega
    rcases h10 with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hns : '/' ∉ s.toList := fun hm => (hchars '/' hm).1 rfl
  have hndot : '.' ∉ s.toList := fun hm => (hchars '.' hm).2 rfl
  have hnd : s ≠ "." := by
    intro heq; rw [heq] at hndot
    exact hndot (by decide)
  exact ⟨s3a0_normalizePath_single hns hne hnd, hndot⟩

private theorem s3a0_pathStr_pathOf_keyName {dir : String}
    (hdir_ne : utf8 dir ≠ [])
    (hdir_str : CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 dir) = dir)
    (id : BitVec 32) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (pathOf (utf8 dir) (keyName id)) =
      (dir ++ "/") ++ CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id) := by
  have hp : pathOf (utf8 dir) (keyName id) = utf8 dir ++ utf8 "/" ++ keyName id := by
    unfold pathOf; simp [hdir_ne]
  have hsl : CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "/") = "/" := by
    unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [s3a0_utf8_eq_kutf8]; rfl
  rw [hp, s3a0_pathStr_append, s3a0_pathStr_append, hdir_str, hsl]

private theorem s3a0_toString_nat_props (n : Nat) :
    (toString n).toList ≠ [] ∧ '/' ∉ (toString n).toList := by
  obtain ⟨hne, hdig⟩ := s3a0_decimalText_bytes n
  refine ⟨?_, ?_⟩
  · intro hnil
    apply hne
    change utf8 (toString n) = []
    rw [s3a0_utf8_eq_kutf8]
    unfold s3a0_kutf8
    rw [hnil]
    rfl
  · intro hsl
    have hu8 : UInt8.ofNat 47 ∈ (toString n).toList.flatMap String.utf8EncodeChar :=
      List.mem_flatMap.mpr ⟨'/', hsl, by decide⟩
    have hbv : (47#8 : BitVec 8) ∈ s3a0_kutf8 (toString n) :=
      List.mem_map.mpr ⟨UInt8.ofNat 47, hu8, by decide⟩
    rw [← s3a0_utf8_eq_kutf8] at hbv
    have hge := (hdig 47#8 hbv).1
    exact absurd hge (by decide)

private theorem s3a0_baseKeysFile_norm_ne {s : String} (hnodot : '.' ∉ s.toList)
    (id : BitVec 32) (dir : String) :
    Arm64.normalizePath (CryptoVerification.SignalSession.baseKeysFile id) ≠ [dir, s] := by
  obtain ⟨hne_n, hns_n⟩ := s3a0_toString_nat_props id.toNat
  let bk := toString id.toNat ++ ".base-keys"
  have hbk_eq : CryptoVerification.SignalSession.baseKeysFile id =
      ("last-resort-kyber-pre-keys" ++ "/") ++ bk := by
    unfold CryptoVerification.SignalSession.baseKeysFile
    simp [bk, String.append_assoc]
  have hbk_ns : '/' ∉ bk.toList := by
    rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hns_n h1
    · exact absurd h2 (by decide)
  have hbk_ne : bk.toList ≠ [] := by
    rw [String.toList_append]
    intro hm
    exact hne_n (List.append_eq_nil_iff.mp hm).1
  have hbk_nd : bk ≠ "." := by
    intro hd
    have hlen1 : bk.toList.length = 1 := by rw [hd]; decide
    have hlen10 : 10 ≤ bk.toList.length := by
      rw [String.toList_append, List.length_append]
      have hsfx : (".base-keys").toList.length = 10 := by decide
      omega
    omega
  have hbk_norm : Arm64.normalizePath bk = [bk] :=
    s3a0_normalizePath_single hbk_ns hbk_ne hbk_nd
  rw [hbk_eq, s3a0_norm_subdir_eq (by decide), hbk_norm]
  intro heq
  injection heq with _ hseg
  injection hseg with hbks
  apply hnodot
  rw [← hbks, String.toList_append]
  exact List.mem_append_right _ (by decide)

private theorem s3a0_encodeVarintAux_len_le :
    ∀ (k : Nat) (v : BitVec 64),
      (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      have ih := s3a0_encodeVarintAux_len_le k (v >>> 7)
      omega

private theorem s3a0_encodeKey_len_le_10 (tag : Nat)
    (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    (CryptoVerification.LibsignalProtoCodec.encodeKey tag wt).length ≤ 10 := by
  unfold CryptoVerification.LibsignalProtoCodec.encodeKey
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  exact s3a0_encodeVarintAux_len_le 10 _

private theorem s3a0_encodeProto3Uint32Field_len_le_20 (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Uint32Field
    CryptoVerification.LibsignalProtoCodec.encodeUint32Field
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := s3a0_encodeKey_len_le_10 tag .varint
    have hv := s3a0_encodeVarintAux_len_le 10 (BitVec.zeroExtend 64 v)
    omega

private theorem s3a0_encodeProto3Fixed64Field_len_le_18 (tag : Nat) (v : BitVec 64) :
    (CryptoVerification.RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Fixed64Field
    CryptoVerification.RecordCodecs.le64Bytes
  split_ifs
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hk := s3a0_encodeKey_len_le_10 tag .sixtyFourBit
    omega

private theorem s3a0_encodeProto3BytesField_len_le (tag : Nat) (v : List (BitVec 8)) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := s3a0_encodeKey_len_le_10 tag .lengthDelimited
    have hv := s3a0_encodeVarintAux_len_le 10 (BitVec.ofNat 64 v.length)
    omega

private theorem s3a0_ikp_encode_len_le_105
    (P : CryptoVerification.E2E.PEParams) (st : CryptoVerification.SignalSession.PqParty) :
    (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
        st.me.idPriv.toList⟩).length ≤ 105 := by
  unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3BytesField_len_le 1
    (CryptoVerification.E2E.djbKey
      (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes)
  have h2 := s3a0_encodeProto3BytesField_len_le 2 st.me.idPriv.toList
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : st.me.idPriv.toList.length = 32 := st.me.idPriv.toList_length
  omega

private theorem s3a0_signedRecordBytes_len_le_230
    (P : CryptoVerification.E2E.PEParams) (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqSignedKey) :
    (CryptoVerification.SignalSession.signedRecordBytes P.C id k).length ≤ 230 := by
  unfold CryptoVerification.SignalSession.signedRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 k.priv.toList
  have h4 := s3a0_encodeProto3BytesField_len_le 4 k.sig.toList
  have h5 := s3a0_encodeProto3Fixed64Field_len_le_18 5 k.timestamp
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : k.priv.toList.length = 32 := k.priv.toList_length
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem s3a0_oneTimeRecordBytes_len_le_125
    (P : CryptoVerification.E2E.PEParams) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (CryptoVerification.SignalSession.oneTimeRecordBytes P.C id sk).length ≤ 125 := by
  unfold CryptoVerification.SignalSession.oneTimeRecordBytes
    CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 sk.toList
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : sk.toList.length = 32 := sk.toList_length
  omega

private theorem s3a0_kyberRecordBytes_len_le_4900
    (id : BitVec 32) (k : CryptoVerification.SignalSession.PqKyberKey) :
    (CryptoVerification.SignalSession.kyberRecordBytes id k).length ≤ 4900 := by
  unfold CryptoVerification.SignalSession.kyberRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2 (CryptoVerification.E2E.kyberKey k.pub)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 (0x08#8 :: k.sec.toList)
  have h4 := s3a0_encodeProto3BytesField_len_le 4 k.sig.toList
  have h5 := s3a0_encodeProto3Fixed64Field_len_le_18 5 k.timestamp
  have hpub : (CryptoVerification.E2E.kyberKey k.pub).length = 1569 := by
    simp [CryptoVerification.E2E.kyberKey]
  have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem s3a0_bundle_norm_ne_ikp {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir) :
    Arm64.normalizePath p ≠ ["identity-key-pair"] := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _; subst hp; decide

private theorem s3a0_bundle_norm_ne_pair {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p d s : String} {bs : List (BitVec 8)}
    (hd : "bundle" ≠ d)
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir) :
    Arm64.normalizePath p ≠ [d, s] := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _; subst hp
    have hn : Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/identity-key") =
        ["bundle", "identity-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/registration-id") =
          ["bundle", "registration-id"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/signed-pre-key") =
          ["bundle", "signed-pre-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/kyber-pre-key") =
          ["bundle", "kyber-pre-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _; subst hp
      have hn :
          Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/one-time-pre-key") =
            ["bundle", "one-time-pre-key"] := by decide
      rw [hn]; exact s3a0_cons_head_ne hd

private theorem s3a0_encodeDir_norm_ikp_len_le_105
    {P : CryptoVerification.E2E.PEParams} {st : CryptoVerification.SignalSession.PqParty}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st)
    (hnorm : Arm64.normalizePath p = ["identity-key-pair"]) :
    bs.length ≤ 105 := by
  unfold CryptoVerification.SignalSession.encodeDir at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
    · injection h with _ hbs; subst hbs; exact s3a0_ikp_encode_len_le_105 P st
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "identities") (by decide) (by decide))
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "sessions") (by decide) (by decide))
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "signed-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (s3a0_norm_subdir_ne_ikp (dir := "one-time-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (s3a0_norm_subdir_ne_ikp (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
    · injection h2 with hp_eq _; subst hp_eq
      unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
      rw [String.append_assoc] at hnorm
      exact absurd hnorm
        (s3a0_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_ownIkp_le_105
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105 := by
  intro bs hrd
  change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 105
  · have hpth :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
          "identity-key-pair" := by
      change CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "identity-key-pair") =
        "identity-key-pair"
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]
      rfl
    rw [hpth] at hfile
    obtain ⟨p, hp_norm, hp_mem⟩ := s3a0_initFsState_files_mem_norm hfile
    have hikp_norm : Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
    rw [hikp_norm] at hp_norm
    have hp_files : (p, bs) ∈ i.files := hp_mem
    obtain ⟨st, _, hcase⟩ := hi
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
        ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
    · simp only [CryptoVerification.SignalSession.pqInitInputs,
        CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
      rcases hp_files with (hed | hbun) | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · exact absurd hp_norm (s3a0_bundle_norm_ne_ikp hbun)
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqSendInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)

private theorem s3a0_cliPqInputs_dir_file_mem
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i)
    {dir s : String} {bs : List (BitVec 8)}
    (hdir_norm : Arm64.normalizePath dir = [dir])
    (hdir_ne_bundle : "bundle" ≠ dir)
    (hs_norm : Arm64.normalizePath s = [s])
    (hfile : (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
      ((dir ++ "/") ++ s) = some (.file bs)) :
    ∃ st p, (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st ∧
      Arm64.normalizePath p = [dir, s] := by
  obtain ⟨p, hp_norm, hp_mem⟩ := s3a0_initFsState_files_mem_norm hfile
  rw [s3a0_norm_subdir_eq hdir_norm, hs_norm] at hp_norm
  have hp_files : (p, bs) ∈ i.files := hp_mem
  have hcoins_norm : Arm64.normalizePath CryptoVerification.SignalSession.coinsFile = ["coins"] := by
    decide
  obtain ⟨st, _, hcase⟩ := hi
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
      ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
  · simp only [CryptoVerification.SignalSession.pqInitInputs,
      CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
    rcases hp_files with (hed | hbun) | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · exact absurd hp_norm (s3a0_bundle_norm_ne_pair hdir_ne_bundle hbun)
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqSendInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair

private theorem s3a0_encodeDir_hdr_peer_sess_ne_pair
    {P : CryptoVerification.E2E.PEParams} {st : CryptoVerification.SignalSession.PqParty}
    {p dir s : String} {bs : List (BitVec 8)}
    (hid_ne : "identities" ≠ dir) (hsess_ne : "sessions" ≠ dir)
    (hhps :
      ((p, bs) ∈
        [(CryptoVerification.SignalSession.addressFile,
            CryptoVerification.SignalSession.textBytes
              (CryptoVerification.SignalSession.partyAddress st.party).text),
         (CryptoVerification.SignalSession.identityKeyPairFile,
            CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
              ⟨CryptoVerification.E2E.djbKey
                (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
                st.me.idPriv.toList⟩),
         (CryptoVerification.SignalSession.registrationIdFile,
            CryptoVerification.SignalSession.le32 st.me.regId)] ∨
       (p, bs) ∈ (match st.peerId with
         | some k =>
           [(CryptoVerification.SignalSession.identityFile
               (CryptoVerification.E2E.partyAddressName st.party.other), k.serialize)]
         | none => [])) ∨
      (p, bs) ∈ (match st.session with
        | some (x, g) =>
          [(CryptoVerification.SignalSession.sessionFile
              (CryptoVerification.SignalSession.partyAddress st.party.other),
            CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) g)]
        | none => [])) :
    Arm64.normalizePath p ≠ [dir, s] := by
  rcases hhps with (hf_hdr | hf_peer) | hf_sess
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp
      have hn : Arm64.normalizePath CryptoVerification.SignalSession.addressFile = ["address"] := by
        decide
      rw [hn]; exact s3a0_singleton_ne_pair
    · injection h with hp _; subst hp
      have hn :
          Arm64.normalizePath CryptoVerification.SignalSession.identityKeyPairFile =
            ["identity-key-pair"] := by decide
      rw [hn]; exact s3a0_singleton_ne_pair
    · injection h with hp _; subst hp
      have hn :
          Arm64.normalizePath CryptoVerification.SignalSession.registrationIdFile =
            ["registration-id"] := by decide
      rw [hn]; exact s3a0_singleton_ne_pair
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact s3a0_norm_subdir_ne_pair (dir := "identities") (by decide) hid_ne
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact s3a0_norm_subdir_ne_pair (dir := "sessions") (by decide) hsess_ne

private theorem s3a0_signed_le_230
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230 := by
  intro id bs hrd
  change cliIo.rd (runFiles i) (pathOf (utf8 "signed-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 230
  · have hdir_ne : utf8 "signed-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "signed-pre-keys") =
          "signed-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨id', k⟩, _, h⟩
      injection h with _ hbs; subst hbs
      exact s3a0_signedRecordBytes_len_le_230 P id' k
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_oneTime_le_125
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125 := by
  intro id bs hrd
  change cliIo.rd (runFiles i) (pathOf (utf8 "one-time-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 125
  · have hdir_ne : utf8 "one-time-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "one-time-pre-keys") =
          "one-time-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨id', opt⟩, _, h⟩
      injection h with _ hbs; subst hbs
      cases opt with
      | none => exact Nat.zero_le 125
      | some sk => exact s3a0_oneTimeRecordBytes_len_le_125 P id' sk
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_kyberOneTime_le_4900
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900 := by
  intro id bs hrd
  change cliIo.rd (runFiles i)
      (pathOf (utf8 "one-time-kyber-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 4900
  · have hdir_ne : utf8 "one-time-kyber-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "one-time-kyber-pre-keys") =
          "one-time-kyber-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨id', opt⟩, _, h⟩
      injection h with _ hbs; subst hbs
      cases opt with
      | none => exact Nat.zero_le 4900
      | some k => exact s3a0_kyberRecordBytes_len_le_4900 id' k
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_kyberLastResort_le_4900
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900 := by
  intro id bs hrd
  change cliIo.rd (runFiles i)
      (pathOf (utf8 "last-resort-kyber-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 4900
  · have hdir_ne : utf8 "last-resort-kyber-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (utf8 "last-resort-kyber-pre-keys") =
          "last-resort-kyber-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, hs_nodot⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨id', k, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with _ hbs; subst hbs
        exact s3a0_kyberRecordBytes_len_le_4900 id' k
      · injection h2 with hp_eq _; subst hp_eq
        exact absurd hnorm (s3a0_baseKeysFile_norm_ne hs_nodot id' "last-resort-kyber-pre-keys")

private theorem s3a_sub0_store_file_caps (W : CliHooks) (i : Inputs)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    (∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) ∧
    (∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230) ∧
    (∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) :=
  ⟨s3a0_ownIkp_le_105 hi,
   s3a0_signed_le_230 hi,
   s3a0_oneTime_le_125 hi,
   s3a0_kyberOneTime_le_4900 hi,
   s3a0_kyberLastResort_le_4900 hi⟩

/-- `PhaseCreditSpec` for `CliSpkDecodeEnv bs` (`bs.length ≤ L ≤ 4900`, covering `L = 230` for
`spkGet` and `L = 4900` for `kpkGet`; `0` live/peak since `9808 ≤ 135167`). -/
private theorem s3a_sub1_cliSpkDecode_credit {bs : List (BitVec 8)} {L : Nat}
    (hbs : bs.length ≤ L) (hL : L ≤ 4900) :
    PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808 := by
  let smallAlloc_pos_le_94 : ∀ {v : Nat}, 0 < v →
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallAllocCost
        fineCostModel v ≤ 94 * (v + 1) := by
    intro v hv
    by_cases h12 : v ≤ 12
    · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_eq_188_of_le_12 h12; omega
    · by_cases h28 : v ≤ 28
      · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_488_of_le_28 h28; omega
      · by_cases h44 : v ≤ 44
        · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_738_of_le_44 h44; omega
        · by_cases h60 : v ≤ 60
          · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1126_of_le_60 h60; omega
          · by_cases h108 : v ≤ 108
            · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1997_of_le_108 h108; omega
            · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add v; omega
  have h_push0 : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DecodeErrorPushBoundedEnv 0) 9795 0 0 128 := by
    have hmax : 128 ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide
    have h128 : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 128 8) 9795 0 0 128 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 128)
        (by decide) hmax).mono
        (Nat.le_trans (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add 128) (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
    have hnil : PhaseCreditSpec fineCostModel (· = []) 9795 0 0 128 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    exact (hnil.or h128).of_imp fun evs hp => by
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
  have h_errTail : PhaseCreditSpec fineCostModel
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkErrTailEnv 11792 0 0 128 := by
    have hmax72 : 72 ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide
    have h72 : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 72 8) 1997 0 0 72 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
        (by decide) hmax72).mono
        (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1997_of_le_108 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
    have hfp : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv
          (· = LibsignalBinary.Heap.rustAllocEvents 72 8)
          (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DecodeErrorPushBoundedEnv 0)) 11792 0 0 128 :=
      (h72.concat h_push0).mono (by decide) (by decide) (by decide) (by decide)
    have hnil : PhaseCreditSpec fineCostModel (· = []) 11792 0 0 128 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    have h72' : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 72 8) 11792 0 0 128 :=
      h72.mono (by decide) (by decide) (by decide) (by decide)
    exact ((hnil.or h72').or hfp).of_imp fun evs he => by
      cases he with
      | nil => exact Or.inl (Or.inl rfl)
      | fromOnly => exact Or.inl (Or.inr rfl)
      | fromPush hp => exact Or.inr (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hp)
  let capsMaxLe (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) (M : Nat) : Prop :=
    caps.pub ≤ M ∧ caps.priv ≤ M ∧ caps.sig ≤ M
  let spkBytePot (M : Nat) (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    (M - caps.pub) + (M - caps.priv) + (M - caps.sig)
  let spkFuelPot (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    s3a_spkFuel4900 caps.pub + s3a_spkFuel4900 caps.priv + s3a_spkFuel4900 caps.sig
  let spkLoopCum (M rem : Nat) (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    94 * rem + 4 * spkBytePot M caps + 9539 * spkFuelPot caps + 11792
  have h_caps_get_le : ∀ {caps M} (_ : capsMaxLe caps M)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField), caps.get f ≤ M := by
    rintro caps M ⟨h1, h2, h3⟩ f
    cases f <;> simp only [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get] <;> omega
  have h_caps_set_le : ∀ {caps M nc} (_ : capsMaxLe caps M) (_ : nc ≤ M)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField), capsMaxLe (caps.set f nc) M := by
    rintro caps M nc ⟨h1, h2, h3⟩ hnc f
    cases f <;> exact
      ⟨by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set],
       by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set],
       by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set]⟩
  have h_caps_set_self : ∀ (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField),
      caps.set f (caps.get f) = caps := by
    intro caps f; cases caps; cases f <;> rfl
  have h_bytePot_step : ∀ {M caps f nc}, capsMaxLe caps M → nc ≤ M → 2 * caps.get f ≤ nc →
      4 * spkBytePot M (caps.set f nc) + 2 * nc ≤ 4 * spkBytePot M caps := by
    rintro M caps f nc ⟨h1, h2, h3⟩ hnc_le h2c
    cases f <;> simp only [spkBytePot,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at h2c ⊢ <;> omega
  have h_fuelPot_step : ∀ {caps f v nc}, v ≤ 4900 → caps.get f < v →
      nc = max (max v (2 * caps.get f)) 8 → spkFuelPot (caps.set f nc) + 1 ≤ spkFuelPot caps := by
    intro caps f v nc hv hcv hnc
    have hstep := (s3a_spkFuel4900_step_raw hv hcv hnc).1
    cases f <;> simp only [spkFuelPot,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at hstep ⊢ <;> omega
  have h_res_props : ∀ {c v : Nat}, c < v → v ≤ L →
      let nc := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v
      nc = max (max v (2 * c)) 8 ∧ 1 ≤ nc ∧ 2 * c ≤ nc ∧ v ≤ nc ∧ nc ≤ max (2 * L) 128 := by
    intro c v hcv hv; dsimp only [CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have h_noRes : ∀ {wt : CryptoVerification.LibsignalProtoCodec.WireType}
      {bs' v rest : List (BitVec 8)} {c M : Nat},
      CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs' = some (v, rest) →
      v.length ≤ c → c ≤ M → M ≤ 9800 →
      PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
          wt (BitVec.ofNat 64 c) bs') (94 * (v.length + 1)) 0 0 M := by
    intro wt bs' v rest c M hm hle hc hM
    have hmaxM : M ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; omega
    have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcore : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs' =
        if v.length = 0 then []
        else LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1 := by
      simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore, hm, hc_toNat]
    rw [show (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs') =
        (· = if v.length = 0 then []
          else LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
            LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
            LibsignalBinary.Heap.rustDeallocEvents v.length 1) by rw [hcore]]
    split_ifs with hv0
    · exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
      have hv_le_M : v.length ≤ M := Nat.le_trans hle hc
      have halloc : PhaseCreditSpec fineCostModel
          (· = LibsignalBinary.Heap.rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 M :=
        (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
          (by decide) (Nat.le_trans hv_le_M hmaxM)).mono
          (smallAlloc_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) hv_le_M
      have hres : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents
          c v.length = [] := by
        simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents, hle]
      rw [hres, List.append_nil]
      have hfree : PhaseCreditSpec fineCostModel
          (· = LibsignalBinary.Heap.rustDeallocEvents v.length 1) 0 0 0 0 :=
        PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
      exact ((halloc.concat hfree).mono
        (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.max_le.mpr ⟨Nat.le_refl M, Nat.zero_le M⟩)).of_imp fun evs he => by
          subst he
          exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl rfl
  have h_res : ∀ {wt : CryptoVerification.LibsignalProtoCodec.WireType}
      {bs' v rest : List (BitVec 8)} {c M : Nat},
      CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs' = some (v, rest) →
      c < v.length → v.length ≤ M →
      1 ≤ CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length →
      CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length ≤ M → M ≤ 9800 →
      PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
          wt (BitVec.ofNat 64 c) bs')
        (94 * (v.length + 1) + (2 * CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length + 9539))
        0 0 M := by
    intro wt bs' v rest c M hm hcv hv_le_M hnc_pos hnc_le hM
    have hmaxM : M ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; omega
    have hc_lt_M : c ≤ M := Nat.le_trans (Nat.le_of_lt hcv) hv_le_M
    have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hv_pos : 0 < v.length := Nat.lt_of_le_of_lt (Nat.zero_le c) hcv
    have hv0 : v.length ≠ 0 := Nat.ne_of_gt hv_pos
    have hcore : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs' =
        LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1 := by
      simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore, hm, hc_toNat, hv0]
    rw [show (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs') =
        (· = LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1) by rw [hcore]]
    have halloc : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 M :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (Nat.le_trans hv_le_M hmaxM)).mono
        (smallAlloc_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) hv_le_M
    have hres_ev : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length)
        (2 * CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length + 9539) 0 0 M := by
      unfold LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents
      have hnle : ¬ v.length ≤ c := Nat.not_le.mpr hcv
      simp only [hnle, ↓reduceIte]
      split_ifs with hc0
      · exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length)
          (by decide) (Nat.le_trans hnc_le hmaxM)).mono
          (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add _)
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hc_pos : 1 ≤ c := Nat.pos_of_ne_zero hc0
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := c)
          (new := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length)
          (al := 1) (by decide) hnc_pos hc_pos
          (Nat.le_trans hc_lt_M hmaxM) hnc_pos (Nat.le_trans hnc_le hmaxM)).mono
          (LibsignalBinary.Heap.Fine.ClientBounds.smallReallocCost_le_two_mul_add _)
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    exact (((halloc.concat hres_ev).concat hfree).mono
      (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl M, Nat.le_refl M⟩, Nat.zero_le M⟩)).of_imp
      fun evs he => by
        subst he
        exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append
          (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl rfl) rfl
  have h_cum_skip : ∀ {M rem' rem caps}, rem' < rem →
      spkLoopCum M rem' caps ≤ spkLoopCum M rem caps := by
    intro M rem' rem caps hlt
    dsimp only [spkLoopCum]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_left 94 (Nat.le_of_lt hlt)) _) _) _
  have h_cum_noRes : ∀ {M rem rem' v caps}, rem' + v + 1 ≤ rem →
      94 * (v + 1) + spkLoopCum M rem' caps ≤ spkLoopCum M rem caps := by
    intro M rem rem' v caps hprog
    dsimp only [spkLoopCum]
    generalize 4 * spkBytePot M caps + 9539 * spkFuelPot caps + 11792 = restPot
    have hmul : 94 * (v + 1) + 94 * rem' ≤ 94 * rem := by
      have h := Nat.mul_le_mul_left 94 (show v + 1 + rem' ≤ rem by omega)
      rwa [Nat.mul_add] at h
    generalize 94 * (v + 1) = a1 at hmul ⊢
    generalize 94 * rem' = a2 at hmul ⊢
    generalize 94 * rem = a3 at hmul ⊢
    omega
  have h_cum_res : ∀ {M rem rem' v nc caps caps'}, rem' + v + 1 ≤ rem →
      4 * spkBytePot M caps' + 2 * nc ≤ 4 * spkBytePot M caps →
      spkFuelPot caps' + 1 ≤ spkFuelPot caps →
      (94 * (v + 1) + (2 * nc + 9539)) + spkLoopCum M rem' caps' ≤ spkLoopCum M rem caps := by
    intro M rem rem' v nc caps caps' hprog hb hk
    have hmul94 : 94 * (v + 1) + 94 * rem' ≤ 94 * rem := by
      have h := Nat.mul_le_mul_left 94 (show v + 1 + rem' ≤ rem by omega)
      rwa [Nat.mul_add] at h
    have hmulK : 9539 * spkFuelPot caps' + 9539 ≤ 9539 * spkFuelPot caps := by
      have h := Nat.mul_le_mul_left 9539 hk
      rwa [Nat.mul_add, Nat.mul_one] at h
    dsimp only [spkLoopCum]
    generalize 94 * (v + 1) = a1 at hmul94 ⊢
    generalize 94 * rem' = a2 at hmul94 ⊢
    generalize 94 * rem = a3 at hmul94 ⊢
    generalize 4 * spkBytePot M caps' = b1 at hb ⊢
    generalize 4 * spkBytePot M caps = b2 at hb ⊢
    generalize 2 * nc = n2 at hb ⊢
    generalize 9539 * spkFuelPot caps' = k1 at hmulK ⊢
    generalize 9539 * spkFuelPot caps = k2 at hmulK ⊢
    generalize (9539 : Nat) = c1 at hmulK ⊢
    generalize (11792 : Nat) = c2
    omega
  have hM : max (2 * L) 128 ≤ 9800 := by omega
  have h_loopBounded : ∀ (rem : Nat) {caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps},
      rem ≤ L → capsMaxLe caps (max (2 * L) 128) →
      PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkLoopBoundedEnv rem caps)
        (spkLoopCum (max (2 * L) 128) rem caps) 0 0 (max (2 * L) 128) := by
    intro rem
    induction rem using Nat.strongRecOn with
    | ind rem ih =>
      intro caps hrem hcaps
      refine {
        req_align := fun evs he => ?_
        credit_le := fun st0 {_} he => ?_
      }
      · cases he with
        | done herr =>
          exact (h_errTail.mono (Nat.le_refl 11792)
            (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_max_right (2 * L) 128)).req_align evs herr
        | @skipStep _ rem' _ _ hlt hnext =>
          exact (ih rem' hlt (Nat.le_trans (Nat.le_of_lt hlt) hrem) hcaps).req_align evs hnext
        | @bytesStep f _ rem' _ wt bs' v rest evs₂ hm hbs_le hprog _ hnext =>
          have hc : caps.get f ≤ max (2 * L) 128 := h_caps_get_le hcaps f
          have hv : v.length ≤ L := by omega
          by_cases hle : v.length ≤ caps.get f
          · simp only [hle, ↓reduceIte, h_caps_set_self] at hnext
            have h1 := h_noRes hm hle hc hM
            have h2 := ih rem' (by omega) (by omega) hcaps
            exact ((h1.concat h2).mono (h_cum_noRes hprog)
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).req_align
              _ (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
          · have hcv : caps.get f < v.length := Nat.lt_of_not_ge hle
            simp only [hle, ↓reduceIte] at hnext
            obtain ⟨hnc_eq, hnc_pos, h2c, _, hnc_le⟩ := h_res_props hcv hv
            have hv_le_M : v.length ≤ max (2 * L) 128 := by omega
            have h1 := h_res hm hcv hv_le_M hnc_pos hnc_le hM
            have h2 := ih rem' (by omega) (by omega) (h_caps_set_le hcaps hnc_le f)
            exact ((h1.concat h2).mono
              (h_cum_res hprog (h_bytePot_step hcaps hnc_le h2c)
                (h_fuelPot_step (Nat.le_trans hv hL) hcv hnc_eq))
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).req_align
              _ (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
      · cases he with
        | done herr =>
          have hle11792 : 11792 ≤ spkLoopCum (max (2 * L) 128) rem caps :=
            Nat.le_add_left 11792 _
          exact (h_errTail.mono hle11792
            (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_max_right (2 * L) 128)).credit_le st0 herr
        | @skipStep _ rem' _ _ hlt hnext =>
          exact ((ih rem' hlt (Nat.le_trans (Nat.le_of_lt hlt) hrem) hcaps).mono
            (h_cum_skip hlt) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)).credit_le st0 hnext
        | @bytesStep f _ rem' _ wt bs' v rest evs₂ hm hbs_le hprog _ hnext =>
          have hc : caps.get f ≤ max (2 * L) 128 := h_caps_get_le hcaps f
          have hv : v.length ≤ L := by omega
          by_cases hle : v.length ≤ caps.get f
          · simp only [hle, ↓reduceIte, h_caps_set_self] at hnext
            have h1 := h_noRes hm hle hc hM
            have h2 := ih rem' (by omega) (by omega) hcaps
            exact ((h1.concat h2).mono (h_cum_noRes hprog)
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).credit_le
              st0 (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
          · have hcv : caps.get f < v.length := Nat.lt_of_not_ge hle
            simp only [hle, ↓reduceIte] at hnext
            obtain ⟨hnc_eq, hnc_pos, h2c, _, hnc_le⟩ := h_res_props hcv hv
            have hv_le_M : v.length ≤ max (2 * L) 128 := by omega
            have h1 := h_res hm hcv hv_le_M hnc_pos hnc_le hM
            have h2 := ih rem' (by omega) (by omega) (h_caps_set_le hcaps hnc_le f)
            exact ((h1.concat h2).mono
              (h_cum_res hprog (h_bytePot_step hcaps hnc_le h2c)
                (h_fuelPot_step (Nat.le_trans hv hL) hcv hnc_eq))
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).credit_le
              st0 (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
  have h_cum_zero : spkLoopCum (max (2 * L) 128) bs.length
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero ≤
        94 * L + 12 * max (2 * L) 128 + 326579 := by
    have hbp : spkBytePot (max (2 * L) 128)
        LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 3 * max (2 * L) 128 := by
      simp only [spkBytePot, LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero, Nat.sub_zero]
      omega
    have hfp : spkFuelPot LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 33 := by
      decide
    dsimp only [spkLoopCum]
    rw [hbp, hfp]
    have h1 : 94 * bs.length ≤ 94 * L := Nat.mul_le_mul_left 94 hbs
    have h2 : 4 * (3 * max (2 * L) 128) = 12 * max (2 * L) 128 := (Nat.mul_assoc 4 3 _).symm
    have h3 : 9539 * 33 + 11792 = 326579 := by decide
    rw [h2, Nat.add_assoc, h3]
    omega
  have h_loop : ∀ {fuel : Nat}, PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkLoopEnv fuel bs.length)
      (380 * L + 750000) 0 0 9808 := fun {_} =>
    (h_loopBounded bs.length hbs
      ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩).mono
      (Nat.le_trans h_cum_zero (by omega)) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  have h_or_free : ∀ {E F : List AllocEvent → Prop} {c r : Nat},
      PhaseCreditSpec fineCostModel E c 0 0 r →
      (∀ evs, F evs → FreeOnlyEvs evs) →
      PhaseCreditSpec fineCostModel
        (fun evs => E evs ∨ ∃ e1 e2, E e1 ∧ F e2 ∧ evs = e1 ++ e2) c 0 0 r := by
    intro E F c r hE hF
    have hfree : PhaseCreditSpec fineCostModel F 0 0 0 0 :=
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp hF
    have hcat : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv E F) c 0 0 r :=
      (hE.concat hfree).mono (Nat.le_of_eq (Nat.add_zero c)) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.max_le.mpr ⟨Nat.le_refl r, Nat.zero_le r⟩)
    exact ((hE.or hcat).mono (Nat.max_le.mpr ⟨Nat.le_refl c, Nat.le_refl c⟩)
      (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl r, Nat.le_refl r⟩)).of_imp fun evs h => by
        rcases h with h1 | ⟨e1, e2, h1, h2, rfl⟩
        · exact Or.inl h1
        · exact Or.inr (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append h1 h2)
  have h_spkDec : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkDecodeEnv bs.length)
      (380 * L + 750000) 0 0 9808 :=
    h_or_free h_loop fun _ h => s3a_spkEpilogue_freeOnly h
  have h_kyberDec : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.KyberDecodeEnv bs.length)
      (380 * L + 750000) 0 0 9808 :=
    h_or_free h_spkDec fun _ h => s3a_dropDecodeError_freeOnly h
  exact (h_loop.or h_kyberDec).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)

section S3aW1cSub2Helpers

open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12
   smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44
   smallAllocCost_le_1126_of_le_60 smallAllocCost_le_1997_of_le_108
   smallAllocCost_le_two_mul_add smallReallocCost_le_two_mul_add)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PreKeyDeserializeEnv RecordCodecErrStep RecordCodecLoopEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

private theorem s3a_w1c_alloc128_cost_eq :
    LibsignalBinary.Heap.Fine.fineSmallAllocCost (4 * 32) = 9789 := by
  decide

private theorem s3a_w1c_smallAllocCost_pos_le_94 {v : Nat} (hv : 0 < v) :
    HasFineReallocCredit.smallAllocCost fineCostModel v ≤ 94 * (v + 1) := by
  by_cases h12 : v ≤ 12
  · have h := smallAllocCost_eq_188_of_le_12 h12; omega
  · by_cases h28 : v ≤ 28
    · have h := smallAllocCost_le_488_of_le_28 h28; omega
    · by_cases h44 : v ≤ 44
      · have h := smallAllocCost_le_738_of_le_44 h44; omega
      · by_cases h60 : v ≤ 60
        · have h := smallAllocCost_le_1126_of_le_60 h60; omega
        · by_cases h108 : v ≤ 108
          · have h := smallAllocCost_le_1997_of_le_108 h108; omega
          · have h := smallAllocCost_le_two_mul_add v; omega

private theorem s3a_w1c_recordCodecErrStep_credit :
    PhaseCreditSpec fineCostModel RecordCodecErrStep 9789 0 0 128 := by
  have hmax : 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 9789 0 0 128 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
      (by decide) (by omega)).mono
      (Nat.le_trans (smallAllocCost_le_1997_of_le_108 (by decide)) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have h128_cost : HasFineReallocCredit.smallAllocCost fineCostModel (4 * 32) ≤ 9789 := by
    change LibsignalBinary.Heap.Fine.fineSmallAllocCost (4 * 32) ≤ 9789
    rw [s3a_w1c_alloc128_cost_eq]
  have h128 : PhaseCreditSpec fineCostModel (· = rustAllocEvents (4 * 32) 8) 9789 0 0 128 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 4 * 32)
      (by decide) hmax).mono h128_cost (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 9789 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h72).or h128).of_imp fun evs hs => by
    cases hs with
    | nil => exact Or.inl (Or.inl rfl)
    | fromErr => exact Or.inl (Or.inr rfl)
    | push0 hp =>
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl
      · omega

private theorem s3a_w1c_pkBytesMerge_125_credit {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)}
    (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 125) :
    PhaseCreditSpec fineCostModel (· = bytesMergeEventsCore wt valCap bs)
      (9789 * (2 * v.length + 1)) 0 0 256 := by
  have hmax256 : 256 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hcore : bytesMergeEventsCore wt valCap bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents valCap.toNat v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm]
  rw [show (· = bytesMergeEventsCore wt valCap bs) =
      (· = if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents valCap.toNat v.length ++
          rustDeallocEvents v.length 1) by rw [hcore]]
  split_ifs with hv0
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
    have halloc : PhaseCreditSpec fineCostModel
        (· = rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 256 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (by omega)).mono
        (s3a_w1c_smallAllocCost_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hres : PhaseCreditSpec fineCostModel
        (· = doReserveClearEvents valCap.toNat v.length) 10051 0 0 256 := by
      unfold doReserveClearEvents
      split_ifs with hle hc0
      · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
      · have hnc_le : reserveCap valCap.toNat 0 v.length ≤ 256 := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := reserveCap valCap.toNat 0 v.length) (by decide) (by omega)).mono
          (Nat.le_trans (smallAllocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hnc_le : reserveCap valCap.toNat 0 v.length ≤ 256 := by
          dsimp only [reserveCap]; omega
        have hnc_pos : 1 ≤ reserveCap valCap.toNat 0 v.length := by
          dsimp only [reserveCap]; omega
        have hc_pos : 1 ≤ valCap.toNat := Nat.pos_of_ne_zero hc0
        have hc_le : valCap.toNat ≤ 256 := by omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := valCap.toNat)
          (new := reserveCap valCap.toNat 0 v.length) (al := 1) (by decide) hnc_pos hc_pos
          (Nat.le_trans hc_le hmax256) hnc_pos (Nat.le_trans hnc_le hmax256)).mono
          (Nat.le_trans (smallReallocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    have hsum : (94 * (v.length + 1) + 10051) + 0 ≤ 9789 * (2 * v.length + 1) := by omega
    exact (((halloc.concat hres).concat hfree).mono
      hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp fun evs he => by
        subst he
        exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl

private theorem s3a_w1c_recordCodecLoop_125_ev_credit {maxLen : Nat} (hmax : maxLen ≤ 125)
    {budget : Nat} {evs : List AllocEvent} (he : RecordCodecLoopEnv budget maxLen evs) :
    PhaseCreditSpec fineCostModel (· = evs) (9789 * budget) 0 0 256 := by
  induction he with
  | nil =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | @step b _ evs₁ evs₂ h1 _ ih =>
    have hs1 : PhaseCreditSpec fineCostModel (· = evs₁) 9789 0 0 256 :=
      (s3a_w1c_recordCodecErrStep_credit.mono (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0)
        (by decide : 128 ≤ 256)).of_imp fun _ h => by subst h; exact h1
    have hsum : 9789 + 9789 * b ≤ 9789 * (b + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    exact ((hs1.concat (ih hmax)).mono hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun _ h => by subst h; exact ConcatEnv.append rfl rfl
  | @bytesStep b _ wt valCap bs v rest evs₁ evs₂ hm hbs heq _ ih =>
    subst heq
    have hprog := LibsignalBinary.Proofs.RecordCodecs.DepsBudget.mergeBytes_len_bound hm
    have hv : v.length ≤ 125 := by omega
    have hs1 := s3a_w1c_pkBytesMerge_125_credit (valCap := valCap) hm hv
    have hsum : 9789 * (2 * v.length + 1) + 9789 * b ≤ 9789 * (b + 2 * v.length + 1) := by
      have h : (2 * v.length + 1) + b = b + 2 * v.length + 1 := by omega
      rw [← Nat.mul_add, h]
    exact ((hs1.concat (ih hmax)).mono hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun _ h => by subst h; exact ConcatEnv.append rfl rfl

private theorem s3a_w1c_recordCodecLoop_125_credit {maxLen : Nat} (hmax : maxLen ≤ 125)
    (budget : Nat) :
    PhaseCreditSpec fineCostModel (RecordCodecLoopEnv budget maxLen) (9789 * budget) 0 0 256 where
  req_align evs he := (s3a_w1c_recordCodecLoop_125_ev_credit hmax he).req_align evs rfl
  credit_le st0 {_} he := (s3a_w1c_recordCodecLoop_125_ev_credit hmax he).credit_le st0 rfl

private theorem s3a_w1c_preKeyDeserialize_125_credit {len : Nat} (hlen : len ≤ 125) :
    PhaseCreditSpec fineCostModel (PreKeyDeserializeEnv len)
      (9789 * (2 * len + 3)) 0 0 256 := by
  have hE := s3a_w1c_recordCodecLoop_125_credit hlen (2 * len + 3)
  have hfree : PhaseCreditSpec fineCostModel
      LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv 0 0 0 0 :=
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h => s3a_errCleanup_freeOnly h
  have hcat : PhaseCreditSpec fineCostModel
      (ConcatEnv (RecordCodecLoopEnv (2 * len + 3) len)
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv)
      (9789 * (2 * len + 3)) 0 0 256 :=
    (hE.concat hfree).mono (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
      (by decide)
  exact ((hE.or hcat).mono (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp fun evs h => by
      rcases h with h1 | ⟨e1, e2, h1, h2, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (ConcatEnv.append h1 h2)

/-- Tight `CliPkDecodeEnv bs` (`bs.length ≤ 125`) credit bound (`9789 * 253 = 2,476,617`). -/
private theorem s3a_w1c_cliPkDecode_credit {bs : List (BitVec 8)}
    (hbs : bs.length ≤ 125) :
    PhaseCreditSpec fineCostModel (CliPkDecodeEnv bs) 2476617 0 0 256 := by
  have hmul : 9789 * (2 * bs.length + 3) ≤ 2476617 := by omega
  exact (((s3a_w1c_recordCodecLoop_125_credit hbs (2 * bs.length + 3)).or
    (s3a_w1c_preKeyDeserialize_125_credit hbs)).mono
    (Nat.max_le.mpr ⟨hmul, hmul⟩) (Nat.le_refl 0) (Nat.le_refl 0) (by decide))

/-- Tight `OptIkpTryFromEnv gr` (`bs.length ≤ 105`) credit bound (`9789 * 213 = 2,085,057`). -/
private theorem s3a_w1c_optIkpTryFrom_credit {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 2085057 0 0 256 := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hloop := s3a_w1c_recordCodecLoop_125_credit
      (Nat.le_trans hbs (by decide)) (2 * bs.length + 3)
    have hfree : PhaseCreditSpec fineCostModel
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv 0 0 0 0 :=
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h =>
        s3a_ikpPostCleanup_freeOnly h
    have hmul : 9789 * (2 * bs.length + 3) + 0 ≤ 2085057 := by omega
    exact ((hloop.concat hfree).mono hmul (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun evs ⟨e1, e2, h1, h2, heq⟩ => by
        subst heq
        exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append h1 h2

end S3aW1cSub2Helpers

section S3a5Sub5Helpers

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText decimalText)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryAcceptWideEnv W4BinaryArchiveDirectEnv W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv
   W4BinaryInitBobWideEnv W4BinaryKpkGetStepEnv W4BinaryPkGetStepEnv W4BinaryPkRemoveStepEnv
   W4BinaryPromoteArchiveEnv W4BinarySelfKpStepEnv W4BinarySelfRegIdStepEnv
   W4BinarySessLoadStepEnv W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv
   W4BinarySpkGetStepEnv W4BinaryStageP1OkEnv W4BinaryStageP2PathAWideEnv
   W4BinaryStageP2PathCWideEnv W4CloneACDomEnv W4TrialRunWideEnv mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec FreeOnlyAlign16Evs IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (PhaseCreditSpec.rustAlloc_optLarge fineSmallReallocCost_le_9789_of_le_256 optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight PhaseCreditSpec.serializePrev1_seqFree_tight
   RecordSerializeSeqFreeEnv SerializePrev1SeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom SessionCloneDom recordSerializeMaxReq_le_of_dom
   recordSerializePeak_fine_le_of_dom recordSerializeTightCum_fine_le_of_dom
   sessionClone_freshBob16K_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2TryDecryptMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv phaseCredit_archivedTrialLoop_le4 phaseCredit_promoteStateArchive)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4PqxdhAcceptEnv phaseCredit_w4BobSessionBuild_small
   phaseCredit_w4BoundedEvs_small phaseCredit_w4PqxdhAccept_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4ErrTailWideEnv W4StageP3WideEnv W4TryDecryptCloneFailWideEnv
   phaseCredit_optStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (addressText_peer_length_le_64 opened_all_dirDomainCaps phaseCreditSpec_seq_freeOnly_exact)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (w4ErrTailWide_fine_phaseCredit_tight w4StageP3Wide_zeroLive_fine_phaseCredit_tight
   w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (FreshBobPrev1Dom fineOptLarge fineOptLarge_mono optLargeCost_fine_eq
   serializePrev1MaxReq_freshBob_le serializePrev1Peak_fine_freshBob_le
   serializePrev1TightCum_fine_freshBob_le w4BoxedStoreStep_fine_le_28 w4BoxedStoreStep_fine_le_44
   w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyTryDecACEnv
   W4TrialDecEnv W4TryDecryptCall W4TryDecryptFailLinkedEnv W4TryDecryptPathACEnv
   spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec w4RealFailTdCum w4RealTdACCum)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4TryDecryptPathACDomOf
   w4FailTdPeakOf w4TdACLiveOf w4TdACPeakOf w4TdMaxReqOf w4TrialMaxReqOf w4TrialPeakOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events
   dropVecChainEvents dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal
   pinFreeEvents senderFreeEvents sgnCapFreeEvents ssFirst3FreeEvents
   ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak
   recordDeserializeCancelEnv_fine_phaseCreditSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv KpkPassEnv OptKpkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight dirGetEnv_path_readFile_fine_phaseCredit_tight
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv OptPkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv OptPkRemoveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (CliSpkGetPollEnv OptSpkDecodeEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

private theorem s3a5_pushBytesEvents_zero_cases {m : Nat} (hm : m ≤ 10) :
    pushBytesEvents m 0 0 = [] ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1 := by
  match m with
  | 0 => exact Or.inl (by decide)
  | 1 => exact Or.inr (Or.inl (by decide))
  | 2 => exact Or.inr (Or.inl (by decide))
  | 3 => exact Or.inr (Or.inl (by decide))
  | 4 => exact Or.inr (Or.inl (by decide))
  | 5 => exact Or.inr (Or.inl (by decide))
  | 6 => exact Or.inr (Or.inl (by decide))
  | 7 => exact Or.inr (Or.inl (by decide))
  | 8 => exact Or.inr (Or.inl (by decide))
  | 9 => exact Or.inr (Or.inr (by decide))
  | 10 => exact Or.inr (Or.inr (by decide))
  | _ + 11 => omega

private theorem s3a5_decimal_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (DecimalEnv id) 19578 0 0 16 := by
  have hlen : (decimalText id.toNat).length ≤ 10 :=
    decimalText_length_le 10 id.toNat (by decide) (Nat.lt_trans id.isLt (by decide))
  have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 9789 0 0 8 :=
    s3_rustAlloc_small_credit (req := 8) (al := 1) (by decide) (by decide)
  have hr16 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 8 16 1) 9789 0 0 16 :=
    (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 8) (new := 16) (al := 1)
      (by decide) (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (fineSmallReallocCost_le_9789_of_le_256 (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)
  have hcat : PhaseCreditSpec fineCostModel
      (· = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1) 19578 0 0 16 :=
    ((ha8.concat hr16).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hall : PhaseCreditSpec fineCostModel _ 19578 0 0 16 :=
    ((PhaseCreditSpec.nil fineCostModel).or (ha8.or hcat)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact hall.of_imp fun evs h => by
    unfold DecimalEnv decimalEvents at h
    rw [h]
    exact s3a5_pushBytesEvents_zero_cases hlen

private theorem s3a5_dhSmall_of_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  rw [fineCostModel_smallMaxReq_eq]
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem s3a5_w2Seeds738Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤ w4RealFailTdCum := by
  unfold w4RealFailTdCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem s3a5_w2GenSeeds12Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptGenSeeds738Cum 12 dhCap needGrow 12 3897904 ≤ w4RealTdACCum := by
  unfold w4RealTdACCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem s3a5_w2MaxReqOf_le_5 {dhCap maxCt : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 maxCt ≤ w4TdMaxReqOf maxCt := by
  unfold w4TdMaxReqOf w2TryDecryptMaxReq
  have h104 : max 416 (104 * (2 * dhCap)) ≤ max 416 (104 * (2 * 5)) := by
    match dhCap, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans h104 (Nat.le_max_left _ _),
          Nat.le_max_right _ _⟩)
       (Nat.le_max_right _ _)⟩

private theorem s3a5_deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem s3a5_pinFreeEvents_freeOnlyAlign16 (pin : VecPin) :
    FreeOnlyAlign16Evs (pinFreeEvents pin) := by
  unfold pinFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) pin.cap.toNat

private theorem s3a5_sgnCapFreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (sgnCapFreeEvents cap) := by
  unfold sgnCapFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) cap.toNat

private theorem s3a5_vec104FreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (vec104FreeEvents cap) := by
  unfold vec104FreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) (cap.toNat * 104)

private theorem s3a5_mkFreeEvents_freeOnlyAlign16 (mk : MessageKeyGhost) :
    FreeOnlyAlign16Evs (mkFreeEvents mk) := by
  unfold mkFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (s3a5_pinFreeEvents_freeOnlyAlign16 mk.cipher)
        (s3a5_pinFreeEvents_freeOnlyAlign16 mk.mac))
      (s3a5_pinFreeEvents_freeOnlyAlign16 mk.iv))
    (s3a5_pinFreeEvents_freeOnlyAlign16 mk.seed)

private theorem s3a5_mkListFreeEvents_freeOnlyAlign16
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (mks.flatMap fun gk => mkFreeEvents gk.1) := by
  induction mks with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gk tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact s3a5_mkFreeEvents_freeOnlyAlign16 gk.1 ev h1
    · exact ih ev h2

private theorem s3a5_dropVecMessageKeyEvents_freeOnlyAlign16 (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (dropVecMessageKeyEvents cap mks) := by
  intro ev hev; dsimp only [dropVecMessageKeyEvents] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact s3a5_mkListFreeEvents_freeOnlyAlign16 mks ev h1
  · exact s3a5_vec104FreeEvents_freeOnlyAlign16 cap ev h2

private theorem s3a5_chainPairFreeEvents_freeOnlyAlign16 (gc : ChainGhost × ReceiverChain) :
    FreeOnlyAlign16Evs (chainPairFreeEvents gc) := by
  unfold chainPairFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨gc.1.srk.cap, gc.1.srk.ptr⟩)
        (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨gc.1.priv.cap, gc.1.priv.ptr⟩))
      (s3a5_sgnCapFreeEvents_freeOnlyAlign16 (optCkCapVal gc.1.ck gc.2.chainKey)))
    (s3a5_dropVecMessageKeyEvents_freeOnlyAlign16 gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))

private theorem s3a5_chainListFreeEvents_freeOnlyAlign16
    (cs : List (ChainGhost × ReceiverChain)) :
    FreeOnlyAlign16Evs (cs.flatMap chainPairFreeEvents) := by
  induction cs with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gc tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact s3a5_chainPairFreeEvents_freeOnlyAlign16 gc ev h1
    · exact ih ev h2

private theorem s3a5_dropSessionStructureLocal1Events_freeOnlyAlign16
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FreeOnlyAlign16Evs (dropSessionStructureLocal1Events G st) := by
  unfold dropSessionStructureLocal1Events ssFirst3FreeEvents ssTail3FreeEvents dropVecChainEvents
  have h1 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨G.localIk.cap, G.localIk.ptr⟩)
      (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨G.remoteIk.cap, G.remoteIk.ptr⟩))
    (s3a5_pinFreeEvents_freeOnlyAlign16 G.root)
  have h2 : FreeOnlyAlign16Evs (senderFreeEvents G.sender) := by
    cases G.sender with
    | none => exact FreeOnlyAlign16Evs.nil
    | some sg =>
      unfold senderFreeEvents
      exact FreeOnlyAlign16Evs.append
        (FreeOnlyAlign16Evs.append
          (FreeOnlyAlign16Evs.append
            (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨sg.srk.cap, sg.srk.ptr⟩)
            (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨sg.priv.cap, sg.priv.ptr⟩))
          (s3a5_sgnCapFreeEvents_freeOnlyAlign16 sg.ck.cap))
        (s3a5_dropVecMessageKeyEvents_freeOnlyAlign16 sg.mkCap [])
  have h3 : FreeOnlyAlign16Evs
      (((G.chains.zip st.receiverChains).flatMap chainPairFreeEvents) ++
        vec104FreeEvents G.chainsCap) := by
    intro ev hev
    rcases List.mem_append.mp hev with h3a | h3b
    · exact s3a5_chainListFreeEvents_freeOnlyAlign16 (G.chains.zip st.receiverChains) ev h3a
    · exact s3a5_vec104FreeEvents_freeOnlyAlign16 G.chainsCap ev h3b
  have h4 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (s3a5_sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.pending))
      (s3a5_sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.kyber)))
    (s3a5_pinFreeEvents_freeOnlyAlign16 ⟨G.alice.cap, G.alice.ptr⟩)
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append (FreeOnlyAlign16Evs.append h1 h2) h3) h4)
    (s3a5_pinFreeEvents_freeOnlyAlign16 G.pq)

private theorem s3a5_deallocCreditSpec_dropSessionStructureLocal1
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hok : SessionDropCapsOk G st) :
    DeallocCreditSpec fineCostModel
      (· = dropSessionStructureLocal1Events G st)
      (ssStateLargeLive fineCostModel G st) where
  req_align := by
    rintro _ rfl ev hev
    exact (PhaseCreditSpec.freeOnly_align16 fineCostModel).req_align _
      (s3a5_dropSessionStructureLocal1Events_freeOnlyAlign16 G st) ev hev
  credit_sub := by
    rintro st0 _ rfl
    exact stepEvents_dropSessionStructureLocal1_bounds fineCostModel hok st0

private theorem s3a5_tryDecryptPathAC_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptPathACDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathACEnv F K td)
      w4RealTdACCum (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12)
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    (s3a5_dhSmall_of_le_5 hDom.base.dh_le) hDom.base.caps_len hDom.base.chain_le
    (spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec F K td.stBytes td.w
      hDom.base.top_tight hDom.zero_skip)
    hDom.base.ct_le
  exact hBase.mono
    (s3a5_w2GenSeeds12Cum_le_5 td.needGrow hDom.base.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (s3a5_w2MaxReqOf_le_5 hDom.base.dh_le)

private theorem s3a5_failedTdCancel_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (s3a5_dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (s3a5_w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _) (s3a5_w2MaxReqOf_le_5 hDom.td_dom.dh_le)
  have hDrop := s3a5_deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem s3a5_trialDec_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialDecEnv F x)
      deserCancelFineCum (sessDeserLargeLive fineCostModel x.r_dec)
      deserCancelFinePeak deserCancelFineMaxReq := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hmaxR : max 212992 (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq :=
    Nat.max_le.mpr ⟨by decide, hDom.enc_le⟩
  have hSym := sessDeserializeCancelEnv_phaseCreditSpec fineCostModel h33 hmaxR
  have hCl := sessDeserializeCancelEnv_fine_phaseCreditSpec hDom.enc_le
  exact
    { req_align := hCl.req_align
      credit_le := fun st0 {_} hE => by
        obtain ⟨hc, _, hp⟩ := hCl.credit_le st0 hE
        obtain ⟨_, hl, _⟩ := hSym.credit_le st0 hE
        exact ⟨hc, hl, hp⟩ }

private theorem s3a5_trialRunWide_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialRunWideEnv F K x)
      (8277456 + w4RealFailTdCum + 8674) 0 (w4TrialPeakOf maxCt) (w4TrialMaxReqOf maxCt) := by
  have hCloneFail := w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit
    (curPqCap := 286196)
    (Or.inr ⟨x.ses_tr, rfl, hDom.tr_gv, hDom.tr_dom⟩)
    (s3a5_failedTdCancel_credit hDom.tr_fail)
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCloneFail).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem s3a5_w4CloneACDom_credit :
    PhaseCreditSpec fineCostModel W4CloneACDomEnv 36295 0 0 208000 where
  req_align evs := fun ⟨_, _, hbob, hE⟩ =>
    (sessionClone_freshBob16K_fine_phaseCredit hbob (Nat.le_refl 16384)).req_align evs hE
  credit_le st0 := fun ⟨_, _, hbob, hE⟩ =>
    (sessionClone_freshBob16K_fine_phaseCredit hbob (Nat.le_refl 16384)).credit_le st0 hE

private theorem s3a5_sessLoadStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinarySessLoadStepEnv cliIo.rd F0 peer)
      17517856 5316629 8478747 2097152 := by
  unfold W4BinarySessLoadStepEnv cliSessionKitLoadPollEnv
  have hpeerVal : peer.val.name.length ≤ 40 := hpeer
  have haddrLen : (addressText peer.val).length ≤ 64 := addressText_peer_length_le_64 hpeer
  have hdcSess := s3_dirDomainCaps_64 dirDomainCaps_opened_sess (by decide)
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeerVal
  have hGetSess : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.sessions (addressText peer.val))
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.sessions (addressText peer.val) hdcSess haddrLen
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptDeser : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val)))
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        have hlen : (b0 :: bsRest).length ≤ 2097152 := by
          change cliIo.rd F0 _ = .ok (b0 :: bsRest) at hget
          exact cliRd_ok_le_fileCap hget
        exact s3_phaseCreditSpec_exists fun r henc => by
          unfold ofBytesEnv
          have hlen' : (encodeRecord r).length ≤ 2097152 := by rw [henc]; exact hlen
          exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen').of_imp fun _ h => h.2
  have hPoll := hAddr.seq
    (hGetSess.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptDeser))
  exact (w4BoxedStoreStep_fine_le_28 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_idTrustStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdTrustStepEnv cliIo.rd F0 peer remoteIdKey)
      596479 2105347 3162118 2097152 := by
  unfold W4BinaryIdTrustStepEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPoll := seq_freeOnly_phaseCredit fineCostModel_freeNonInc hGet
  exact (w4BoxedStoreStep_fine_le_44 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_idSaveStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdSaveStepEnv cliIo.rd F0 peer remoteIdKey)
      625846 2105347 3162118 2097152 := by
  unfold W4BinaryIdSaveStepEnv cliIdentityKitSavePollEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hTail : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity peer.val remoteIdKey
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name))
      29367 0 0 192 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 9789 0 0 33 := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
      have hput := s3_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        (Nat.le_trans hpeer (by decide)) remoteIdKey.serialize
      have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (hf.seq (hpks.seq hput)).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hGet.seq hTail)).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_recordSerializeSeqFree_credit
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (RecordSerializeSeqFreeEnv g r)
      8420940 3480713 3480713 2097152 := by
  have hp : 1080975 + optLargeCost fineCostModel 286196 + optLargeCost fineCostModel 2097152 ≤
      3480713 := by
    rw [optLargeCost_fine_eq 286196, optLargeCost_fine_eq 2097152]; decide
  have hr : max (max 208000 286196) 2097152 ≤ 2097152 := by decide
  exact (PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps g r).mono
    (recordSerializeTightCum_fine_le_of_dom hValid)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializeMaxReq_le_of_dom hValid hEnc) hr)

private theorem s3a5_sessStoreStep_credit (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_rec).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinarySessStoreStepEnv peer g_rec r_rec)
      8442732 3480713 3480713 2097152 := by
  unfold W4BinarySessStoreStepEnv cliSessionKitStorePollEnv
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeer
  have hSer := s3a5_recordSerializeSeqFree_credit hValid hEnc
  have hPut := s2b_dirPutTail_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText peer.val)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hAddr.seq (hSer.seq hPut))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_sessStorePrev1Step_credit (peer : AddrGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (hpeer : peer.name.bytes.length ≤ 40)
    (hbob : FreshBobPrev1Dom 16384 2097152 2457152 G sess enc) :
    PhaseCreditSpec fineCostModel (W4BinarySessStorePrev1StepEnv peer G sess enc)
      1206704
      (fineOptLarge 16384 + fineOptLarge 2097152 + fineOptLarge 2457152)
      (fineOptLarge 16384 + fineOptLarge 2097152 + fineOptLarge 2457152)
      2457152 := by
  unfold W4BinarySessStorePrev1StepEnv
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeer
  have hr : max (max 208000 16384) (max (max 24 2097152) 2457152) ≤ 2457152 := by decide
  have hSer := (PhaseCreditSpec.serializePrev1_seqFree_tight fineCostModel_modelHyps G sess enc).mono
    (serializePrev1TightCum_fine_freshBob_le hbob)
    (serializePrev1Peak_fine_freshBob_le hbob)
    (serializePrev1Peak_fine_freshBob_le hbob)
    (Nat.le_trans (serializePrev1MaxReq_freshBob_le hbob) hr)
  have hPut := s3_dirPut_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText peer.val) (encodeRecordPrev1Mem G sess enc)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hAddr.seq (hSer.seq hPut))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_archiveDirect_credit {maxEncLen : Nat} (hEnc : maxEncLen ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryArchiveDirectEnv maxEncLen)
      4213766 2105347 2105347 2097152 := by
  unfold W4BinaryArchiveDirectEnv
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hAlloc : PhaseCreditSpec fineCostModel
      (fun e => ∃ n ≤ maxEncLen, e = rustAllocEvents n 1)
      4203843 2105347 2105347 2097152 :=
    s3_phaseCreditSpec_exists fun n hn => by
      have hnCap : n ≤ 2097152 := Nat.le_trans hn hEnc
      have hc : 2 * n + 9539 ≤ 4203843 :=
        Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnCap) 9539) (by decide)
      have hl : optLargeCost fineCostModel n ≤ 2105347 := by
        rw [optLargeCost_fine_eq n]
        exact Nat.le_trans (fineOptLarge_mono hnCap) (by decide)
      exact (PhaseCreditSpec.rustAlloc_optLarge fineCostModel_modelHyps
        (req := n) (al := 1) (by decide)).mono hc hl hl hnCap
  have hVec : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  exact (hf.seq (hAlloc.seq (hVec.seq hf))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_promoteArchive_credit
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_arch).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryPromoteArchiveEnv g_arch r_arch)
      8430863 3480713 3480713 2097152 := by
  unfold W4BinaryPromoteArchiveEnv
  have hPush : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  have hProm := phaseCredit_promoteStateArchive fineCostModel_modelHyps
    (s3a5_recordSerializeSeqFree_credit hValid hEnc) hPush
  have hDir := s3a5_archiveDirect_credit hEnc
  exact (hProm.or hDir).mono (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_kemKpFromPubPriv_credit :
    PhaseCreditSpec fineCostModel (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs)
      19578 0 0 3168 := by
  have ha1 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 1568 1) 9789 0 0 1568 :=
    s3_rustAlloc_small_credit (req := 1568) (al := 1) (by decide) (by decide)
  have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 3168 1) 9789 0 0 3168 :=
    s3_rustAlloc_small_credit (req := 3168) (al := 1) (by decide) (by decide)
  have hkp : PhaseCreditSpec fineCostModel KemKeyPairFromPubPrivEnv 19578 0 0 3168 :=
    ((ha1.concat ha2).of_imp fun _ h => by
      unfold KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents at h
      exact ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hkp

private theorem s3a5_kpkPass_credit (F0 : FsFiles) (dir : DirGhost) (kpkId : BitVec 32)
    (hdc : DirDomainCaps 64 0 0 dir)
    (hcapRd : ∀ bs, cliIo.rd F0 (pathOf dir.path (keyName kpkId)) = .ok bs → bs.length ≤ 4900)
    (hcapGet : ∀ bs, dir.get cliIo.rd F0 (keyName kpkId) = .ok bs → bs.length ≤ 4900)
    (hSpkDec : ∀ {bs : List (BitVec 8)} {L : Nat}, bs.length ≤ L → L ≤ 4900 →
      PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808) :
    PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 dir kpkId)
      (19578 + ((21185 + fineReadFileCum (max 0 4900)) + (380 * 4900 + 750000)))
      (0 + (fineReadFileLive (max 0 4900) + 0))
      (max 0 (0 + max (fineReadFilePeak (max 0 4900)) (fineReadFileLive (max 0 4900) + 0)))
      (max 16 (max (max 256 (fineReadFileMaxReq (max 0 4900))) 9808)) := by
  unfold KpkPassEnv
  have hDec := s3a5_decimal_credit kpkId
  have hGet := dirGetEnv_path_readFile_fine_phaseCredit_tight
    cliIo.rd F0 dir (keyName kpkId) hdc
    (Nat.le_trans (keyName_length_le kpkId) (by decide)) hcapRd
  have hOpt : PhaseCreditSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv (dir.get cliIo.rd F0 (keyName kpkId)))
      (380 * 4900 + 750000) 0 0 9808 := by
    unfold OptKpkDecodeEnv
    cases hgr : dir.get cliIo.rd F0 (keyName kpkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact hSpkDec (hcapGet (b0 :: bsRest) hgr) (Nat.le_refl 4900)
  exact hDec.seq (hGet.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOpt))

private theorem s3a5_subst_rd_files
    {P : ReadRule → FsFiles → List AllocEvent → Prop} {rd1 rd2 : ReadRule} {f1 f2 : FsFiles}
    {c l p r : Nat}
    (hrd : rd1 = rd2) (hf : f1 = f2)
    (h : PhaseCreditSpec fineCostModel (P rd2 f2) c l p r) :
    PhaseCreditSpec fineCostModel (P rd1 f1) c l p r := by
  subst hrd; subst hf; exact h

private theorem s3a5_ite_or_nil (b : Bool) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (if b then E else (· = [])) c l p r := by
  cases b
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le c) (Nat.zero_le l) (Nat.zero_le p) (Nat.zero_le r)
  · exact h

private theorem s3a5_kpkPass_empty_credit (F0 : FsFiles) (kpkId : BitVec 32)
    (hdc : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime)
    (hempty : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) = .ok []) :
    PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.oneTime kpkId)
      (19578 + ((21185 + max 738 (fineReadFileCum 0)) + 0))
      (0 + (fineReadFileLive 0 + 0))
      (max 0 (0 + max (fineReadFilePeak 0) (fineReadFileLive 0 + 0)))
      (max 16 (max (max 256 (fineReadFileMaxReq 0)) 0)) := by
  unfold KpkPassEnv
  have hDec := s3a5_decimal_credit kpkId
  have hcap0 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .ok bs →
        bs.length ≤ 0 := by
    intro bs h
    change StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) = .ok bs at h
    rw [hempty] at h
    injection h with h
    subst h
    decide
  have hGet := dirGetEnv_path_readFile_fine_phaseCredit_tight
    cliIo.rd F0 StoresGhost.opened.kyber.oneTime (keyName kpkId) hdc
    (Nat.le_trans (keyName_length_le kpkId) (by decide)) hcap0
  have hOpt : PhaseCreditSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId)))
      0 0 0 0 := by
    rw [hempty]
    exact PhaseCreditSpec.nil fineCostModel
  exact hDec.seq (hGet.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOpt))

private theorem s3a5_kpkPoll_credit (F0 : FsFiles) (kpkId : BitVec 32)
    (hdcKot : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime)
    {c l p r : Nat}
    (hOt : PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.oneTime kpkId) c l p r)
    (hLr : PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.lastResort kpkId) c l p r) :
    let c0 := 19578 + ((21185 + max 738 (fineReadFileCum 0)) + 0)
    let l0 := 0 + (fineReadFileLive 0 + 0)
    let p0 := max 0 (0 + max (fineReadFilePeak 0) (fineReadFileLive 0 + 0))
    let r0 := max 16 (max (max 256 (fineReadFileMaxReq 0)) 0)
    PhaseCreditSpec fineCostModel
      (CliKpkGetPollEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0
        ⟨0#64, 0#64, 0#64, kpkId, StoresGhost.opened.kyber⟩)
      (c0 + c) (l0 + l) (max p0 (l0 + p)) (max r0 r) := by
  dsimp only
  unfold CliKpkGetPollEnv
  dsimp only
  cases hgr : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) with
  | error u =>
    simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
    exact hOt.mono
      (Nat.le_add_left _ _) (Nat.le_add_left _ _)
      (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  | ok bs =>
    cases bs with
    | nil =>
      simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
      exact (s3a5_kpkPass_empty_credit F0 kpkId hdcKot hgr).seq hLr
    | cons b0 bsRest =>
      simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
      cases CryptoVerification.RecordCodecs.KyberPreKeyRecord.deserialize (b0 :: bsRest) with
      | error _ =>
        dsimp only
        exact hOt.mono
          (Nat.le_add_left _ _) (Nat.le_add_left _ _)
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _)
      | ok _ =>
        dsimp only
        exact hOt.mono
          (Nat.le_add_left _ _) (Nat.le_add_left _ _)
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _)

private theorem s3a5_pathAC_credit_core (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (w4 : W4BinaryRecvPrekeyParams)
    (hw4 : W4BinaryRecvPrekeyDom (.recv peerAddr) i w4)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105)
    (hspk : ∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230)
    (hopk : ∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (hkpkLr : ∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (hSpkDec : ∀ {bs : List (BitVec 8)} {L : Nat}, bs.length ≤ L → L ≤ 4900 →
      PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808)
    (hPkDec : ∀ {bs : List (BitVec 8)}, bs.length ≤ 125 →
      PhaseCreditSpec fineCostModel (CliPkDecodeEnv bs) 2476617 0 0 256)
    (hIkpDec : ∀ {gr : Except Unit (List (BitVec 8))},
      (∀ bs, gr = .ok bs → bs.length ≤ 105) →
      PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 2085057 0 0 256)
    (hMark : ∀ (kpkId spkId : BitVec 32) (baseKey : PublicKey),
      PhaseCreditSpec fineCostModel
        (W4BinaryKpkMarkStepEnvFixed cliIo.rd (runFiles i) kpkId spkId baseKey)
        1300000 4250000 6400000 4194368) :
    PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryRecvPrekeyPathAWideEnvFixed w4 e ∨
        W4BinaryRecvPrekeyPathCWideEnvFixed w4 e)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
  obtain ⟨_, hpeer, hfiles, hrd, hDom⟩ := hw4 peerAddr rfl
  obtain ⟨hdcOwn0, _hdcPeers0, hdcSpk0, hdcKot0, hdcKlr0, hdcOpk0, _hdcSess0⟩ :=
    opened_all_dirDomainCaps
  have hdcOwn := s3_dirDomainCaps_64 hdcOwn0 (by decide)
  have hdcSpk := s3_dirDomainCaps_64 hdcSpk0 (by decide)
  have hdcKot := s3_dirDomainCaps_64 hdcKot0 (by decide)
  have hdcKlr := s3_dirDomainCaps_64 hdcKlr0 (by decide)
  have hdcOpk := s3_dirDomainCaps_64 hdcOpk0 (by decide)
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoad : PhaseCreditSpec fineCostModel
      (W4BinarySessLoadStepEnv w4.base.rd w4.base.files w4.base.peer)
      17517856 5316629 8478747 2097152 := by
    rw [hrd, hfiles]; exact s3a5_sessLoadStep_credit (runFiles i) w4.base.peer hpeer
  have hTrust : PhaseCreditSpec fineCostModel
      (W4BinaryIdTrustStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      596479 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idTrustStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hP1Ok : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1OkEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18114335 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1OkEnv
    exact (hLoad.seq (phaseCredit_optStageEnv fineCostModel_modelHyps hTrust)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hBnd33 := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 33
        (by rw [fineCostModel_smallMaxReq_eq]; decide)))
  have hOptSpk : PhaseCreditSpec fineCostModel
      (OptSpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName w4.base.spkId)))
      (380 * 230 + 750000) 0 0 9808 := by
    unfold OptSpkDecodeEnv
    cases hgr : StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName w4.base.spkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact hSpkDec (hspk w4.base.spkId (b0 :: bsRest) hgr) (by decide)
  have hSpkCli := w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide)
    ((s3a5_decimal_credit w4.base.spkId).seq
      ((dirGetEnv_path_readFile_fine_phaseCredit_tight
          cliIo.rd (runFiles i) StoresGhost.opened.signed (keyName w4.base.spkId) hdcSpk
          (Nat.le_trans (keyName_length_le w4.base.spkId) (by decide))
          (fun bs h => hspk w4.base.spkId bs h)).seq
        (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptSpk)))
  have hSpkStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_subst_rd_files (P := fun rd files => W4BinarySpkGetStepEnv rd files w4.base.spkId)
      hrd hfiles hSpkCli)
  have hOtKpk := s3a5_kpkPass_credit (runFiles i) StoresGhost.opened.kyber.oneTime w4.base.kpkId
    hdcKot (fun bs h => hkpkOt w4.base.kpkId bs h) (fun bs h => hkpkOt w4.base.kpkId bs h)
    hSpkDec
  have hLrKpk := s3a5_kpkPass_credit (runFiles i) StoresGhost.opened.kyber.lastResort w4.base.kpkId
    hdcKlr (fun bs h => hkpkLr w4.base.kpkId bs h) (fun bs h => hkpkLr w4.base.kpkId bs h)
    hSpkDec
  have hKpkCli := w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide)
    (s3a5_kpkPoll_credit (runFiles i) w4.base.kpkId hdcKot hOtKpk hLrKpk)
  have hKpkStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_subst_rd_files (P := fun rd files => W4BinaryKpkGetStepEnv rd files w4.base.kpkId)
      hrd hfiles hKpkCli)
  have hKemStep := phaseCredit_optStageEnv fineCostModel_modelHyps s3a5_kemKpFromPubPriv_credit
  have hBnd21 := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 21
        (by rw [fineCostModel_smallMaxReq_eq]; decide)))
  have hOptPk : PhaseCreditSpec fineCostModel
      (OptPkDecodeEnv CliPkDecodeEnv
        (StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId)))
      2476617 0 0 256 := by
    unfold OptPkDecodeEnv
    cases hgr : StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact hPkDec (hopk w4.base.opkId (b0 :: bsRest) hgr)
  have hPkGetCli := w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide)
    ((s3a5_decimal_credit w4.base.opkId).seq
      ((dirGetEnv_path_readFile_fine_phaseCredit_tight
          cliIo.rd (runFiles i) StoresGhost.opened.oneTime (keyName w4.base.opkId) hdcOpk
          (Nat.le_trans (keyName_length_le w4.base.opkId) (by decide))
          (fun bs h => hopk w4.base.opkId bs h)).seq
        (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptPk)))
  have hPkGetStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_ite_or_nil w4.base.hasOpk
      (s3a5_subst_rd_files (P := fun rd files => W4BinaryPkGetStepEnv rd files w4.base.opkId)
        hrd hfiles hPkGetCli))
  have hkpName : (utf8 "identity-key-pair").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hSelfKpCli : PhaseCreditSpec fineCostModel
      (W4BinarySelfKpStepEnv cliIo.rd (runFiles i)) _ _ _ _ :=
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux.boxAllocEnv_fine_le_28
        (boxSz := 16) (by decide))).seq
      ((dirGetEnv_path_readFile_fine_phaseCredit_tight
          cliIo.rd (runFiles i) StoresGhost.opened.identity.own (utf8 "identity-key-pair") hdcOwn
          hkpName (fun bs h => hikp bs h)).seq
        (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps (hIkpDec hikp)))
  have hSelfKpStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_subst_rd_files (P := fun rd files => W4BinarySelfKpStepEnv rd files)
      hrd hfiles hSelfKpCli)
  have hSmallIkm : max 4096 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; exact hDom.outer_dom.ikm_small
  have hSm68 : 68 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hAccWide : PhaseCreditSpec fineCostModel
      (W4BinaryAcceptWideEnv w4.base.x_res w4.base.hasOpk) _ _ _ _ :=
    (phaseCredit_w4PqxdhAccept_small fineCostModel_modelHyps
        (hasOpk := w4.base.hasOpk) hDom.outer_dom.res_old hDom.outer_dom.res_new hSmallIkm).or
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
        (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 6 192
          (by rw [fineCostModel_smallMaxReq_eq]; decide)))
  have hInitBob0 : PhaseCreditSpec fineCostModel
      (W4BinaryInitBobWideEnv w4.base.F w4.base.x_res w4.base.hasOpk w4.base.x_spqr) _ _ _ _ :=
    hAccWide.seq
      (phaseCredit_optStageEnv fineCostModel_modelHyps
        ((w4SpqrInit32_fine_phaseCredit w4.base.F w4.base.x_spqr hDom.outer_dom.spqr_key).seq
          (phaseCredit_optStageEnv fineCostModel_modelHyps
            (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.phaseCredit_w4BobSessionBuild9_small
              fineCostModel_modelHyps hSm68))))
  have hInitBobStep := phaseCredit_optStageEnv fineCostModel_modelHyps hInitBob0
  have hregName : (utf8 "registration-id").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hRegMal : PhaseCreditSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "registration-id")))
      9789 0 0 14 := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "registration-id") with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      · exact s3_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide)
  have hSelfRegCli := w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide)
    ((dirGetEnv_path_readFile_fine_phaseCredit_tight
        cliIo.rd (runFiles i) StoresGhost.opened.identity.own (utf8 "registration-id") hdcOwn
        hregName (fun _ h => cliRd_ok_le_fileCap h)).seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hRegMal))
  have hSelfRegStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_subst_rd_files (P := fun rd files => W4BinarySelfRegIdStepEnv rd files)
      hrd hfiles hSelfRegCli)
  have hP2ATail := hBnd33.seq (hSpkStep.seq (hKpkStep.seq (hKemStep.seq
    (hBnd21.seq (hPkGetStep.seq (hSelfKpStep.seq (hInitBobStep.seq
      (hSelfRegStep.seq w4ErrTailWide_fine_phaseCredit_tight))))))))
  have hOptP2A := phaseCredit_optStageEnv fineCostModel_modelHyps hP2ATail
  let P := mkW4RecvPrekeyWideSlotParams w4.base
  have hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      w4RealFailTdCum 0 (w4FailTdPeakOf msgCapBytes) (w4TdMaxReqOf msgCapBytes) := by
    change PhaseCreditSpec fineCostModel
      (if w4.base.hasCurSession then W4FailedTdCancelEnv w4.base.F w4.base.K w4.base.fc_cur
       else fun _ => False)
      w4RealFailTdCum 0 (w4FailTdPeakOf msgCapBytes) (w4TdMaxReqOf msgCapBytes)
    cases hcs : w4.base.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact s3a5_failedTdCancel_credit (hDom.cur_fail_dom hcs)
  have hCurStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit hDom.outer_dom.cur_dom hCurTrial)
  have hLoopStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCredit_archivedTrialLoop_le4
      (DecEnv := P.DecEnv) (TrialEnv := P.TrialEnv) (DropEnv := P.DropEnv) (xs := P.archivedTrials)
      (l_dec := fun x => sessDeserLargeLive fineCostModel x.r_dec)
      hDom.outer_dom.trials_len4
      (fun x hx => (hDom.trials_dom x hx).live_le_peak)
      (fun x hx => s3a5_trialDec_credit (hDom.trials_dom x hx))
      (fun x hx => s3a5_trialRunWide_credit (hDom.trials_dom x hx))
      (fun x hx =>
        s3a5_deallocCreditSpec_mono_le
          (s3a5_deallocCreditSpec_dropSessionStructureLocal1 (hDom.trials_dom x hx).drop_caps)
          (hDom.trials_dom x hx).live_le_drop))
  have hPromStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_promoteArchive_credit w4.base.g_arch w4.base.r_arch
      hDom.outer_dom.arch_valid hDom.outer_dom.arch_enc)
  have hP2CTail := hCurStep.seq (hLoopStep.seq (hBnd33.seq (hSpkStep.seq (hKpkStep.seq
    (hKemStep.seq (hBnd21.seq (hPkGetStep.seq (hSelfKpStep.seq (hInitBobStep.seq
      (hSelfRegStep.seq (hPromStep.seq w4ErrTailWide_fine_phaseCredit_tight)))))))))))
  have hOptP2C := phaseCredit_optStageEnv fineCostModel_modelHyps hP2CTail
  have hTdAC : PhaseCreditSpec fineCostModel (W4RecvPrekeyTryDecACEnv w4.base)
      w4RealTdACCum (w4TdACLiveOf msgCapBytes) (w4TdACPeakOf msgCapBytes)
      (w4TdMaxReqOf msgCapBytes) := by
    unfold W4RecvPrekeyTryDecACEnv
    cases hpac : w4.base.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact s3a5_tryDecryptPathAC_credit (hDom.tdAC_dom hpac)
  have hOptP3AC := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP3Wide_zeroLive_fine_phaseCredit_tight s3a5_w4CloneACDom_credit hTdAC)
  have hSaveStep0 : PhaseCreditSpec fineCostModel
      (W4BinaryIdSaveStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      625846 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idSaveStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hSaveStep := phaseCredit_optStageEnv fineCostModel_modelHyps hSaveStep0
  have hMarkStep0 : PhaseCreditSpec fineCostModel
      (W4BinaryKpkMarkStepEnvFixed w4.base.rd w4.base.files w4.base.kpkId w4.base.spkId w4.baseKey)
      1300000 4250000 6400000 4194368 := by
    rw [hrd, hfiles]
    exact hMark w4.base.kpkId w4.base.spkId w4.baseKey
  have hMarkStep := phaseCredit_optStageEnv fineCostModel_modelHyps hMarkStep0
  have hTailRem : PhaseCreditSpec fineCostModel
      (OptPkRemoveTailEnv DecimalEnv DirPutEnv
        ⟨0#64, 0#64, 0#64, w4.base.opkId, StoresGhost.opened.oneTime⟩
        (StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId)))
      (0 + (19578 + 9789)) 0 0 192 := by
    unfold OptPkRemoveTailEnv
    cases StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId) with
    | error _ =>
      exact hf.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact hf.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons _ _ =>
        have hDec2 := s3a5_decimal_credit w4.base.opkId
        have hPut := s3_dirPut_opened_credit (dir := StoresGhost.opened.oneTime) rfl
          (keyName w4.base.opkId) []
        exact (hf.seq (hDec2.seq hPut)).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hPkRemCli := w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide)
    ((s3a5_decimal_credit w4.base.opkId).seq
      ((dirGetEnv_path_readFile_fine_phaseCredit_tight
          cliIo.rd (runFiles i) StoresGhost.opened.oneTime (keyName w4.base.opkId) hdcOpk
          (Nat.le_trans (keyName_length_le w4.base.opkId) (by decide))
          (fun bs h => hopk w4.base.opkId bs h)).seq hTailRem))
  have hPkRemStep := phaseCredit_optStageEnv fineCostModel_modelHyps
    (s3a5_ite_or_nil w4.base.hasOpk
      (s3a5_subst_rd_files (P := fun rd files => W4BinaryPkRemoveStepEnv rd files w4.base.opkId)
        hrd hfiles hPkRemCli))
  have hStore0 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_sessStoreStep_credit w4.base.peer w4.base.g_out0 w4.base.r_out0 hpeer
        hDom.outer_dom.out0_valid hDom.outer_dom.out0_enc))
  have hStore1 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_sessStorePrev1Step_credit w4.base.peer w4.base.G_out1 w4.base.sess_out1
        w4.base.enc_prev1 hpeer hDom.outer_dom.out1_freshBob))
  have hOptP4A := phaseCredit_optStageEnv fineCostModel_modelHyps
    (hSaveStep.seq (hMarkStep.seq (hPkRemStep.seq hStore0)))
  have hOptP4C := phaseCredit_optStageEnv fineCostModel_modelHyps
    (hSaveStep.seq (hMarkStep.seq (hPkRemStep.seq hStore1)))
  have hPathA : PhaseCreditSpec fineCostModel (W4BinaryRecvPrekeyPathAWideEnvFixed w4)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq :=
    (hP1Ok.seq (hOptP2A.seq (hOptP3AC.seq hOptP4A))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPathC : PhaseCreditSpec fineCostModel (W4BinaryRecvPrekeyPathCWideEnvFixed w4)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq :=
    (hP1Ok.seq (hOptP2C.seq (hOptP3AC.seq hOptP4C))).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (hPathA.or hPathC).mono (by decide) (by decide) (by decide) (by decide)

end S3a5Sub5Helpers

section S3a3Sub3Helpers

open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.SignalSession.Cli
  (KpkMarkPollGhost baseKeyEntry baseKeysName decimalText hasChunk)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq smallReallocCost_le_two_mul_add)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (baseKeysName_length_le dirDomainCaps_opened_kpkLr dirDomainCaps_opened_kpkOt keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (fineSmallReallocCost_le_9789_of_le_256 optLargeCost_of_gt optLargeCost_of_le)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv phaseCreditSpec_seq_freeOnly_exact w4BoxedStepCum w4BoxedStepMaxReq
   w4BoxedStoreStep_small_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetMissEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
  (freeOnlyEvs_optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
  (kpkAfterLrGetPreEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget
  (KpkBaseKeysReserveEnv KpkLastResortPreAfterGetEnv kpkBaseKeysReserveEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkAfterLrGetCapFreeBranchEnv KpkOneTimeConsTailEnv KpkOneTimePreAfterGetEnv
   KpkSeenAppendReserveMidEnv OptKpkMarkLastResortTailEnv OptKpkMarkOneTimeTailEnv
   kpkSeenAppendReserveEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushBytesEvents)

private theorem s3a3_seqEnv_assoc_left {A B C : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv A (SeqEnv B C) evs) : SeqEnv (SeqEnv A B) C evs := by
  rcases h with ha | ⟨e1, e23, rfl, ha, hbc⟩
  · exact Or.inl (Or.inl ha)
  · rcases hbc with hb | ⟨e2, e3, rfl, hb, hc⟩
    · exact Or.inl (Or.inr ⟨e1, e23, rfl, ha, hb⟩)
    · exact Or.inr ⟨e1 ++ e2, e3, (List.append_assoc e1 e2 e3).symm,
        Or.inr ⟨e1, e2, rfl, ha, hb⟩, hc⟩

private theorem s3a3_pushBytesEvents_zero_cases {m : Nat} (hm : m ≤ 10) :
    pushBytesEvents m 0 0 = [] ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1 := by
  match m with
  | 0 => exact Or.inl (by decide)
  | 1 => exact Or.inr (Or.inl (by decide))
  | 2 => exact Or.inr (Or.inl (by decide))
  | 3 => exact Or.inr (Or.inl (by decide))
  | 4 => exact Or.inr (Or.inl (by decide))
  | 5 => exact Or.inr (Or.inl (by decide))
  | 6 => exact Or.inr (Or.inl (by decide))
  | 7 => exact Or.inr (Or.inl (by decide))
  | 8 => exact Or.inr (Or.inl (by decide))
  | 9 => exact Or.inr (Or.inr (by decide))
  | 10 => exact Or.inr (Or.inr (by decide))
  | _ + 11 => omega

private theorem s3a3_decimal_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (DecimalEnv id) 19578 0 0 16 := by
  have hlen : (decimalText id.toNat).length ≤ 10 :=
    decimalText_length_le 10 id.toNat (by decide) (Nat.lt_trans id.isLt (by decide))
  have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 9789 0 0 8 :=
    s3_rustAlloc_small_credit (req := 8) (al := 1) (by decide) (by decide)
  have hr16 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 8 16 1) 9789 0 0 16 :=
    (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 8) (new := 16) (al := 1)
      (by decide) (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (fineSmallReallocCost_le_9789_of_le_256 (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)
  have hcat : PhaseCreditSpec fineCostModel
      (· = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1) 19578 0 0 16 :=
    ((ha8.concat hr16).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hall : PhaseCreditSpec fineCostModel _ 19578 0 0 16 :=
    ((PhaseCreditSpec.nil fineCostModel).or (ha8.or hcat)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact hall.of_imp fun evs h => by
    unfold DecimalEnv decimalEvents at h
    rw [h]
    exact s3a3_pushBytesEvents_zero_cases hlen

private theorem s3a3_baseKeysReserveAt_credit (id : BitVec 32) {spare : Nat} (hsp : spare ≤ 9) :
    PhaseCreditSpec fineCostModel (· = kpkBaseKeysReserveEventsAt id spare) 9789 0 0 38 := by
  have hk : (keyName id).length ≤ 10 := keyName_length_le id
  let old := (keyName id).length + spare
  let newCap := reserveCap old (keyName id).length 10
  have hold_le : old ≤ 19 := by dsimp only [old]; omega
  have hrc : 8 ≤ newCap ∧ newCap ≤ 38 := by dsimp only [newCap, old, reserveCap]; omega
  have htoNat : (BitVec.ofNat 64 old).toNat = old := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hold_le (by decide))]
  by_cases hz : old = 0
  · have hb0 : BitVec.ofNat 64 old = 0#64 := by rw [hz]
    have hd : kpkBaseKeysReserveEventsAt id spare = rustAllocEvents newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, keyName id, 10⟩ =
        rustAllocEvents newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hb0, ↓reduceIte]
      exact rfl
    exact ((s3_rustAlloc_small_credit (req := newCap) (al := 1)
      (by decide) (Nat.le_trans hrc.2 (by decide))).of_imp
      (fun _ heq => by rw [heq, hd])).mono
      (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
  · have hpos : 0 < old := Nat.pos_of_ne_zero hz
    have hne0 : BitVec.ofNat 64 old ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      exact hz ht
    have hd : kpkBaseKeysReserveEventsAt id spare = rustReallocEvents old newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, keyName id, 10⟩ =
        rustReallocEvents old newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hne0, ↓reduceIte]
      exact rfl
    exact ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
      (old := old) (new := newCap) (al := 1) (by decide)
      (Nat.le_trans (by decide : 1 ≤ 8) hrc.1) hpos
      (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hold_le (by decide))
      (Nat.lt_of_lt_of_le (by decide : 0 < 8) hrc.1)
      (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hrc.2 (by decide))).of_imp
      (fun _ heq => by rw [heq, hd])).mono
      (fineSmallReallocCost_le_9789_of_le_256 (Nat.le_trans hrc.2 (by decide)))
      (Nat.le_refl 0) (Nat.le_refl 0) hrc.2

private theorem s3a3_baseKeysReserve_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (KpkBaseKeysReserveEnv id) 9789 0 0 38 := by
  have hex : PhaseCreditSpec fineCostModel
      (fun evs => ∃ spare, spare ≤ 9 ∧ evs = kpkBaseKeysReserveEventsAt id spare)
      9789 0 0 38 :=
    s3_phaseCreditSpec_exists fun _ hsp => s3a3_baseKeysReserveAt_credit id hsp
  exact (((PhaseCreditSpec.nil fineCostModel).or hex).mono
    (by decide) (by decide) (by decide) (by decide)).of_imp fun evs h => by
    unfold KpkBaseKeysReserveEnv at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by decide, rfl⟩
    · exact Or.inr ⟨1, by decide, rfl⟩
    · exact Or.inr ⟨2, by decide, rfl⟩
    · exact Or.inr ⟨3, by decide, rfl⟩
    · exact Or.inr ⟨4, by decide, rfl⟩
    · exact Or.inr ⟨5, by decide, rfl⟩
    · exact Or.inr ⟨6, by decide, rfl⟩
    · exact Or.inr ⟨7, by decide, rfl⟩
    · exact Or.inr ⟨8, by decide, rfl⟩
    · exact Or.inr ⟨9, by decide, rfl⟩

private theorem s3a3_dirGetFixed_ok_credit
    (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {bs : List (BitVec 8)} {fileCap : Nat}
    (hdc : DirDomainCaps 64 0 0 dir)
    (hch : dir.changed = [])
    (hname : name.length ≤ 64)
    (hrd : cliIo.rd F0 (pathOf dir.path name) = .ok bs)
    (hbs : bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd F0 dir name)
      (21185 + max 738 (fineReadFileCum fileCap))
      (fineReadFileLive fileCap)
      (fineReadFilePeak fileCap)
      (max 256 (fineReadFileMaxReq fileCap)) := by
  have hcap : ∀ bs', cliIo.rd F0 (pathOf dir.path name) = .ok bs' → bs'.length ≤ fileCap := by
    intro bs' h
    rw [hrd] at h
    injection h with heq
    subst heq
    exact hbs
  have hbase := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0 dir name hdc hname hcap
  dsimp only at hbase
  have h0 : max 0 fileCap = fileCap := by omega
  rw [h0] at hbase
  exact hbase.of_imp fun evs hm => by
    unfold DirGetEnv at hm ⊢
    simp only [hch, List.find?_nil] at hm ⊢
    unfold DirGetMissEnv at hm ⊢
    exact s3_seqEnv_mono (fun _ h => h)
      (fun _ hr => s3_seqEnv_mono
        (fun _ hrf => hrf.elim id fun ⟨herr, _, _⟩ => by rw [hrd] at herr; cases herr)
        (fun _ h => h) hr) hm

private theorem s3a3_afterLrGetPre_credit :
    PhaseCreditSpec fineCostModel (· = kpkAfterLrGetPreEvents) 19578 0 0 37 := by
  have h33 : PhaseCreditSpec fineCostModel (· = publicKeySerializeEvents) 9789 0 0 33 :=
    s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
  have h37 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 37 1) 9789 0 0 37 :=
    s3_rustAlloc_small_credit (req := 37) (al := 1) (by decide) (by decide)
  have hf33 : PhaseCreditSpec fineCostModel (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  exact (((h33.concat h37).concat hf33).of_imp fun _ h => by
    rw [h]
    unfold kpkAfterLrGetPreEvents
    exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem s3a3_reserveCap37_eq_two_mul {len spare : Nat} (hge : 37 ≤ len + spare) :
    reserveCap (len + spare) len 37 = 2 * (len + spare) := by
  unfold reserveCap
  omega

private theorem s3a3_reserveCap37_small {len spare : Nat} (hlt : len + spare < 37) :
    37 ≤ reserveCap (len + spare) len 37 ∧ reserveCap (len + spare) len 37 ≤ 73 := by
  unfold reserveCap
  omega

private theorem s3a3_ll_keep_bound (m w old : Nat) :
    m + w ≤ (m - old) + (old + w) := by
  omega

private theorem s3a3_ll_live_bound {m w old : Nat} (hold : old ≤ m + 7) :
    (m - old) + (2 * old + w) ≤ m + m + w + 14 := by
  omega

private theorem s3a3_ll_peak_bound {m w old : Nat} (hold : old ≤ m + 7) :
    (m - old) + (old + w) + (2 * old + w) ≤ 3 * m + 2 * w + 21 := by
  omega

private theorem s3a3_concat_seenReserveAt_credit
    {E₁ : List AllocEvent → Prop} {c₁ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 2105347 3162118 2097152)
    {seenBs : List (BitVec 8)} (hseen : seenBs.length ≤ 2097123)
    {spare : Nat} (hsp : spare < 37) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv E₁ (· = kpkSeenAppendReserveEventsAt seenBs spare))
      (c₁ + 279873) 4202513 6307867 4194318 := by
  let old := seenBs.length + spare
  let newCap := reserveCap old seenBs.length 37
  have hsp36 : spare ≤ 36 := Nat.le_of_lt_succ hsp
  have hold_max : old ≤ 2097159 :=
    Nat.le_trans (Nat.add_le_add hseen hsp36) (by decide)
  have htoNat : (BitVec.ofNat 64 old).toNat = old := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hold_max (by decide))]
  by_cases hz : old = 0
  · have hb0 : BitVec.ofNat 64 old = 0#64 := by rw [hz]
    have hlt37 : seenBs.length + spare < 37 := by change old < 37; rw [hz]; decide
    have hrc := s3a3_reserveCap37_small hlt37
    have hd : kpkSeenAppendReserveEventsAt seenBs spare = rustAllocEvents newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, seenBs, 37⟩ =
        rustAllocEvents newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hb0, ↓reduceIte]
      exact rfl
    have ha : PhaseCreditSpec fineCostModel
        (· = kpkSeenAppendReserveEventsAt seenBs spare) 9789 0 0 73 :=
      ((s3_rustAlloc_small_credit (req := newCap) (al := 1)
        (by decide) (Nat.le_trans hrc.2 (by decide))).of_imp
        (fun _ heq => by rw [heq, hd])).mono
        (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
    exact (h₁.concat ha).mono
      (Nat.add_le_add_left (by decide : 9789 ≤ 279873) c₁)
      (by decide) (by decide) (by decide)
  · have hpos : 0 < old := Nat.pos_of_ne_zero hz
    have hne0 : BitVec.ofNat 64 old ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      exact hz ht
    have hd : kpkSeenAppendReserveEventsAt seenBs spare = rustReallocEvents old newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, seenBs, 37⟩ =
        rustReallocEvents old newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hne0, ↓reduceIte]
      exact rfl
    by_cases hlt37 : old < 37
    · have hrc := s3a3_reserveCap37_small hlt37
      have hss : PhaseCreditSpec fineCostModel
          (· = kpkSeenAppendReserveEventsAt seenBs spare) 279873 0 0 73 :=
        ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (old := old) (new := newCap) (al := 1) (by decide)
          (Nat.le_trans (by decide : 1 ≤ 37) hrc.1) hpos
          (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans (Nat.le_of_lt hlt37) (by decide))
          (Nat.lt_of_lt_of_le (by decide : 0 < 37) hrc.1)
          (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hrc.2 (by decide))).of_imp
          (fun _ heq => by rw [heq, hd])).mono
          (Nat.le_trans (fineSmallReallocCost_le_9789_of_le_256 (Nat.le_trans hrc.2 (by decide)))
            (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
      exact (h₁.concat hss).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    · have hge37 : 37 ≤ old := Nat.le_of_not_lt hlt37
      have hnew_eq : newCap = 2 * old := s3a3_reserveCap37_eq_two_mul hge37
      have hnew_ge74 : 74 ≤ newCap := by
        rw [hnew_eq]
        exact Nat.mul_le_mul_left 2 hge37
      by_cases hold_sm : old ≤ 135167
      · have hnew270 : newCap ≤ 270334 := by
          rw [hnew_eq]
          exact Nat.le_trans (Nat.mul_le_mul_left 2 hold_sm) (by decide)
        by_cases hnew_sm : newCap ≤ 135167
        · have hsr : HasFineReallocCredit.smallReallocCost fineCostModel newCap ≤ 279873 :=
            Nat.le_trans (smallReallocCost_le_two_mul_add newCap)
              (Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnew_sm) 9539) (by decide))
          have hss : PhaseCreditSpec fineCostModel
              (· = kpkSeenAppendReserveEventsAt seenBs spare) 279873 0 0 135167 :=
            ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
              (old := old) (new := newCap) (al := 1) (by decide)
              (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74) hpos
              (by rw [fineCostModel_smallMaxReq_eq]; exact hold_sm)
              (Nat.lt_of_lt_of_le (by decide : 0 < 74) hnew_ge74)
              (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_sm)).of_imp
              (fun _ heq => by rw [heq, hd])).mono
              hsr (Nat.le_refl 0) (Nat.le_refl 0) hnew_sm
          exact (h₁.concat hss).mono
            (Nat.le_refl _) (by decide) (by decide) (by decide)
        · have hnew_gt : 135167 < newCap := Nat.lt_of_not_ge hnew_sm
          have hsl : PhaseCreditSpec fineCostModel
              (· = kpkSeenAppendReserveEventsAt seenBs spare) 122 278529 278529 270334 :=
            ((PhaseCreditSpec.rustRealloc_small_large fineCostModel
              (old := old) (new := newCap) (al := 1) (by decide)
              (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74) hpos
              (by rw [fineCostModel_smallMaxReq_eq]; exact hold_sm)
              (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)).of_imp
              (fun _ heq => by rw [heq, hd])).mono
              (by decide)
              (by rw [fineCostModel_largeCost_eq]
                  exact Nat.le_trans (Nat.add_le_add_right hnew270 8195) (by decide))
              (by rw [fineCostModel_largeCost_eq]
                  exact Nat.le_trans (Nat.add_le_add_right hnew270 8195) (by decide))
              hnew270
          exact (h₁.concat hsl).mono
            (Nat.add_le_add_left (by decide : 122 ≤ 279873) c₁)
            (by decide) (by decide) (by decide)
      · have hold_gt : 135167 < old := Nat.lt_of_not_ge hold_sm
        have hnew_gt : 135167 < newCap := by
          rw [hnew_eq]
          exact Nat.lt_of_lt_of_le hold_gt (Nat.le_mul_of_pos_left old (by decide : 0 < 2))
        have hnew_max : newCap ≤ 4194318 := by
          rw [hnew_eq]
          exact Nat.le_trans (Nat.mul_le_mul_left 2 hold_max) (by decide)
        let l_keep := 2097152 - old
        have hlive_w : 2105347 ≤ l_keep + HasFineReallocCredit.largeCost fineCostModel old := by
          rw [fineCostModel_largeCost_eq]
          exact Nat.le_trans (by decide : 2105347 ≤ 2097152 + 8195)
            (s3a3_ll_keep_bound 2097152 8195 old)
        have h₁' := h₁.mono (Nat.le_refl c₁) hlive_w (Nat.le_refl 3162118) (Nat.le_refl 2097152)
        have hll := h₁'.concat_rustRealloc_large_large (al := 1) (new := newCap)
          (by decide) (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74)
          (by rw [fineCostModel_smallMaxReq_eq]; exact hold_gt)
          (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)
        have hold_m7 : old ≤ 2097152 + 7 := Nat.le_trans hold_max (by decide)
        refine (hll.of_imp fun _ ⟨e1, e2, heq, he1, he2⟩ =>
          ⟨e1, e2, heq, he1, by rw [he2, hd]⟩).mono
          (Nat.add_le_add_left (by decide : HasFineReallocCredit.largeMetaCost fineCostModel ≤ 279873) c₁)
          ?_ ?_ (Nat.max_le.mpr ⟨by decide, hnew_max⟩)
        · dsimp only [l_keep]
          rw [fineCostModel_largeCost_eq, hnew_eq]
          exact Nat.le_trans (s3a3_ll_live_bound hold_m7) (by decide)
        · dsimp only [l_keep]
          rw [fineCostModel_largeCost_eq, fineCostModel_largeCost_eq, hnew_eq]
          exact Nat.max_le.mpr ⟨by decide, Nat.le_trans (s3a3_ll_peak_bound hold_m7) (by decide)⟩

private theorem s3a3_concat_seenAppendReserveMid_credit
    {E₁ : List AllocEvent → Prop} {c₁ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 2105347 3162118 2097152)
    {seenBs : List (BitVec 8)} (hseen : seenBs.length ≤ 2097123) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv E₁ (KpkSeenAppendReserveMidEnv seenBs))
      (c₁ + 279873) 4202513 6307867 4194318 := by
  have hfast : PhaseCreditSpec fineCostModel (ConcatEnv E₁ FreeOnlyEvs)
      (c₁ + 279873) 4202513 6307867 4194318 :=
    (h₁.concat (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
      (Nat.add_le_add_left (Nat.zero_le _) c₁) (by decide) (by decide) (by decide)
  have hfree37 : PhaseCreditSpec fineCostModel (· = optDeallocBufEvents 37#64) 0 0 0 0 :=
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h => by
      rw [h]
      exact freeOnlyEvs_optDeallocBufEvents 37#64
  have hgrow1 : ∀ spare, spare < 37 →
      PhaseCreditSpec fineCostModel
        (ConcatEnv E₁
          (· = kpkSeenAppendReserveEventsAt seenBs spare ++ optDeallocBufEvents 37#64))
        (c₁ + 279873) 4202513 6307867 4194318 := fun spare hsp =>
    (((s3a3_concat_seenReserveAt_credit h₁ hseen hsp).concat hfree37).of_imp
      fun _ ⟨e1, _, heq, he1, he2⟩ => by
        rw [heq, he2, ← List.append_assoc]
        exact ⟨e1 ++ kpkSeenAppendReserveEventsAt seenBs spare, optDeallocBufEvents 37#64,
          rfl, ⟨e1, _, rfl, he1, rfl⟩, rfl⟩).mono
      (Nat.le_of_eq (Nat.add_zero _)) (by decide) (by decide) (by decide)
  have hgrow : PhaseCreditSpec fineCostModel
      (fun evs => ∃ spare, spare < 37 ∧
        ConcatEnv E₁
          (· = kpkSeenAppendReserveEventsAt seenBs spare ++ optDeallocBufEvents 37#64) evs)
      (c₁ + 279873) 4202513 6307867 4194318 :=
    s3_phaseCreditSpec_exists hgrow1
  exact ((hfast.or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) (by decide) (by decide) (by decide)).of_imp
    fun _ ⟨e1, e2, heq, he1, hmid⟩ => by
      cases hmid with
      | fast e2 hf => exact Or.inl ⟨e1, e2, heq, he1, hf⟩
      | grow spare hsp => exact Or.inr ⟨spare, hsp, e1, _, heq, he1, rfl⟩

private theorem s3a3_fineReadFile_0 :
    fineReadFileCum 0 = 0 ∧ fineReadFileLive 0 = 0 ∧
    fineReadFilePeak 0 = 0 ∧ fineReadFileMaxReq 0 = 0 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  decide

private theorem s3a3_fineReadFile_4900 :
    fineReadFileCum 4900 = 573818 ∧ fineReadFileLive 4900 = 2105347 ∧
    fineReadFilePeak 4900 = 3162118 ∧ fineReadFileMaxReq 4900 = 2097152 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  rw [optLargeCost_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; decide)]
  decide

private theorem s3a3_fineReadFile_2M :
    fineReadFileCum 2097152 = 573818 ∧ fineReadFileLive 2097152 = 2105347 ∧
    fineReadFilePeak 2097152 = 3162118 ∧ fineReadFileMaxReq 2097152 = 2097152 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  rw [optLargeCost_of_gt fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; decide),
    fineCostModel_largeCost_eq]
  decide

private theorem s3a3_kpkMarkPoll_credit (i : Inputs)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey) :
    PhaseCreditSpec fineCostModel
      (CliKpkMarkPollEnv cliIo.rd DecimalEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd) DirPutEnv (runFiles i)
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)
      975111 4202513 6307867 4194318 := by
  let F0 := runFiles i
  let GetFixed := DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd
  let x : KpkMarkPollGhost :=
    ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
  have hdcOt : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime :=
    s3_dirDomainCaps_64 dirDomainCaps_opened_kpkOt (by decide)
  have hdcLr : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.lastResort :=
    s3_dirDomainCaps_64 dirDomainCaps_opened_kpkLr (by decide)
  have hkn64 : (keyName kpkId).length ≤ 64 :=
    Nat.le_trans (keyName_length_le kpkId) (by decide)
  have hbkn64 : (baseKeysName kpkId).length ≤ 64 :=
    Nat.le_trans (baseKeysName_length_le kpkId) (by decide)
  have hdec := s3a3_decimal_credit kpkId
  obtain ⟨hfc0_c, hfc0_l, hfc0_p, hfc0_r⟩ := s3a3_fineReadFile_0
  obtain ⟨hfc49_c, hfc49_l, hfc49_p, hfc49_r⟩ := s3a3_fineReadFile_4900
  obtain ⟨hfc2M_c, hfc2M_l, hfc2M_p, hfc2M_r⟩ := s3a3_fineReadFile_2M
  unfold CliKpkMarkPollEnv KpkOneTimePreAfterGetEnv
  dsimp only
  cases hOt : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) with
  | error u =>
    cases u
    dsimp only [OptKpkMarkOneTimeTailEnv]
    have hOtRd :
        cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .error () :=
      hOt
    have hg0 : PhaseCreditSpec fineCostModel
        (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
        595741 0 3162118 2097152 := by
      have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.oneTime
        (keyName kpkId) (fileCap := 0) hdcOt hkn64
        (fun _ h => by rw [hOtRd] at h; cases h)
      dsimp only at hraw
      rw [show max 0 0 = 0 from rfl, hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
      exact hraw.mono (by decide) (by decide) (by decide) (by decide)
    exact (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps (hdec.seq hg0)).mono
      (by decide) (by decide) (by decide) (by decide)
  | ok otBs =>
    cases otBs with
    | cons b bs =>
      dsimp only [OptKpkMarkOneTimeTailEnv, KpkOneTimeConsTailEnv]
      have hg49 : PhaseCreditSpec fineCostModel
          (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
          595741 2105347 3162118 2097152 := by
        have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.oneTime
          (keyName kpkId) (fileCap := 4900) hdcOt hkn64
          (fun bs' h => hkpkOt kpkId bs' h)
        dsimp only at hraw
        rw [show max 0 4900 = 4900 from rfl, hfc49_c, hfc49_l, hfc49_p, hfc49_r] at hraw
        exact hraw.mono (by decide) (by decide) (by decide) (by decide)
      have hputOt : PhaseCreditSpec fineCostModel
          (DirPutEnv StoresGhost.opened.kyber.oneTime (keyName kpkId) []) 9789 0 0 192 :=
        s3_dirPut_opened_credit rfl (keyName kpkId) []
      have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
        PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
      exact ((hdec.seq hg49).seq (hfree.seq (hdec.seq hputOt))).mono
        (by decide) (by decide) (by decide) (by decide)
    | nil =>
      dsimp only [OptKpkMarkOneTimeTailEnv]
      have hOtRd :
          cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .ok [] :=
        hOt
      have hgOtNil : PhaseCreditSpec fineCostModel
          (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
          21923 0 0 256 := by
        have hraw := s3a3_dirGetFixed_ok_credit F0 StoresGhost.opened.kyber.oneTime
          (keyName kpkId) (fileCap := 0) hdcOt rfl hkn64 hOtRd (Nat.le_refl 0)
        rw [hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
        exact hraw.mono (by decide) (by decide) (by decide) (by decide)
      have hOtPre : PhaseCreditSpec fineCostModel
          (SeqEnv (DecimalEnv kpkId)
            (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId)))
          41501 0 0 256 :=
        (hdec.seq hgOtNil).mono (by decide) (by decide) (by decide) (by decide)
      have hres := s3a3_baseKeysReserve_credit kpkId
      cases hLr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F0 (baseKeysName kpkId) with
      | error u =>
        cases u
        dsimp only [OptKpkMarkLastResortTailEnv, KpkLastResortPreAfterGetEnv]
        have hLrRd :
            cliIo.rd F0 (pathOf StoresGhost.opened.kyber.lastResort.path (baseKeysName kpkId)) =
              .error () :=
          hLr
        have hgLrErr : PhaseCreditSpec fineCostModel
            (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))
            595741 0 3162118 2097152 := by
          have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.lastResort
            (baseKeysName kpkId) (fileCap := 0) hdcLr hbkn64
            (fun _ h => by rw [hLrRd] at h; cases h)
          dsimp only at hraw
          rw [show max 0 0 = 0 from rfl, hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
          exact hraw.mono (by decide) (by decide) (by decide) (by decide)
        have hLrPre : PhaseCreditSpec fineCostModel _ 625108 0 3162118 2097152 :=
          (hdec.seq (hres.seq hgLrErr)).mono
            (by decide) (by decide) (by decide) (by decide)
        have hLrAll := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hLrPre
        have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
          PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
        exact (hOtPre.seq (hfree.seq hLrAll)).mono
          (by decide) (by decide) (by decide) (by decide)
      | ok seenBs =>
        dsimp only [OptKpkMarkLastResortTailEnv, KpkLastResortPreAfterGetEnv,
          KpkAfterLrGetCapFreeBranchEnv]
        have hLrRd :
            cliIo.rd F0 (pathOf StoresGhost.opened.kyber.lastResort.path (baseKeysName kpkId)) =
              .ok seenBs :=
          hLr
        have hseen2M : seenBs.length ≤ 2097152 := cliRd_ok_le_fileCap hLrRd
        have hgLrOk : PhaseCreditSpec fineCostModel
            (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))
            595003 2105347 3162118 2097152 := by
          have hraw := s3a3_dirGetFixed_ok_credit F0 StoresGhost.opened.kyber.lastResort
            (baseKeysName kpkId) (fileCap := 2097152) hdcLr rfl hbkn64 hLrRd hseen2M
          rw [hfc2M_c, hfc2M_l, hfc2M_p, hfc2M_r] at hraw
          exact hraw.mono (by decide) (by decide) (by decide) (by decide)
        have hLrPre : PhaseCreditSpec fineCostModel
            (SeqEnv (DecimalEnv kpkId)
              (SeqEnv (KpkBaseKeysReserveEnv kpkId)
                (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))))
            624370 2105347 3162118 2097152 :=
          (hdec.seq (hres.seq hgLrOk)).mono (by decide) (by decide) (by decide) (by decide)
        have hAfterPre := s3a3_afterLrGetPre_credit
        by_cases hmod : seenBs.length % 37 = 0
        · simp only [hmod, ↓reduceIte]
          by_cases hchk : hasChunk seenBs (baseKeyEntry spkId baseKey)
          · simp only [hchk, ↓reduceIte]
            have h15 : PhaseCreditSpec fineCostModel
                (SeqEnv (· = rustAllocEvents 15 1) FreeOnlyEvs) 9789 0 0 15 :=
              phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
                (s3_rustAlloc_small_credit (req := 15) (al := 1) (by decide) (by decide))
            have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
              PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
            exact (hOtPre.seq (hfree.seq (hLrPre.seq (hAfterPre.seq h15)))).mono
              (by decide) (by decide) (by decide) (by decide)
          · simp only [hchk, Bool.false_eq_true, ↓reduceIte]
            have hdiv : seenBs.length / 37 ≤ 2097152 / 37 := Nat.div_le_div_right hseen2M
            have hmul37 : seenBs.length = 37 * (seenBs.length / 37) := by
              have hdm := Nat.div_add_mod seenBs.length 37
              rw [hmod, Nat.add_zero] at hdm
              exact hdm.symm
            have hseen123 : seenBs.length ≤ 2097123 := by
              rw [hmul37]
              exact Nat.le_trans (Nat.mul_le_mul_left 37 hdiv) (by decide)
            have hAB := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOtPre
            have hABC : PhaseCreditSpec fineCostModel _ 665871 2105347 3162118 2097152 :=
              (hAB.seq hLrPre).mono (by decide) (by decide) (by decide) (by decide)
            have hBefore : PhaseCreditSpec fineCostModel _ 685449 2105347 3162118 2097152 :=
              (hABC.seq hAfterPre).mono (by decide) (by decide) (by decide) (by decide)
            have hCatMid := s3a3_concat_seenAppendReserveMid_credit hBefore hseen123
            have hSeqMid : PhaseCreditSpec fineCostModel
                (SeqEnv _ (KpkSeenAppendReserveMidEnv seenBs))
                965322 4202513 6307867 4194318 :=
              ((hBefore.or hCatMid).mono (by decide) (by decide) (by decide) (by decide)).of_imp
                fun _ hd => hd.elim Or.inl fun ⟨e1, e2, heq, h1, h2⟩ => Or.inr ⟨e1, e2, heq, h1, h2⟩
            have hPutLr : PhaseCreditSpec fineCostModel
                (DirPutEnv StoresGhost.opened.kyber.lastResort (baseKeysName kpkId)
                  (seenBs ++ baseKeyEntry spkId baseKey))
                9789 0 0 192 :=
              s3_dirPut_opened_credit rfl _ _
            exact ((hSeqMid.seq hPutLr).mono
              (by decide) (by decide) (by decide) (by decide)).of_imp fun _ h0 =>
              s3a3_seqEnv_assoc_left (s3a3_seqEnv_assoc_left
                (s3a3_seqEnv_assoc_left (s3a3_seqEnv_assoc_left h0)))
        · simp only [hmod, ↓reduceIte]
          have h14 : PhaseCreditSpec fineCostModel
              (SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs) 9789 0 0 14 :=
            phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
              (s3_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide))
          have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
            PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
          exact (hOtPre.seq (hfree.seq (hLrPre.seq (hAfterPre.seq h14)))).mono
            (by decide) (by decide) (by decide) (by decide)

end S3a3Sub3Helpers

/-- `PhaseCreditSpec` for `W4BinaryKpkMarkStepEnvFixed` under `oneTime ≤ 4900` and
`cliRd_ok_le_fileCap` (`baseKeysFile ≤ 2097152`, `seenBs.length % 37 = 0` grow `≤ 4194368`). -/
private theorem s3a_sub3_kpkMarkFixed_credit (i : Inputs)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey) :
    PhaseCreditSpec fineCostModel
      (W4BinaryKpkMarkStepEnvFixed cliIo.rd (runFiles i) kpkId spkId baseKey)
      1300000 4250000 6400000 4194368 := by
  unfold W4BinaryKpkMarkStepEnvFixed
  have hpoll := s3a3_kpkMarkPoll_credit i hkpkOt kpkId spkId baseKey
  have hbox :=
    LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers.w4BoxedStoreStep_small_phaseCredit
      fineCostModel_modelHyps 32
      (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide) hpoll
  exact hbox.mono (by decide) (by decide) (by decide) (by decide)

section S3aSub4Helpers

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryArchiveDirectEnv W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv
   W4BinaryPromoteArchiveEnv W4BinarySessLoadStepEnv W4BinarySessStoreStepEnv
   W4BinaryStageP1OkEnv W4BinaryStageP2MatchedWideEnv W4BinaryStageP4MatchedWideEnv
   W4CloneBDomEnv W4TrialRunWideEnv mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec FreeOnlyAlign16Evs)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (PhaseCreditSpec.rustAlloc_optLarge optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom recordSerializeMaxReq_le_of_dom recordSerializePeak_fine_le_of_dom
   recordSerializeTightCum_fine_le_of_dom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2TryDecryptMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 (w2TryDecryptSeeds738Cum)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (phaseCredit_archivedTrialLoop_le4 phaseCredit_promoteStateArchive)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_w4BoundedEvs_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers (stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4StageP3WideEnv phaseCredit_optStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (addressText_peer_length_le_64 phaseCreditSpec_seq_freeOnly_exact)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (sessionClone_dom_fine_phaseCredit_tight w4StageP2MatchedCheck_fine_phaseCredit
   w4StageP3Wide_fine_phaseCredit_tight w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (fineOptLarge_mono optLargeCost_fine_eq w4BoxedStoreStep_fine_le_28 w4BoxedStoreStep_fine_le_44)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4TrialDecEnv W4TrialDropEnv
   W4TryDecryptCall W4TryDecryptFailLinkedEnv W4TryDecryptPathBEnv
   w4RealFailTdCum)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4TryDecryptCallDomOf
   w4FailTdPeakOf w4TdBLiveOf w4TdMaxReqOf w4TrialMaxReqOf w4TrialPeakOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events
   dropVecChainEvents dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal
   pinFreeEvents senderFreeEvents sgnCapFreeEvents ssFirst3FreeEvents
   ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak
   recordDeserializeCancelEnv_fine_phaseCreditSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight dirGetEnv_path_readFile_fine_phaseCredit_tight
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)

private theorem s3a4_dhSmall_of_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  rw [fineCostModel_smallMaxReq_eq]
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem s3a4_w2Seeds738Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤ w4RealFailTdCum := by
  unfold w4RealFailTdCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem s3a4_w2MaxReqOf_le_5 {dhCap maxCt : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 maxCt ≤ w4TdMaxReqOf maxCt := by
  unfold w4TdMaxReqOf w2TryDecryptMaxReq
  have h104 : max 416 (104 * (2 * dhCap)) ≤ max 416 (104 * (2 * 5)) := by
    match dhCap, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans h104 (Nat.le_max_left _ _),
          Nat.le_max_right _ _⟩)
       (Nat.le_max_right _ _)⟩

private theorem s3a4_deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem s3a4_pinFreeEvents_freeOnlyAlign16 (pin : VecPin) :
    FreeOnlyAlign16Evs (pinFreeEvents pin) := by
  unfold pinFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) pin.cap.toNat

private theorem s3a4_sgnCapFreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (sgnCapFreeEvents cap) := by
  unfold sgnCapFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) cap.toNat

private theorem s3a4_vec104FreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (vec104FreeEvents cap) := by
  unfold vec104FreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) (cap.toNat * 104)

private theorem s3a4_mkFreeEvents_freeOnlyAlign16 (mk : MessageKeyGhost) :
    FreeOnlyAlign16Evs (mkFreeEvents mk) := by
  unfold mkFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (s3a4_pinFreeEvents_freeOnlyAlign16 mk.cipher)
        (s3a4_pinFreeEvents_freeOnlyAlign16 mk.mac))
      (s3a4_pinFreeEvents_freeOnlyAlign16 mk.iv))
    (s3a4_pinFreeEvents_freeOnlyAlign16 mk.seed)

private theorem s3a4_mkListFreeEvents_freeOnlyAlign16
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (mks.flatMap fun gk => mkFreeEvents gk.1) := by
  induction mks with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gk tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact s3a4_mkFreeEvents_freeOnlyAlign16 gk.1 ev h1
    · exact ih ev h2

private theorem s3a4_dropVecMessageKeyEvents_freeOnlyAlign16 (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (dropVecMessageKeyEvents cap mks) := by
  intro ev hev; dsimp only [dropVecMessageKeyEvents] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact s3a4_mkListFreeEvents_freeOnlyAlign16 mks ev h1
  · exact s3a4_vec104FreeEvents_freeOnlyAlign16 cap ev h2

private theorem s3a4_chainPairFreeEvents_freeOnlyAlign16 (gc : ChainGhost × ReceiverChain) :
    FreeOnlyAlign16Evs (chainPairFreeEvents gc) := by
  unfold chainPairFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨gc.1.srk.cap, gc.1.srk.ptr⟩)
        (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨gc.1.priv.cap, gc.1.priv.ptr⟩))
      (s3a4_sgnCapFreeEvents_freeOnlyAlign16 (optCkCapVal gc.1.ck gc.2.chainKey)))
    (s3a4_dropVecMessageKeyEvents_freeOnlyAlign16 gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))

private theorem s3a4_chainListFreeEvents_freeOnlyAlign16
    (cs : List (ChainGhost × ReceiverChain)) :
    FreeOnlyAlign16Evs (cs.flatMap chainPairFreeEvents) := by
  induction cs with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gc tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact s3a4_chainPairFreeEvents_freeOnlyAlign16 gc ev h1
    · exact ih ev h2

private theorem s3a4_dropSessionStructureLocal1Events_freeOnlyAlign16
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FreeOnlyAlign16Evs (dropSessionStructureLocal1Events G st) := by
  unfold dropSessionStructureLocal1Events ssFirst3FreeEvents ssTail3FreeEvents dropVecChainEvents
  have h1 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨G.localIk.cap, G.localIk.ptr⟩)
      (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨G.remoteIk.cap, G.remoteIk.ptr⟩))
    (s3a4_pinFreeEvents_freeOnlyAlign16 G.root)
  have h2 : FreeOnlyAlign16Evs (senderFreeEvents G.sender) := by
    cases G.sender with
    | none => exact FreeOnlyAlign16Evs.nil
    | some sg =>
      unfold senderFreeEvents
      exact FreeOnlyAlign16Evs.append
        (FreeOnlyAlign16Evs.append
          (FreeOnlyAlign16Evs.append
            (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨sg.srk.cap, sg.srk.ptr⟩)
            (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨sg.priv.cap, sg.priv.ptr⟩))
          (s3a4_sgnCapFreeEvents_freeOnlyAlign16 sg.ck.cap))
        (s3a4_dropVecMessageKeyEvents_freeOnlyAlign16 sg.mkCap [])
  have h3 : FreeOnlyAlign16Evs
      (((G.chains.zip st.receiverChains).flatMap chainPairFreeEvents) ++
        vec104FreeEvents G.chainsCap) := by
    intro ev hev
    rcases List.mem_append.mp hev with h3a | h3b
    · exact s3a4_chainListFreeEvents_freeOnlyAlign16 (G.chains.zip st.receiverChains) ev h3a
    · exact s3a4_vec104FreeEvents_freeOnlyAlign16 G.chainsCap ev h3b
  have h4 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (s3a4_sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.pending))
      (s3a4_sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.kyber)))
    (s3a4_pinFreeEvents_freeOnlyAlign16 ⟨G.alice.cap, G.alice.ptr⟩)
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append (FreeOnlyAlign16Evs.append h1 h2) h3) h4)
    (s3a4_pinFreeEvents_freeOnlyAlign16 G.pq)

private theorem s3a4_deallocCreditSpec_dropSessionStructureLocal1
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hok : SessionDropCapsOk G st) :
    DeallocCreditSpec fineCostModel
      (· = dropSessionStructureLocal1Events G st)
      (ssStateLargeLive fineCostModel G st) where
  req_align := by
    rintro _ rfl ev hev
    exact (PhaseCreditSpec.freeOnly_align16 fineCostModel).req_align _
      (s3a4_dropSessionStructureLocal1Events_freeOnlyAlign16 G st) ev hev
  credit_sub := by
    rintro st0 _ rfl
    exact stepEvents_dropSessionStructureLocal1_bounds fineCostModel hok st0

private theorem s3a4_tryDecryptPathB_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptCallDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathBEnv F K td)
      w4RealFailTdCum (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    td.stBytes td.w.pre_pb td.w.vn td.w.pb td.w.st0 td.w.sckaMsg td.w.v
    td.w.xInit td.w.xNew td.w.xAdd td.w.xRk td.w.xSInto td.w.xCInto
    (s3a4_dhSmall_of_le_5 hDom.dh_le) hDom.caps_len hDom.chain_le hDom.top_tight hDom.ct_le
  exact hBase.mono
    (s3a4_w2Seeds738Cum_le_5 td.needGrow hDom.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (s3a4_w2MaxReqOf_le_5 hDom.dh_le)

private theorem s3a4_failedTdCancel_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (s3a4_dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (s3a4_w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _) (s3a4_w2MaxReqOf_le_5 hDom.td_dom.dh_le)
  have hDrop := s3a4_deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem s3a4_trialDec_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialDecEnv F x)
      deserCancelFineCum (sessDeserLargeLive fineCostModel x.r_dec)
      deserCancelFinePeak deserCancelFineMaxReq := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hmaxR : max 212992 (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq :=
    Nat.max_le.mpr ⟨by decide, hDom.enc_le⟩
  have hSym := sessDeserializeCancelEnv_phaseCreditSpec fineCostModel h33 hmaxR
  have hCl := sessDeserializeCancelEnv_fine_phaseCreditSpec hDom.enc_le
  exact
    { req_align := hCl.req_align
      credit_le := fun st0 {_} hE => by
        obtain ⟨hc, _, hp⟩ := hCl.credit_le st0 hE
        obtain ⟨_, hl, _⟩ := hSym.credit_le st0 hE
        exact ⟨hc, hl, hp⟩ }

private theorem s3a4_trialRunWide_credit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDomOf F K maxCt x) :
    PhaseCreditSpec fineCostModel (W4TrialRunWideEnv F K x)
      (8277456 + w4RealFailTdCum + 8674) 0 (w4TrialPeakOf maxCt) (w4TrialMaxReqOf maxCt) := by
  have hCloneFail := w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit
    (curPqCap := 286196)
    (Or.inr ⟨x.ses_tr, rfl, hDom.tr_gv, hDom.tr_dom⟩)
    (s3a4_failedTdCancel_credit hDom.tr_fail)
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCloneFail).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem s3a4_sessLoadStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinarySessLoadStepEnv cliIo.rd F0 peer)
      17517856 5316629 8478747 2097152 := by
  unfold W4BinarySessLoadStepEnv cliSessionKitLoadPollEnv
  have hpeerVal : peer.val.name.length ≤ 40 := hpeer
  have haddrLen : (addressText peer.val).length ≤ 64 := addressText_peer_length_le_64 hpeer
  have hdcSess := s3_dirDomainCaps_64 dirDomainCaps_opened_sess (by decide)
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeerVal
  have hGetSess : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.sessions (addressText peer.val))
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.sessions (addressText peer.val) hdcSess haddrLen
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptDeser : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val)))
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        have hlen : (b0 :: bsRest).length ≤ 2097152 := by
          change cliIo.rd F0 _ = .ok (b0 :: bsRest) at hget
          exact cliRd_ok_le_fileCap hget
        exact s3_phaseCreditSpec_exists fun r henc => by
          unfold ofBytesEnv
          have hlen' : (encodeRecord r).length ≤ 2097152 := by rw [henc]; exact hlen
          exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen').of_imp fun _ h => h.2
  have hPoll := hAddr.seq
    (hGetSess.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptDeser))
  exact (w4BoxedStoreStep_fine_le_28 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_idTrustStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdTrustStepEnv cliIo.rd F0 peer remoteIdKey)
      596479 2105347 3162118 2097152 := by
  unfold W4BinaryIdTrustStepEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPoll := seq_freeOnly_phaseCredit fineCostModel_freeNonInc hGet
  exact (w4BoxedStoreStep_fine_le_44 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_idSaveStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdSaveStepEnv cliIo.rd F0 peer remoteIdKey)
      625846 2105347 3162118 2097152 := by
  unfold W4BinaryIdSaveStepEnv cliIdentityKitSavePollEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hTail : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity peer.val remoteIdKey
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name))
      29367 0 0 192 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 9789 0 0 33 := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
      have hput := s3_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        (Nat.le_trans hpeer (by decide)) remoteIdKey.serialize
      have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (hf.seq (hpks.seq hput)).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hGet.seq hTail)).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_recordSerializeSeqFree_credit
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (RecordSerializeSeqFreeEnv g r)
      8420940 3480713 3480713 2097152 := by
  have hp : 1080975 + optLargeCost fineCostModel 286196 + optLargeCost fineCostModel 2097152 ≤
      3480713 := by
    rw [optLargeCost_fine_eq 286196, optLargeCost_fine_eq 2097152]; decide
  have hr : max (max 208000 286196) 2097152 ≤ 2097152 := by decide
  exact (PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps g r).mono
    (recordSerializeTightCum_fine_le_of_dom hValid)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializeMaxReq_le_of_dom hValid hEnc) hr)

private theorem s3a4_sessStoreStep_credit (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_rec).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinarySessStoreStepEnv peer g_rec r_rec)
      8442732 3480713 3480713 2097152 := by
  unfold W4BinarySessStoreStepEnv cliSessionKitStorePollEnv
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeer
  have hSer := s3a4_recordSerializeSeqFree_credit hValid hEnc
  have hPut := s2b_dirPutTail_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText peer.val)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hAddr.seq (hSer.seq hPut))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_archiveDirect_credit {maxEncLen : Nat} (hEnc : maxEncLen ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryArchiveDirectEnv maxEncLen)
      4213766 2105347 2105347 2097152 := by
  unfold W4BinaryArchiveDirectEnv
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hAlloc : PhaseCreditSpec fineCostModel
      (fun e => ∃ n ≤ maxEncLen, e = rustAllocEvents n 1)
      4203843 2105347 2105347 2097152 :=
    s3_phaseCreditSpec_exists fun n hn => by
      have hnCap : n ≤ 2097152 := Nat.le_trans hn hEnc
      have hl : optLargeCost fineCostModel n ≤ 2105347 := by
        rw [optLargeCost_fine_eq n]
        exact Nat.le_trans (fineOptLarge_mono hnCap) (by decide)
      exact (PhaseCreditSpec.rustAlloc_optLarge fineCostModel_modelHyps
        (req := n) (al := 1) (by decide)).mono (by omega) hl hl hnCap
  have hVec : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  exact (hf.seq (hAlloc.seq (hVec.seq hf))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_promoteArchive_credit
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_arch).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryPromoteArchiveEnv g_arch r_arch)
      8430863 3480713 3480713 2097152 := by
  unfold W4BinaryPromoteArchiveEnv
  have hPush : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  have hProm := phaseCredit_promoteStateArchive fineCostModel_modelHyps
    (s3a4_recordSerializeSeqFree_credit hValid hEnc) hPush
  have hDir := s3a4_archiveDirect_credit hEnc
  exact (hProm.or hDir).mono (by decide) (by decide) (by decide) (by decide)

private theorem s3a4_w4CloneBDom_credit :
    PhaseCreditSpec fineCostModel W4CloneBDomEnv
      8277456 1375366 1375366 286196 where
  req_align evs := fun ⟨G, ses, hgv, hdom, hE⟩ => by
    have hm : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G ses.state)
        8277456 1375366 1375366 286196 :=
      (sessionClone_dom_fine_phaseCredit_tight hgv hdom).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    exact hm.req_align evs hE
  credit_le st0 := fun ⟨G, ses, hgv, hdom, hE⟩ => by
    have hm : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G ses.state)
        8277456 1375366 1375366 286196 :=
      (sessionClone_dom_fine_phaseCredit_tight hgv hdom).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    exact hm.credit_le st0 hE

private theorem s3a_sub4_untrusted_and_pathB_credit (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (w4 : W4BinaryRecvPrekeyParams)
    (hw4 : W4BinaryRecvPrekeyDom (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey e ∨
        W4BinaryRecvPrekeyPathBWideEnv w4 e)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
  obtain ⟨_, hpeer, hfiles, hrd, hDom⟩ := hw4 peerAddr rfl
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoad : PhaseCreditSpec fineCostModel
      (W4BinarySessLoadStepEnv w4.base.rd w4.base.files w4.base.peer)
      17517856 5316629 8478747 2097152 := by
    rw [hrd, hfiles]; exact s3a4_sessLoadStep_credit (runFiles i) w4.base.peer hpeer
  have hTrust : PhaseCreditSpec fineCostModel
      (W4BinaryIdTrustStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      596479 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a4_idTrustStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hStr : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv w4.base.peer.name)
      9619 0 0 40 :=
    stringClone_phaseCredit_small fineCostModel_modelHyps hpeer
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
  have hUntr : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18123954 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1UntrustedEnv
    exact (hLoad.seq (hTrust.seq (hStr.seq hf))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hP1Ok : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1OkEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18114335 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1OkEnv
    exact (hLoad.seq (phaseCredit_optStageEnv fineCostModel_modelHyps hTrust)).mono
      (by decide) (by decide) (by decide) (by decide)
  let P := mkW4RecvPrekeyWideSlotParams w4.base
  have hLoop :=
    phaseCredit_archivedTrialLoop_le4
      (DecEnv := P.DecEnv) (TrialEnv := P.TrialEnv) (DropEnv := P.DropEnv) (xs := P.archivedTrials)
      (l_dec := fun x => sessDeserLargeLive fineCostModel x.r_dec)
      hDom.outer_dom.trials_len4
      (fun x hx => (hDom.trials_dom x hx).live_le_peak)
      (fun x hx => s3a4_trialDec_credit (hDom.trials_dom x hx))
      (fun x hx => s3a4_trialRunWide_credit (hDom.trials_dom x hx))
      (fun x hx =>
        s3a4_deallocCreditSpec_mono_le
          (s3a4_deallocCreditSpec_dropSessionStructureLocal1 (hDom.trials_dom x hx).drop_caps)
          (hDom.trials_dom x hx).live_le_drop)
  have hProm := s3a4_promoteArchive_credit w4.base.g_arch w4.base.r_arch
    hDom.outer_dom.arch_valid hDom.outer_dom.arch_enc
  have hP2B := w4StageP2MatchedCheck_fine_phaseCredit.seq
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (hf.or (hLoop.seq (hf.or (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hProm)))))
  have hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv
      w4RealFailTdCum
      (w4TdBLiveOf msgCapBytes)
      (w4FailTdPeakOf msgCapBytes)
      (w4TdMaxReqOf msgCapBytes) := by
    change PhaseCreditSpec fineCostModel
      (if w4.base.isPathB then W4TryDecryptPathBEnv w4.base.F w4.base.K w4.base.td_B
       else fun _ => False)
      w4RealFailTdCum
      (w4TdBLiveOf msgCapBytes)
      (w4FailTdPeakOf msgCapBytes)
      (w4TdMaxReqOf msgCapBytes)
    cases hpb : w4.base.isPathB
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact s3a4_tryDecryptPathB_credit (hDom.tdB_dom hpb)
  have hP3B := w4StageP3Wide_fine_phaseCredit_tight s3a4_w4CloneBDom_credit hTdB
  have hSave : PhaseCreditSpec fineCostModel
      (W4BinaryIdSaveStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      625846 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a4_idSaveStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hStore := s3a4_sessStoreStep_credit w4.base.peer w4.base.g_out0 w4.base.r_out0 hpeer
    hDom.outer_dom.out0_valid hDom.outer_dom.out0_enc
  have hP4B := (phaseCredit_optStageEnv fineCostModel_modelHyps hSave).seq
    (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (phaseCredit_optStageEnv fineCostModel_modelHyps hStore))
  have hOptP2B := phaseCredit_optStageEnv fineCostModel_modelHyps hP2B
  have hOptP3B := phaseCredit_optStageEnv fineCostModel_modelHyps hP3B
  have hOptP4B := phaseCredit_optStageEnv fineCostModel_modelHyps hP4B
  have hPathB : PhaseCreditSpec fineCostModel (W4BinaryRecvPrekeyPathBWideEnv w4)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
    unfold W4BinaryRecvPrekeyPathBWideEnv
    exact (hP1Ok.seq (hOptP2B.seq (hOptP3B.seq hOptP4B))).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (hUntr.or hPathB).mono (by decide) (by decide) (by decide) (by decide)

end S3aSub4Helpers

private theorem s3a_sub5_pathAC_credit (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (w4 : W4BinaryRecvPrekeyParams)
    (hw4 : W4BinaryRecvPrekeyDom (.recv peerAddr) i w4)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105)
    (hspk : ∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230)
    (hopk : ∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (hkpkLr : ∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (hSpkDec : ∀ {bs : List (BitVec 8)} {L : Nat}, bs.length ≤ L → L ≤ 4900 →
      PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808)
    (hPkDec : ∀ {bs : List (BitVec 8)}, bs.length ≤ 125 →
      PhaseCreditSpec fineCostModel (CliPkDecodeEnv bs) 2476617 0 0 256)
    (hIkpDec : ∀ {gr : Except Unit (List (BitVec 8))},
      (∀ bs, gr = .ok bs → bs.length ≤ 105) →
      PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 2085057 0 0 256)
    (hMark : ∀ (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey),
      PhaseCreditSpec fineCostModel
        (W4BinaryKpkMarkStepEnvFixed cliIo.rd (runFiles i) kpkId spkId baseKey)
        1300000 4250000 6400000 4194368) :
    PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryRecvPrekeyPathAWideEnvFixed w4 e ∨
        W4BinaryRecvPrekeyPathCWideEnvFixed w4 e)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq :=
  s3a5_pathAC_credit_core i peerAddr w4 hw4 hikp hspk hopk hkpkOt hkpkLr
    hSpkDec hPkDec hIkpDec hMark

private theorem s3a_w4Fixed_credit (W : CliHooks) (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (_hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w4 : W4BinaryRecvPrekeyParams)
    (hw4 : W4BinaryRecvPrekeyDom (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyWideSlotEnvFixed w4)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
  obtain ⟨hikp, hspk, hopk, hkpkOt, hkpkLr⟩ := s3a_sub0_store_file_caps W i hi
  have hUB := s3a_sub4_untrusted_and_pathB_credit i peerAddr w4 hw4
  have hAC := s3a_sub5_pathAC_credit i peerAddr w4 hw4 hikp hspk hopk hkpkOt hkpkLr
    (fun hbs hL => s3a_sub1_cliSpkDecode_credit hbs hL)
    (fun hbs => s3a_w1c_cliPkDecode_credit hbs)
    (fun h => s3a_w1c_optIkpTryFrom_credit h)
    (fun kpkId spkId bk => s3a_sub3_kpkMarkFixed_credit i hkpkOt kpkId spkId bk)
  have h4arms : PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey e ∨
        W4BinaryRecvPrekeyPathBWideEnv w4 e ∨
        W4BinaryRecvPrekeyPathAWideEnvFixed w4 e ∨
        W4BinaryRecvPrekeyPathCWideEnvFixed w4 e)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
    refine (hUB.or hAC).of_imp ?_ |>.mono
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    rintro e (hU | hB | hA | hC)
    · exact Or.inl (Or.inl hU)
    · exact Or.inl (Or.inr hB)
    · exact Or.inr (Or.inl hA)
    · exact Or.inr (Or.inr hC)
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
  have hSeq := (h4arms.seq hFree).mono
    (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (Nat.add_zero _))
    (Nat.max_le.mpr ⟨Nat.le_refl _, by rw [Nat.add_zero]; exact d3RecvW4Ext_live_le_peak⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
  unfold W4BinaryRecvPrekeyWideSlotEnvFixed
  exact (hFree.or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

end S3aHoleAHelpers

private theorem s3_hole_a (W : CliHooks) (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w4 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryRecvPrekeyParams)
    (hw4 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryRecvPrekeyDom
      (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.W4BinaryRecvPrekeyWideSlotEnvFixed w4)
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq :=
  s3a_w4Fixed_credit W i peerAddr hi hparse w4 hw4

section S3bHoleBHelpers

/-!
### Binary-Kit W4 `PhaseGroupSpec` Helpers

Worst-case Path C (`W4BinaryRecvPrekeyPathCWideEnvFixed`) binary-kit store and key-decode steps
total `3024 * FineScale`, fitting within `binaryKitW4FixedGrpS = d3RecvW4ExtGrpS + 2000 * FineScale`
(`3231 * FineScale` budget across the 8 store steps and P2/P3 allocations; Paths A, B, and
Untrusted are strictly smaller).
-/

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open LibsignalBinary.Heap.Fine (MmapThresholdReq)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText decimalText keyName)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers
  (decimalText_digit decimalText_ge10 decimalText_length_le)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec dropClonedSessionEvents_groupSpec
   initialStateEnv_groupSpec optTailCloneEvents_groupSpec recordSerializeDomFineGrpS
   segCloneDomFineGrpS segCloneEnv_dom_fine_groupSpec
   senderChainCloneDomFineGrpS senderChainCloneEnv_dom_fine_groupSpec
   serializePrev1DomFineGrpS serializeSomeSeqFreeEnv_groupSpec vecCloneEvents_groupSpec
   vecVecClone1Events_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryAcceptWideEnv W4BinaryArchiveDirectEnv
   W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv W4BinaryInitBobWideEnv
   W4BinaryKpkGetStepEnv W4BinaryPkGetStepEnv W4BinaryPkRemoveStepEnv
   W4BinaryPromoteArchiveEnv W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams
   W4BinaryRecvPrekeyPathBWideEnv W4BinarySelfKpStepEnv W4BinarySelfRegIdStepEnv
   W4BinarySessLoadStepEnv W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv
   W4BinarySpkGetStepEnv W4BinaryStageP1OkEnv W4BinaryStageP1UntrustedEnv
   W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv W4BinaryStageP2PathCWideEnv
   W4BinaryStageP4MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv W4TrialRunWideEnv
   mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound fineSmallAllocGroupS nonFreeCount nonFreeCount_append nonFreeCount_nil
   nonFreeCount_rustAllocEvents nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents
   smallAllocGroupS_fineCostModel_eq smallAllocGroupS_le_4737_of_le_12
   smallAllocGroupS_le_11056_of_le_28 smallAllocGroupS_le_16659_of_le_44
   smallAllocGroupS_le_24623_of_le_60)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryKpkMarkStepEnvFixed W4BinaryRecvPrekeyPathAWideEnvFixed
   W4BinaryRecvPrekeyPathCWideEnvFixed W4BinaryRecvPrekeyWideSlotEnvFixed
   W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (FreeOnlyAlign16Evs IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializePrev1SeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 w2TryDecryptFailTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (FreshBobCloneDom SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4PqxdhAcceptEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4ErrTailWideEnv W4StageP2MatchedCheckEnv W4StageP3WideEnv
   W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyRealParams
   W4RecvPrekeyTryDecACEnv mkW4RecvPrekeySlotParams serializePrev1FreshBobFineGrpS
   w4RealTrialFineGrpS w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4FailedTdDomOf W4RecvPrekeyRealDomOf)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (archivedTrialLoop_le4_groupSpec phaseGroupSpec_ite_nil phaseGroupSpec_optStage
   promoteStateArchive_groupSpec segCloneEnv_freshBobCloneDom_fine_groupSpec
   segCloneFreshBobFineGrpS w4BobSessionBuild_groupSpec w4BoundedEvs_groupSpec
   w4BoxedStoreStep_le_28_fine_groupSpec w4BoxedStoreStep_le_44_fine_groupSpec
   w4ErrTailWide_fine_groupSpec w4ErrTailWideFineGrpS w4InitBobSpqrFineGrpS
   w4PqxdhAccept_fine_groupSpec w4StageP2MatchedCheck_fine_groupSpec
   w4StageP2MatchedCheckFineGrpS w4StageP3Wide_fine_groupSpec w4StageP3WideFineGrpS
   w4TryDecryptCloneFailWide_fine_groupSpec)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (PreKeyDeserializeEnv RecordCodecLoopEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkCaps SpkDecodeEnv SpkErrTailEnv SpkField SpkLoopBoundedEnv SpkLoopEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (chainPairFreeEvents dropSessionStructureLocal1Events dropVecChainEvents
   dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal pinFreeEvents senderFreeEvents
   sgnCapFreeEvents ssFirst3FreeEvents ssTail3FreeEvents vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineGrpS recordDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_groupSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

private theorem dirGet_readPlain_groups_s3b
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name)
      (42 * FineScale) := by
  refine (s3_dirGetFixed_groups fineCostModel rd F0 dir name).of_imp fun evs h => ?_
  unfold DirGetEnv
  unfold DirGetEnv at h
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some _ => rw [hfind] at h; exact h
  | none =>
    rw [hfind] at h
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a.DirGetMissEnv at h ⊢
    exact s3_seqEnv_mono (fun _ hp => hp)
      (fun _ hr => s3_seqEnv_mono (fun _ hrf => Or.inl hrf) (fun _ ha => ha) hr) h

private theorem pushBytesEvents_nonFree_le_s3b :
    ∀ (m cap len : Nat), nonFreeCount (pushBytesEvents m cap len) ≤ m
  | 0, _, _ => by simp [pushBytesEvents, nonFreeCount_nil]
  | m + 1, cap, len => by
    unfold pushBytesEvents
    rw [nonFreeCount_append]
    have hstep : nonFreeCount (pushByteStep cap len).2 ≤ 1 := by
      unfold pushByteStep
      split
      · dsimp only; simp [nonFreeCount_nil]
      · dsimp only; split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
    have ih := pushBytesEvents_nonFree_le_s3b m (pushByteStep cap len).1 (len + 1)
    omega

private theorem decimal_groups_s3b (n : BitVec 32) :
    PhaseGroupSpec fineCostModel (DecimalEnv n) (30 * FineScale) := by
  have hnf : NonFreeBound (DecimalEnv n) 10 := by
    intro evs h
    unfold DecimalEnv LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.decimalEvents at h
    subst h
    have hlen : (decimalText n.toNat).length ≤ 10 :=
      decimalText_length_le 10 n.toNat (by omega) (Nat.lt_trans n.isLt (by omega))
    exact Nat.le_trans (pushBytesEvents_nonFree_le_s3b _ 0 0) hlen
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private def spkIndLe_s3b (k x : Nat) : Nat :=
  if x ≤ k then 1 else 0

private theorem spkIndLe_mono_s3b (k : Nat) {x y : Nat} (h : x ≤ y) :
    spkIndLe_s3b k y ≤ spkIndLe_s3b k x := by
  unfold spkIndLe_s3b
  split_ifs <;> omega

private theorem spkIndLe_lt_s3b (k x y : Nat) (hx : x ≤ k) (hy : k < y) :
    spkIndLe_s3b k y + 1 ≤ spkIndLe_s3b k x := by
  unfold spkIndLe_s3b
  simp [hx, Nat.not_le.mpr hy]

/-- 14-tier doubling rank on `Vec<u8>` capacity `c` for `SpkLoopBoundedEnv` at `rem ≤ 4900`:
each `reserveCap c 0 v.length` with `c < v.length ≤ 4900` strictly decreases `spkCapRank_s3b`. -/
private def spkCapRank_s3b (c : Nat) : Nat :=
  spkIndLe_s3b 0 c + spkIndLe_s3b 4 c + spkIndLe_s3b 8 c + spkIndLe_s3b 16 c +
  spkIndLe_s3b 32 c + spkIndLe_s3b 64 c + spkIndLe_s3b 128 c + spkIndLe_s3b 256 c +
  spkIndLe_s3b 512 c + spkIndLe_s3b 1024 c + spkIndLe_s3b 2048 c + spkIndLe_s3b 4096 c +
  spkIndLe_s3b 4899 c + spkIndLe_s3b 4899 c

private def spkCapsRank_s3b (caps : SpkCaps) : Nat :=
  spkCapRank_s3b caps.pub + spkCapRank_s3b caps.priv + spkCapRank_s3b caps.sig

private theorem spkCapRank_step_lt_s3b {c vlen : Nat} (hlt : c < vlen) (hle : vlen ≤ 4900) :
    spkCapRank_s3b (reserveCap c 0 vlen) + 1 ≤ spkCapRank_s3b c := by
  have hres : max 8 (max vlen (2 * c)) ≤ reserveCap c 0 vlen := by
    unfold reserveCap; omega
  generalize reserveCap c 0 vlen = r at hres ⊢
  have hr8 : 8 ≤ r := by omega
  have hrv : vlen ≤ r := by omega
  have hr2 : 2 * c ≤ r := by omega
  have hcr : c ≤ r := by omega
  have m0 := spkIndLe_mono_s3b 0 hcr
  have m4 := spkIndLe_mono_s3b 4 hcr
  have m8 := spkIndLe_mono_s3b 8 hcr
  have m16 := spkIndLe_mono_s3b 16 hcr
  have m32 := spkIndLe_mono_s3b 32 hcr
  have m64 := spkIndLe_mono_s3b 64 hcr
  have m128 := spkIndLe_mono_s3b 128 hcr
  have m256 := spkIndLe_mono_s3b 256 hcr
  have m512 := spkIndLe_mono_s3b 512 hcr
  have m1024 := spkIndLe_mono_s3b 1024 hcr
  have m2048 := spkIndLe_mono_s3b 2048 hcr
  have m4096 := spkIndLe_mono_s3b 4096 hcr
  have m4899 := spkIndLe_mono_s3b 4899 hcr
  unfold spkCapRank_s3b
  by_cases hc4 : c ≤ 4
  · have s := spkIndLe_lt_s3b 4 c r hc4 (by omega); omega
  · by_cases hc8 : c ≤ 8
    · have s := spkIndLe_lt_s3b 8 c r hc8 (by omega); omega
    · by_cases hc16 : c ≤ 16
      · have s := spkIndLe_lt_s3b 16 c r hc16 (by omega); omega
      · by_cases hc32 : c ≤ 32
        · have s := spkIndLe_lt_s3b 32 c r hc32 (by omega); omega
        · by_cases hc64 : c ≤ 64
          · have s := spkIndLe_lt_s3b 64 c r hc64 (by omega); omega
          · by_cases hc128 : c ≤ 128
            · have s := spkIndLe_lt_s3b 128 c r hc128 (by omega); omega
            · by_cases hc256 : c ≤ 256
              · have s := spkIndLe_lt_s3b 256 c r hc256 (by omega); omega
              · by_cases hc512 : c ≤ 512
                · have s := spkIndLe_lt_s3b 512 c r hc512 (by omega); omega
                · by_cases hc1024 : c ≤ 1024
                  · have s := spkIndLe_lt_s3b 1024 c r hc1024 (by omega); omega
                  · by_cases hc2048 : c ≤ 2048
                    · have s := spkIndLe_lt_s3b 2048 c r hc2048 (by omega); omega
                    · by_cases hc4096 : c ≤ 4096
                      · have s := spkIndLe_lt_s3b 4096 c r hc4096 (by omega); omega
                      · have s := spkIndLe_lt_s3b 4899 c r (by omega) (by omega); omega

private theorem rustAlloc_linear_groups_s3b (n : Nat) (hn : 0 < n) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents n 1) (3172 * (n + 1)) := by
  by_cases h60 : n ≤ 60
  · have hm : n ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
    have hsm := PhaseGroupSpec.rustAlloc_small fineCostModel (size := n) (align := 1) (by decide) hm
    rw [smallAllocGroupS_fineCostModel_eq] at hsm
    by_cases h12 : n ≤ 12
    · have hb := smallAllocGroupS_le_4737_of_le_12 h12
      exact hsm.mono (by omega)
    · by_cases h28 : n ≤ 28
      · have hb := smallAllocGroupS_le_11056_of_le_28 h28
        exact hsm.mono (by omega)
      · have hb := smallAllocGroupS_le_24623_of_le_60 h60
        exact hsm.mono (by omega)
  · exact (PhaseGroupSpec.rustAlloc_any fineCostModel n 1).mono (by unfold FineScale; omega)

private theorem optByteFree_spk_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.OptByteFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap

private theorem spkEpilogueFree_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkEpilogueFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
  exact FreeOnlyEvs.append
    (FreeOnlyEvs.append (optByteFree_spk_freeOnly_s3b h1) (optByteFree_spk_freeOnly_s3b h2))
    (optByteFree_spk_freeOnly_s3b h3)

private theorem dropDecodeError_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DropDecodeErrorEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · exact FreeOnlyEvs.singleton 8 72
  · exact FreeOnlyEvs.append (FreeOnlyEvs.singleton 8 (c * 32)) (FreeOnlyEvs.singleton 8 72)

private theorem spkErrTail_groups_s3b :
    PhaseGroupSpec fineCostModel SpkErrTailEnv (6 * FineScale) := by
  have hnf : NonFreeBound SpkErrTailEnv 2 := by
    intro evs h
    cases h with
    | nil => simp [nonFreeCount_nil]
    | fromOnly => simp [nonFreeCount_rustAllocEvents]
    | fromPush hp =>
      rw [nonFreeCount_append]
      have h72 : nonFreeCount (rustAllocEvents 72 8) = 1 := nonFreeCount_rustAllocEvents 72 8
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
      · simp [h72, nonFreeCount_nil]
      · simp [h72, nonFreeCount_rustAllocEvents]
      · omega
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private theorem doReserveClear_groups_s3b (cap vlen : Nat) :
    PhaseGroupSpec fineCostModel (· = doReserveClearEvents cap vlen) (3 * FineScale) := by
  have hnf : NonFreeBound (· = doReserveClearEvents cap vlen) 1 := by
    intro evs h
    subst h
    unfold doReserveClearEvents
    split
    · simp [nonFreeCount_nil]
    · split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private theorem spkCaps_set_get_s3b (f : SpkField) (caps : SpkCaps) :
    caps.set f (caps.get f) = caps := by
  cases f <;> rfl

private theorem spkCapsRank_set_lt_s3b (f : SpkField) (caps : SpkCaps) {vlen : Nat}
    (hlt : caps.get f < vlen) (hle : vlen ≤ 4900) :
    spkCapsRank_s3b (caps.set f (reserveCap (caps.get f) 0 vlen)) + 1 ≤ spkCapsRank_s3b caps := by
  cases f <;>
  · dsimp only [SpkCaps.get, SpkCaps.set, spkCapsRank_s3b] at hlt ⊢
    have h := spkCapRank_step_lt_s3b hlt hle
    omega

private theorem spkLoopBounded_eq_groups_s3b {rem : Nat} {caps : SpkCaps} {evs : List AllocEvent}
    (h : SpkLoopBoundedEnv rem caps evs) :
    rem ≤ 4900 →
      PhaseGroupSpec fineCostModel (· = evs)
        (3172 * rem + (3 * spkCapsRank_s3b caps + 6) * FineScale) := by
  induction h with
  | done htail =>
    intro _
    exact (spkErrTail_groups_s3b.of_imp fun _ he => by subst he; exact htail).mono
      (by unfold FineScale; omega)
  | skipStep hlt _ ih =>
    intro hrem
    exact (ih (by omega)).mono (by unfold FineScale; omega)
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm _ hprog hcap_lt _ ih =>
    intro hrem
    have ih' := ih (by omega)
    have hbv : (BitVec.ofNat 64 (caps.get f)).toNat = caps.get f := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hv0 : v.length = 0
    · have hbm : bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs = [] := by
        simp [bytesMergeEventsCore, hm, hv0]
      have hle_cap : v.length ≤ caps.get f := by omega
      simp only [hle_cap, ↓reduceIte, spkCaps_set_get_s3b] at ih'
      rw [hbm, List.nil_append]
      exact ih'.mono (by unfold FineScale; omega)
    · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
      have hbm : bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs =
          rustAllocEvents v.length 1 ++
            doReserveClearEvents (caps.get f) v.length ++
            rustDeallocEvents v.length 1 := by
        simp [bytesMergeEventsCore, hm, hv0, hbv, List.append_assoc]
      have halloc := rustAlloc_linear_groups_s3b v.length hv_pos
      have hfree : PhaseGroupSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 :=
        (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ he => by
          subst he; exact FreeOnlyEvs.singleton 1 v.length
      by_cases hle_cap : v.length ≤ caps.get f
      · have hdrc : doReserveClearEvents (caps.get f) v.length = [] := by
          simp [doReserveClearEvents, hle_cap]
        simp only [hle_cap, ↓reduceIte, spkCaps_set_get_s3b] at ih'
        rw [hbm, hdrc, List.append_nil]
        have h1 := (s3_phaseGroupSpec_append_eq fineCostModel halloc hfree).mono
          (Nat.le_of_eq (Nat.add_zero _))
        exact (s3_phaseGroupSpec_append_eq fineCostModel h1 ih').mono (by unfold FineScale; omega)
      · have hlt_cap : caps.get f < v.length := by omega
        have hv_4900 : v.length ≤ 4900 := by omega
        simp only [hle_cap, ↓reduceIte] at ih'
        have hrank := spkCapsRank_set_lt_s3b f caps hlt_cap hv_4900
        rw [hbm]
        have h12 := s3_phaseGroupSpec_append_eq fineCostModel
          halloc (doReserveClear_groups_s3b (caps.get f) v.length)
        have h123 := (s3_phaseGroupSpec_append_eq fineCostModel h12 hfree).mono
          (Nat.le_of_eq (Nat.add_zero _))
        exact (s3_phaseGroupSpec_append_eq fineCostModel h123 ih').mono (by unfold FineScale; omega)

/-- Tight `PhaseGroupSpec` for `CliSpkDecodeEnv bs` (`bs.length ≤ L ≤ 4900`): each `bytesMerge`
step consumes at least `v.length + 1` input bytes (`≤ 3172 * (v.length + 1)` scaled units) with at
most `42` capacity doublings across `(pub, priv, sig)`. -/
private theorem cliSpkDecode_groups_s3b {bs : List (BitVec 8)} {L : Nat}
    (hbs : bs.length ≤ L) (hL : L ≤ 4900) :
    PhaseGroupSpec fineCostModel (CliSpkDecodeEnv bs) (3172 * L + 132 * FineScale) := by
  have hbs_4900 : bs.length ≤ 4900 := Nat.le_trans hbs hL
  have hloop : PhaseGroupSpec fineCostModel (SpkLoopBoundedEnv bs.length SpkCaps.zero)
      (3172 * bs.length + 132 * FineScale) := by
    have hex : PhaseGroupSpec fineCostModel
        (fun evs => ∃ e, SpkLoopBoundedEnv bs.length SpkCaps.zero e ∧ evs = e)
        (3172 * bs.length + (3 * spkCapsRank_s3b SpkCaps.zero + 6) * FineScale) :=
      s3_phaseGroupSpec_exists (P := SpkLoopBoundedEnv bs.length SpkCaps.zero)
        (E := fun e evs => evs = e) fun e he => spkLoopBounded_eq_groups_s3b he hbs_4900
    have hrank0 : spkCapsRank_s3b SpkCaps.zero = 42 := by decide
    rw [hrank0] at hex
    exact (hex.of_imp fun evs h => ⟨evs, h, rfl⟩).mono (by unfold FineScale; omega)
  have hseq : PhaseGroupSpec fineCostModel
      (SeqEnv (SpkLoopBoundedEnv bs.length SpkCaps.zero) FreeOnlyEvs)
      (3172 * L + 132 * FineScale) :=
    (hloop.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by unfold FineScale; omega)
  refine hseq.of_imp fun evs h => ?_
  rcases h with hL0 | hK
  · exact Or.inl hL0
  · rcases hK with hS | ⟨evs₁, evs₂, hS, hD, rfl⟩
    · rcases hS with hL0 | ⟨evsL, evsF, hL0, hF, rfl⟩
      · exact Or.inl hL0
      · exact Or.inr ⟨evsL, evsF, rfl, hL0, spkEpilogueFree_freeOnly_s3b hF⟩
    · rcases hS with hL0 | ⟨evsL, evsF, hL0, hF, rfl⟩
      · exact Or.inr ⟨evs₁, evs₂, rfl, hL0, dropDecodeError_freeOnly_s3b hD⟩
      · exact Or.inr ⟨evsL, evsF ++ evs₂, List.append_assoc _ _ _, hL0,
          FreeOnlyEvs.append (spkEpilogueFree_freeOnly_s3b hF) (dropDecodeError_freeOnly_s3b hD)⟩

private theorem cliPkDecode_groups_s3b {bs : List (BitVec 8)} (hbs : bs.length ≤ 125) :
    PhaseGroupSpec fineCostModel (CliPkDecodeEnv bs) (759 * FineScale) := by
  have hnf : NonFreeBound (CliPkDecodeEnv bs) 253 := by
    intro evs h
    have hclean : ∀ {e},
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv e →
          nonFreeCount e = 0 := by
      rintro e ⟨_, eD, ⟨e1, e2, h1, h2, rfl⟩, hD, rfl⟩
      have f1 : nonFreeCount e1 = 0 := by rcases h1 with rfl | ⟨_, _, _, rfl⟩ <;> rfl
      have f2 : nonFreeCount e2 = 0 := by rcases h2 with rfl | ⟨_, _, _, rfl⟩ <;> rfl
      have fD : nonFreeCount eD = 0 := by
        rcases hD with rfl | ⟨_, _, _, rfl⟩ <;>
          simp [nonFreeCount_append, nonFreeCount_rustDeallocEvents]
      simp [nonFreeCount_append, f1, f2, fD]
    rcases h with hL | (hL | ⟨evsL, evsC, hL, hC, rfl⟩)
    · have hc := s3_recordCodecLoop_nonFree hL; omega
    · have hc := s3_recordCodecLoop_nonFree hL; omega
    · rw [nonFreeCount_append, hclean hC]
      have hc := s3_recordCodecLoop_nonFree hL; omega
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private def EntriesFromNormS3b (files : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, Arm64.normalizePath p = k ∧ (p, bs) ∈ files

private theorem entriesFromNorm_empty_s3b (files : List (String × List (BitVec 8))) :
    EntriesFromNormS3b files ({} : Arm64.FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem entriesFromNorm_setEntry_dir_s3b {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : EntriesFromNormS3b files fs) (pref : Arm64.FsPath) :
    EntriesFromNormS3b files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromNorm_foldl_dirs_s3b {files : List (String × List (BitVec 8))}
    (prefs : List Arm64.FsPath) {fs : Arm64.FsState} (h : EntriesFromNormS3b files fs) :
    EntriesFromNormS3b files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_setEntry_dir_s3b h hd)

private theorem entriesFromNorm_foldl_outer_dirs_s3b {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : Arm64.FsState} (h : EntriesFromNormS3b files fs) :
    EntriesFromNormS3b files
      (dirs.foldl
        (fun acc d => (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_foldl_dirs_s3b _ h)

private theorem entriesFromNorm_setFile_s3b {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : EntriesFromNormS3b files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFromNormS3b files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold Arm64.FsState.setFile Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i heq
    have hk_eq : Arm64.normalizePath p = k := (beq_iff_eq.mp heq).symm
    injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, hk_eq, hmem⟩
  · exact h k bs' hk

private theorem entriesFromNorm_foldl_files_s3b {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : Arm64.FsState} (h : EntriesFromNormS3b allFiles fs) :
    EntriesFromNormS3b allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc :=
            ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
              (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFromNorm_foldl_dirs_s3b
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast) h
    have hset := entriesFromNorm_setFile_s3b hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem initFsState_files_mem_norm_s3b {inputs : Arm64.Process.ProcessInputs} {q : String}
    {bs : List (BitVec 8)}
    (h : (Arm64.Process.initFsState inputs).files q = some (.file bs)) :
    ∃ p, Arm64.normalizePath p = Arm64.normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := entriesFromNorm_foldl_outer_dirs_s3b inputs.dirs (entriesFromNorm_empty_s3b inputs.files)
  have hf := entriesFromNorm_foldl_files_s3b inputs.files (fun _ hx => hx) hd
  unfold Arm64.FsState.files Arm64.FsState.getEntry at h
  split at h
  · cases h
  · exact hf (Arm64.normalizePath q) bs h

private theorem splitSlash_go_append_slash_s3b (cur a b : List Char) :
    Arm64.splitSlash.go cur (a ++ ('/' :: b)) =
      Arm64.splitSlash.go cur a ++ Arm64.splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, Arm64.splitSlash.go, ih []]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        Arm64.splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem normalizePath_append_slash_s3b (a b : String) :
    Arm64.normalizePath (a ++ "/" ++ b) = Arm64.normalizePath a ++ Arm64.normalizePath b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [htl, splitSlash_go_append_slash_s3b [] a.toList b.toList, List.filter_append]

private def kutf8_s3b (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem utf8_eq_kutf8_s3b (s : String) : utf8 s = kutf8_s3b s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8_s3b, List.utf8Encode, s3_byteArray_toList_eq_data]

private theorem cliIo_rd_eq_ok_nil_or_files_some_s3b {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
        (CryptoVerification.SignalSession.Cli.MainHops.pathStr path) = some (.file bs) := by
  change CryptoVerification.SignalSession.Cli.MainHops.cliRd
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files path =
        .ok bs at hrd
  unfold CryptoVerification.SignalSession.Cli.MainHops.cliRd at hrd; split at hrd
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

private theorem pathStr_append_s3b (a b : List (BitVec 8)) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (a ++ b) =
      CryptoVerification.SignalSession.Cli.MainHops.pathStr a ++
        CryptoVerification.SignalSession.Cli.MainHops.pathStr b := by
  unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
  rw [List.map_append, ← String.ofList_append]

private theorem utf8EncodeChar_ascii_s3b {c : Char} (hc : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  have hle : c.val.toNat ≤ 127 := by change c.toNat ≤ 127; omega
  simp only [hle, ↓reduceIte]
  rfl

private theorem pathStr_utf8_ascii_list_s3b :
    ∀ (cs : List Char), (∀ c ∈ cs, c.toNat < 128) →
      ((cs.flatMap String.utf8EncodeChar).map fun b =>
        Char.ofNat (BitVec.ofNat 8 b.toNat).toNat) = cs
  | [], _ => rfl
  | c :: cs, hasc => by
    have hc : c.toNat < 128 := hasc c (List.mem_cons_self ..)
    have ih := pathStr_utf8_ascii_list_s3b cs (fun x hx => hasc x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, utf8EncodeChar_ascii_s3b hc, List.singleton_append,
      List.map_cons]
    have hu8 : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hbv : (BitVec.ofNat 8 (UInt8.ofNat c.toNat).toNat).toNat = c.toNat := by
      rw [hu8, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [hbv, Char.ofNat_toNat, ih]

private theorem pathStr_utf8_ascii_s3b {s : String} (hasc : ∀ c ∈ s.toList, c.toNat < 128) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 s) = s := by
  unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
  rw [utf8_eq_kutf8_s3b]
  unfold kutf8_s3b
  rw [List.map_map]
  have hmap := pathStr_utf8_ascii_list_s3b s.toList hasc
  exact Eq.trans (congrArg String.ofList hmap) String.ofList_toList

private theorem splitSlash_go_no_slash_s3b :
    ∀ (cur cs : List Char),
      '/' ∉ cs →
        Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | cur, [], _ => by simp [Arm64.splitSlash.go]
  | cur, c :: cs, hns => by
    have hc : c ≠ '/' := fun heq => hns (heq ▸ List.mem_cons_self ..)
    have hns' : '/' ∉ cs := fun hm => hns (List.mem_cons_of_mem _ hm)
    rw [Arm64.splitSlash.go.eq_3 cur c cs hc, splitSlash_go_no_slash_s3b (c :: cur) cs hns']
    simp [List.reverse_cons, List.append_assoc]

private theorem normalizePath_single_s3b {s : String} (hslash : '/' ∉ s.toList)
    (hne : s.isEmpty = false) (hdot : (s != ".") = true) :
    Arm64.normalizePath s = [s] := by
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [splitSlash_go_no_slash_s3b [] s.toList hslash]
  simp [String.ofList_toList, hne, hdot]

private theorem splitSlash_go_suffix_no_slash_s3b (cs : List Char) (hcs : '/' ∉ cs) :
    ∀ (cur a : List Char), ∃ init u,
      Arm64.splitSlash.go cur (a ++ cs) = init ++ [String.ofList (u ++ cs)]
  | cur, [] => ⟨[], cur.reverse, by simp only [List.nil_append, splitSlash_go_no_slash_s3b cur cs hcs]⟩
  | cur, c :: tl => by
    by_cases hc : c = '/'
    · subst hc
      obtain ⟨init, u, ih⟩ := splitSlash_go_suffix_no_slash_s3b cs hcs [] tl
      refine ⟨String.ofList cur.reverse :: init, u, ?_⟩
      simp only [List.cons_append, Arm64.splitSlash.go, ih]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (tl ++ cs) hc]
      exact splitSlash_go_suffix_no_slash_s3b cs hcs (c :: cur) tl

private theorem normalizePath_baseKeysFile_shape_s3b (j : BitVec 32) :
    ∃ (mid : List String) (lastSeg : String),
      Arm64.normalizePath (CryptoVerification.SignalSession.baseKeysFile j) =
        "last-resort-kyber-pre-keys" :: (mid ++ [lastSeg]) ∧
      '.' ∈ lastSeg.toList := by
  have heq : CryptoVerification.SignalSession.baseKeysFile j =
      ("last-resort-kyber-pre-keys" ++ "/") ++ (toString j.toNat ++ ".base-keys") := by
    unfold CryptoVerification.SignalSession.baseKeysFile
    exact String.ext (by simp [String.toList_append])
  rw [heq, normalizePath_append_slash_s3b]
  have h1 : Arm64.normalizePath "last-resort-kyber-pre-keys" = ["last-resort-kyber-pre-keys"] := by
    decide
  have hno_slash : '/' ∉ (".base-keys" : String).toList := by decide
  obtain ⟨init, u, hsp⟩ :=
    splitSlash_go_suffix_no_slash_s3b (".base-keys" : String).toList hno_slash
      [] (toString j.toNat).toList
  let lastSeg := String.ofList (u ++ (".base-keys" : String).toList)
  have hlen : 10 ≤ lastSeg.toList.length := by
    dsimp only [lastSeg]
    rw [String.toList_ofList, List.length_append]
    have h10 : (".base-keys" : String).toList.length = 10 := by decide
    omega
  have hne : lastSeg.isEmpty = false := by
    cases hb : lastSeg.isEmpty
    · rfl
    · have h0 : lastSeg = "" := String.isEmpty_iff.mp hb
      rw [h0] at hlen
      contradiction
  have hndot : (lastSeg != ".") = true := by
    rw [bne_iff_ne]
    intro hd
    rw [hd] at hlen
    contradiction
  have hnorm2 : Arm64.normalizePath (toString j.toNat ++ ".base-keys") =
      init.filter (fun seg => !seg.isEmpty && seg != ".") ++ [lastSeg] := by
    unfold Arm64.normalizePath Arm64.splitSlash
    rw [String.toList_append, hsp, List.filter_append]
    change init.filter (fun seg => !seg.isEmpty && seg != ".") ++
        List.filter (fun seg => !seg.isEmpty && seg != ".") [lastSeg] =
      init.filter (fun seg => !seg.isEmpty && seg != ".") ++ [lastSeg]
    simp only [List.filter, hne, Bool.not_false, hndot, Bool.true_and]
  have hdot_in : '.' ∈ lastSeg.toList := by
    dsimp only [lastSeg]
    rw [String.toList_ofList, List.mem_append]
    exact Or.inr (by decide)
  refine ⟨init.filter (fun seg => !seg.isEmpty && seg != "."), lastSeg, ?_, hdot_in⟩
  rw [h1, hnorm2, List.singleton_append]

private theorem digit_char_ne_slash_dot_s3b :
    ∀ d : Nat, d < 10 →
      Char.ofNat (BitVec.ofNat 8 (0x30 + d)).toNat ≠ '/' ∧
      Char.ofNat (BitVec.ofNat 8 (0x30 + d)).toNat ≠ '.' := by
  intro d hd
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
                     d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem decimalText_digits_s3b :
    ∀ n : Nat, decimalText n ≠ [] ∧
      ∀ b ∈ decimalText n, ∃ d < 10, b = BitVec.ofNat 8 (0x30 + d) := by
  intro n
  refine Nat.strongRecOn n fun m ih => ?_
  by_cases hm : m < 10
  · rw [decimalText_digit m hm]
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    intro b hb
    rw [List.mem_singleton] at hb
    exact ⟨m, hm, hb⟩
  · have hge : 10 ≤ m := by omega
    rw [decimalText_ge10 m hge]
    obtain ⟨hne, hdig⟩ := ih (m / 10) (by omega)
    refine ⟨by simp [hne], ?_⟩
    intro b hb
    rw [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb1 | rfl
    · exact hdig b hb1
    · exact ⟨m % 10, by omega, rfl⟩

private theorem keyName_pathStr_props_s3b (k : BitVec 32) :
    let s := CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)
    '/' ∉ s.toList ∧ '.' ∉ s.toList ∧ s.isEmpty = false ∧ (s != ".") = true := by
  dsimp only
  obtain ⟨hne, hdig⟩ := decimalText_digits_s3b k.toNat
  have htl : (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).toList =
      (decimalText k.toNat).map (fun b => Char.ofNat b.toNat) := by
    unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr keyName
    rw [String.toList_ofList]
  have hslash : '/' ∉ (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).toList := by
    rw [htl, List.mem_map]
    rintro ⟨b, hb, hch⟩
    obtain ⟨d, hd, rfl⟩ := hdig b hb
    exact (digit_char_ne_slash_dot_s3b d hd).1 hch
  have hdot : '.' ∉ (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).toList := by
    rw [htl, List.mem_map]
    rintro ⟨b, hb, hch⟩
    obtain ⟨d, hd, rfl⟩ := hdig b hb
    exact (digit_char_ne_slash_dot_s3b d hd).2 hch
  have hne_str : (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).isEmpty = false := by
    cases hb : (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).isEmpty
    · rfl
    · have h0 : (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).toList = [] := by
        rw [String.isEmpty_iff.mp hb]
        rfl
      rw [htl, List.map_eq_nil_iff] at h0
      exact False.elim (hne h0)
  have hdot_ne : (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k) != ".") = true := by
    rw [bne_iff_ne]
    intro hd
    have hdot_in : '.' ∈ (CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName k)).toList := by
      rw [hd]
      decide
    exact hdot hdot_in
  exact ⟨hslash, hdot, hne_str, hdot_ne⟩

private theorem encodeProto3Uint32Field_len_le_20_s3b (tag : Nat) (_htag : tag ≤ 15) (v : BitVec 32) :
    (CryptoVerification.RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Uint32Field
    CryptoVerification.LibsignalProtoCodec.encodeUint32Field
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk : (CryptoVerification.LibsignalProtoCodec.encodeKey tag .varint).length ≤ 10 := by
      unfold CryptoVerification.LibsignalProtoCodec.encodeKey
      exact (CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_length_bounds _).2
    have hv := (CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_length_bounds (v.zeroExtend 64)).2
    omega

private theorem encodeProto3Fixed64Field_len_le_18_s3b (tag : Nat) (v : BitVec 64) :
    (CryptoVerification.RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Fixed64Field
    CryptoVerification.RecordCodecs.le64Bytes
  split_ifs
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hk : (CryptoVerification.LibsignalProtoCodec.encodeKey tag .sixtyFourBit).length ≤ 10 := by
      unfold CryptoVerification.LibsignalProtoCodec.encodeKey
      exact (CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_length_bounds _).2
    omega

private theorem encodeProto3BytesField_len_le_s3b (tag : Nat) (v : List (BitVec 8)) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk : (CryptoVerification.LibsignalProtoCodec.encodeKey tag .lengthDelimited).length ≤ 10 := by
      unfold CryptoVerification.LibsignalProtoCodec.encodeKey
      exact (CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_length_bounds _).2
    have hv := (CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_length_bounds
      (BitVec.ofNat 64 v.length)).2
    omega

private theorem ikp_encode_len_le_105_s3b
    (P : PEParams) (st : CryptoVerification.SignalSession.PqParty) :
    (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
        st.me.idPriv.toList⟩).length ≤ 105 := by
  unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3BytesField_len_le_s3b 1
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes)
  have h2 := encodeProto3BytesField_len_le_s3b 2 st.me.idPriv.toList
  have hdjb : (CryptoVerification.E2E.djbKey
    (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : st.me.idPriv.toList.length = 32 := st.me.idPriv.toList_length
  omega

private theorem signedRecordBytes_len_le_230_s3b (P : PEParams) (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqSignedKey) :
    (CryptoVerification.SignalSession.signedRecordBytes P.C id k).length ≤ 230 := by
  unfold CryptoVerification.SignalSession.signedRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_len_le_20_s3b 1 (by decide) id
  have h2 := encodeProto3BytesField_len_le_s3b 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes)
  have h3 := encodeProto3BytesField_len_le_s3b 3 k.priv.toList
  have h4 := encodeProto3BytesField_len_le_s3b 4 k.sig.toList
  have h5 := encodeProto3Fixed64Field_len_le_18_s3b 5 k.timestamp
  have hdjb : (CryptoVerification.E2E.djbKey
    (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : k.priv.toList.length = 32 := k.priv.toList_length
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem oneTimeRecordBytes_len_le_125_s3b (P : PEParams) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (CryptoVerification.SignalSession.oneTimeRecordBytes P.C id sk).length ≤ 125 := by
  unfold CryptoVerification.SignalSession.oneTimeRecordBytes
    CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_len_le_20_s3b 1 (by decide) id
  have h2 := encodeProto3BytesField_len_le_s3b 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes)
  have h3 := encodeProto3BytesField_len_le_s3b 3 sk.toList
  have hdjb : (CryptoVerification.E2E.djbKey
    (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : sk.toList.length = 32 := sk.toList_length
  omega

private theorem kyberRecordBytes_len_le_4900_s3b (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqKyberKey) :
    (CryptoVerification.SignalSession.kyberRecordBytes id k).length ≤ 4900 := by
  unfold CryptoVerification.SignalSession.kyberRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3Uint32Field_len_le_20_s3b 1 (by decide) id
  have h2 := encodeProto3BytesField_len_le_s3b 2 (CryptoVerification.E2E.kyberKey k.pub)
  have h3 := encodeProto3BytesField_len_le_s3b 3 (0x08#8 :: k.sec.toList)
  have h4 := encodeProto3BytesField_len_le_s3b 4 k.sig.toList
  have h5 := encodeProto3Fixed64Field_len_le_18_s3b 5 k.timestamp
  have hpub : (CryptoVerification.E2E.kyberKey k.pub).length = 1569 := by
    simp [CryptoVerification.E2E.kyberKey]
  have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem norm_slash_prefix_s3b {dir dirSlash sub : String}
    (htl : dirSlash.toList = dir.toList ++ ['/'])
    (hdir : Arm64.normalizePath dir = [dir]) :
    Arm64.normalizePath (dirSlash ++ sub) = dir :: Arm64.normalizePath sub := by
  have heq : dirSlash ++ sub = (dir ++ "/") ++ sub :=
    String.ext (by simp [String.toList_append, htl])
  rw [heq, normalizePath_append_slash_s3b dir sub, hdir, List.singleton_append]

private theorem bundle_norm_not_store_s3b {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p : String} {bs : List (BitVec 8)} {tgt : List String}
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir)
    (htgt : tgt.head? = some "identity-key-pair" ∨
            tgt.head? = some "signed-pre-keys" ∨
            tgt.head? = some "one-time-pre-keys" ∨
            tgt.head? = some "one-time-kyber-pre-keys" ∨
            tgt.head? = some "last-resort-kyber-pre-keys") :
    Arm64.normalizePath p ≠ tgt := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf
    CryptoVerification.SignalSession.bundleDir at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _
    have hp' : p = "bundle/identity-key" := hp.trans (String.ext (by decide))
    subst hp'; intro heq; rw [← heq] at htgt; revert htgt; decide
  · injection h with hp _
    have hp' : p = "bundle/registration-id" := hp.trans (String.ext (by decide))
    subst hp'; intro heq; rw [← heq] at htgt; revert htgt; decide
  · injection h with hp _
    have hp' : p = "bundle/signed-pre-key" := hp.trans (String.ext (by decide))
    subst hp'; intro heq; rw [← heq] at htgt; revert htgt; decide
  · injection h with hp _
    have hp' : p = "bundle/kyber-pre-key" := hp.trans (String.ext (by decide))
    subst hp'; intro heq; rw [← heq] at htgt; revert htgt; decide
  · cases hbo : b.opk with
    | none => simp [hbo] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hbo, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _
      have hp' : p = "bundle/one-time-pre-key" := hp.trans (String.ext (by decide))
      subst hp'; intro heq; rw [← heq] at htgt; revert htgt; decide

private theorem pqInputs_file_from_encodeDir_s3b {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {tgt : List String} {bs : List (BitVec 8)}
    (htgt : tgt.head? = some "identity-key-pair" ∨
            tgt.head? = some "signed-pre-keys" ∨
            tgt.head? = some "one-time-pre-keys" ∨
            tgt.head? = some "one-time-kyber-pre-keys" ∨
            tgt.head? = some "last-resort-kyber-pre-keys")
    (hfile : ∃ p, Arm64.normalizePath p = tgt ∧ (p, bs) ∈ i.files) :
    ∃ st p, Arm64.normalizePath p = tgt ∧ (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st := by
  obtain ⟨p, hp_norm, hp_files⟩ := hfile
  obtain ⟨st, _, hcase⟩ := hi
  have hcoins_ne : Arm64.normalizePath CryptoVerification.SignalSession.coinsFile ≠ tgt := by
    unfold CryptoVerification.SignalSession.coinsFile
    intro heq; rw [← heq] at htgt
    have hc : (Arm64.normalizePath "coins").head? = some "coins" := by decide
    rw [hc] at htgt; revert htgt; decide
  rcases hcase with ⟨_, b, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
  · simp only [CryptoVerification.SignalSession.pqInitInputs,
      CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
    rcases hp_files with (hed | hbun) | hcoins
    · exact ⟨st, p, hp_norm, hed⟩
    · exact False.elim (bundle_norm_not_store_s3b hbun htgt hp_norm)
    · injection hcoins with hp_c _; subst hp_c; exact False.elim (hcoins_ne hp_norm)
  · simp only [CryptoVerification.SignalSession.pqSendInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hp_norm, hed⟩
    · injection hcoins with hp_c _; subst hp_c; exact False.elim (hcoins_ne hp_norm)
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hp_norm, hed⟩
    · injection hcoins with hp_c _; subst hp_c; exact False.elim (hcoins_ne hp_norm)
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hp_norm, hed⟩
    · injection hcoins with hp_c _; subst hp_c; exact False.elim (hcoins_ne hp_norm)
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hp_norm, hed⟩
    · injection hcoins with hp_c _; subst hp_c; exact False.elim (hcoins_ne hp_norm)

private theorem store_keyName_norm_s3b {dirStr : String}
    (hdir_asc : ∀ c ∈ dirStr.toList, c.toNat < 128)
    (hdir_ne : utf8 dirStr ≠ [])
    (hdir_norm : Arm64.normalizePath dirStr = [dirStr])
    (id : BitVec 32) :
    Arm64.normalizePath
      (CryptoVerification.SignalSession.Cli.MainHops.pathStr
        (pathOf (utf8 dirStr) (keyName id))) =
          [dirStr, CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id)] := by
  unfold pathOf
  simp only [hdir_ne, ↓reduceIte]
  rw [List.append_assoc, pathStr_append_s3b, pathStr_append_s3b]
  have h1 := pathStr_utf8_ascii_s3b hdir_asc
  have h2 : CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "/") = "/" :=
    pathStr_utf8_ascii_s3b (by decide)
  obtain ⟨hslash, _, hne, hdot⟩ := keyName_pathStr_props_s3b id
  rw [h1, h2, ← String.append_assoc, normalizePath_append_slash_s3b, hdir_norm,
    normalizePath_single_s3b hslash hne hdot]
  rfl

private theorem cons_ne_of_head_ne_s3b {a b : String} {xs ys : List String} (hne : a ≠ b) :
    a :: xs ≠ b :: ys := fun h => hne (List.cons.inj h).1

private theorem head_cons_ne_s3b {a b : String} {xs : List String} (hne : a ≠ b) :
    (a :: xs).head? ≠ some b := fun h => hne (Option.some.inj h)

private theorem encodeDir_head_disjoint_s3b {P : PEParams}
    {st : CryptoVerification.SignalSession.PqParty} {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st) :
    ((Arm64.normalizePath p = ["identity-key-pair"] → bs.length ≤ 105) ∧
     ((Arm64.normalizePath p).head? = some "signed-pre-keys" → bs.length ≤ 230) ∧
     ((Arm64.normalizePath p).head? = some "one-time-pre-keys" → bs.length ≤ 125) ∧
     ((Arm64.normalizePath p).head? = some "one-time-kyber-pre-keys" → bs.length ≤ 4900) ∧
     (∀ id : BitVec 32,
       Arm64.normalizePath p =
         ["last-resort-kyber-pre-keys",
          CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id)] →
         bs.length ≤ 4900)) := by
  unfold CryptoVerification.SignalSession.encodeDir
    CryptoVerification.SignalSession.addressFile
    CryptoVerification.SignalSession.identityKeyPairFile
    CryptoVerification.SignalSession.registrationIdFile
    CryptoVerification.SignalSession.identityFile
    CryptoVerification.SignalSession.sessionFile
    CryptoVerification.SignalSession.signedPreKeyFile
    CryptoVerification.SignalSession.oneTimePreKeyFile
    CryptoVerification.SignalSession.oneTimeKyberPreKeyFile
    CryptoVerification.SignalSession.lastResortKyberPreKeyFile at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp
      have hn : Arm64.normalizePath "address" = ["address"] := by decide
      rw [hn]
      exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
    · injection h with hp hbs; subst hp hbs
      have hn : Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
      rw [hn]
      exact ⟨fun _ => ikp_encode_len_le_105_s3b P st,
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
    · injection h with hp _; subst hp
      have hn : Arm64.normalizePath "registration-id" = ["registration-id"] := by decide
      rw [hn]
      exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      rw [norm_slash_prefix_s3b (dir := "identities") (by decide) (by decide)]
      exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      rw [norm_slash_prefix_s3b (dir := "sessions") (by decide) (by decide)]
      exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨id', k⟩, _, h⟩
    injection h with hp_eq hbs; subst hp_eq hbs
    rw [norm_slash_prefix_s3b (dir := "signed-pre-keys") (by decide) (by decide)]
    exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
      fun _ => signedRecordBytes_len_le_230_s3b P id' k,
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨id', opt⟩, _, h⟩
    injection h with hp_eq hbs; subst hp_eq hbs
    rw [norm_slash_prefix_s3b (dir := "one-time-pre-keys") (by decide) (by decide)]
    refine ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun _ => ?_,
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
    cases opt with
    | none => simp
    | some sk => exact oneTimeRecordBytes_len_le_125_s3b P id' sk
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨id', opt⟩, _, h⟩
    injection h with hp_eq hbs; subst hp_eq hbs
    rw [norm_slash_prefix_s3b (dir := "one-time-kyber-pre-keys") (by decide) (by decide)]
    refine ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun h => absurd h (head_cons_ne_s3b (by decide)),
      fun _ => ?_,
      fun _ h => absurd h (cons_ne_of_head_ne_s3b (by decide))⟩
    cases opt with
    | none => simp
    | some k => exact kyberRecordBytes_len_le_4900_s3b id' k
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨id', k, seen⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq hbs; subst hp_eq hbs
      rw [norm_slash_prefix_s3b (dir := "last-resort-kyber-pre-keys") (by decide) (by decide)]
      exact ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun _ _ => kyberRecordBytes_len_le_4900_s3b id' k⟩
    · injection h2 with hp_eq _; subst hp_eq
      obtain ⟨mid, lastSeg, hbk, hdot_in⟩ := normalizePath_baseKeysFile_shape_s3b id'
      rw [hbk]
      refine ⟨fun h => absurd h (cons_ne_of_head_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun h => absurd h (head_cons_ne_s3b (by decide)),
        fun id heq => ?_⟩
      injection heq with _ htail
      have hmem_last : lastSeg ∈ mid ++ [lastSeg] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      rw [htail, List.mem_singleton] at hmem_last
      subst hmem_last
      exact False.elim ((keyName_pathStr_props_s3b id).2.1 hdot_in)

/-- Per-directory byte caps on `runFiles i` under `CliPqxdhInputs P i` (`'.' ∉ keyName k`,
excluding `.base-keys`). -/
private theorem pqInputs_store_file_caps_s3b {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    (∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) ∧
    (∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230) ∧
    (∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro bs hrd
    change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some_s3b hrd with rfl | hfile
    · exact Nat.zero_le _
    · have hpth : CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
            "identity-key-pair" :=
        pathStr_utf8_ascii_s3b (s := "identity-key-pair") (by decide)
      rw [hpth] at hfile
      obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s3b hfile
      rw [show Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] by decide] at hp_norm
      obtain ⟨st, p', hp'_norm, hp'_ed⟩ := pqInputs_file_from_encodeDir_s3b hi
        (Or.inl rfl) ⟨p, hp_norm, hp_mem⟩
      exact (encodeDir_head_disjoint_s3b hp'_ed).1 hp'_norm
  · intro id bs hrd
    change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.signed.path (keyName id)) = .ok bs at hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some_s3b hrd with rfl | hfile
    · exact Nat.zero_le _
    · obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s3b hfile
      have hkn := store_keyName_norm_s3b (dirStr := "signed-pre-keys")
        (by decide) (by rw [utf8_eq_kutf8_s3b]; decide) (by decide) id
      change Arm64.normalizePath (CryptoVerification.SignalSession.Cli.MainHops.pathStr
        (pathOf StoresGhost.opened.signed.path (keyName id))) = _ at hkn
      rw [hkn] at hp_norm
      obtain ⟨st, p', hp'_norm, hp'_ed⟩ := pqInputs_file_from_encodeDir_s3b hi
        (Or.inr (Or.inl rfl)) ⟨p, hp_norm, hp_mem⟩
      exact (encodeDir_head_disjoint_s3b hp'_ed).2.1 (by rw [hp'_norm]; rfl)
  · intro id bs hrd
    change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.oneTime.path (keyName id)) = .ok bs at hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some_s3b hrd with rfl | hfile
    · exact Nat.zero_le _
    · obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s3b hfile
      have hkn := store_keyName_norm_s3b (dirStr := "one-time-pre-keys")
        (by decide) (by rw [utf8_eq_kutf8_s3b]; decide) (by decide) id
      change Arm64.normalizePath (CryptoVerification.SignalSession.Cli.MainHops.pathStr
        (pathOf StoresGhost.opened.oneTime.path (keyName id))) = _ at hkn
      rw [hkn] at hp_norm
      obtain ⟨st, p', hp'_norm, hp'_ed⟩ := pqInputs_file_from_encodeDir_s3b hi
        (Or.inr (Or.inr (Or.inl rfl))) ⟨p, hp_norm, hp_mem⟩
      exact (encodeDir_head_disjoint_s3b hp'_ed).2.2.1 (by rw [hp'_norm]; rfl)
  · intro id bs hrd
    change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.kyber.oneTime.path (keyName id)) = .ok bs at hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some_s3b hrd with rfl | hfile
    · exact Nat.zero_le _
    · obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s3b hfile
      have hkn := store_keyName_norm_s3b (dirStr := "one-time-kyber-pre-keys")
        (by decide) (by rw [utf8_eq_kutf8_s3b]; decide) (by decide) id
      change Arm64.normalizePath (CryptoVerification.SignalSession.Cli.MainHops.pathStr
        (pathOf StoresGhost.opened.kyber.oneTime.path (keyName id))) = _ at hkn
      rw [hkn] at hp_norm
      obtain ⟨st, p', hp'_norm, hp'_ed⟩ := pqInputs_file_from_encodeDir_s3b hi
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ⟨p, hp_norm, hp_mem⟩
      exact (encodeDir_head_disjoint_s3b hp'_ed).2.2.2.1 (by rw [hp'_norm]; rfl)
  · intro id bs hrd
    change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.kyber.lastResort.path (keyName id)) = .ok bs at hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some_s3b hrd with rfl | hfile
    · exact Nat.zero_le _
    · obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s3b hfile
      have hkn := store_keyName_norm_s3b (dirStr := "last-resort-kyber-pre-keys")
        (by decide) (by rw [utf8_eq_kutf8_s3b]; decide) (by decide) id
      change Arm64.normalizePath (CryptoVerification.SignalSession.Cli.MainHops.pathStr
        (pathOf StoresGhost.opened.kyber.lastResort.path (keyName id))) = _ at hkn
      rw [hkn] at hp_norm
      obtain ⟨st, p', hp'_norm, hp'_ed⟩ := pqInputs_file_from_encodeDir_s3b hi
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ⟨p, hp_norm, hp_mem⟩
      exact (encodeDir_head_disjoint_s3b hp'_ed).2.2.2.2 id hp'_norm

private theorem freeOnly_nonFree_zero_s3b {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    nonFreeCount evs = 0 := by
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    obtain ⟨al, sz, hev⟩ := h ev (List.mem_cons_self ..)
    subst hev
    rw [show AllocEvent.free al sz :: tl = rustDeallocEvents sz al ++ tl from rfl,
      nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.zero_add]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

private theorem kpkMarkStepFixed_groups_s3b (rd : ReadRule) (files : FsFiles)
    (kpkId spkId : BitVec 32) (baseKey : PublicKey) :
    PhaseGroupSpec fineCostModel (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey)
      (16659 + 159 * FineScale) := by
  unfold W4BinaryKpkMarkStepEnvFixed CliKpkMarkPollEnv
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  have hdec := decimal_groups_s3b kpkId
  have hgetOt := s3_dirGetFixed_groups fineCostModel rd files
    StoresGhost.opened.kyber.oneTime (keyName kpkId)
  have hpre : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkOneTimePreAfterGetEnv
        DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) files
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)
      (72 * FineScale) :=
    (hdec.seq hgetOt).mono (by omega)
  have htail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkOneTimeTailEnv
        rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) DirPutEnv files
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
        (StoresGhost.opened.kyber.oneTime.get rd files (keyName kpkId)))
      (87 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkOneTimeTailEnv
    cases StoresGhost.opened.kyber.oneTime.get rd files (keyName kpkId) with
    | error _ => exact hf.mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | cons b rest =>
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkOneTimeConsTailEnv
        have hput := s3_dirPut_opened_groups fineCostModel
          (dir := StoresGhost.opened.kyber.oneTime) rfl (keyName kpkId) []
        exact (hf.seq (hdec.seq hput)).mono (by omega)
      | nil =>
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkLastResortPreAfterGetEnv
        have hres : PhaseGroupSpec fineCostModel
            (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkBaseKeysReserveEnv kpkId)
            (3 * FineScale) := by
          have hnf : NonFreeBound
              (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkBaseKeysReserveEnv kpkId)
              1 := by
            intro evs hr
            have hdr : ∀ (x : DoReserveCall),
                nonFreeCount (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents x) ≤ 1 := by
              intro x; unfold LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents
              split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · simp [nonFreeCount_nil]
            all_goals exact hdr _
          exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
        have hgetLr := s3_dirGetFixed_groups fineCostModel rd files
          StoresGhost.opened.kyber.lastResort (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)
        have hlrPre := (hdec.seq (hres.seq hgetLr)).mono (show 30 * FineScale + (3 * FineScale + 42 * FineScale) ≤ 75 * FineScale by omega)
        have hlrTail : PhaseGroupSpec fineCostModel
            (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkLastResortTailEnv
              DirPutEnv ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
              (StoresGhost.opened.kyber.lastResort.get rd files
                (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)))
            (12 * FineScale) := by
          unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkLastResortTailEnv
          cases StoresGhost.opened.kyber.lastResort.get rd files
            (CryptoVerification.SignalSession.Cli.baseKeysName kpkId) with
          | error _ => exact hf.mono (Nat.zero_le _)
          | ok seenBs =>
            have hpreEv : PhaseGroupSpec fineCostModel
                (· = LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.kpkAfterLrGetPreEvents)
                (6 * FineScale) := by
              have hnf : NonFreeBound
                  (· = LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.kpkAfterLrGetPreEvents)
                  2 := by
                intro evs he; subst he; decide
              exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
            have hbr : PhaseGroupSpec fineCostModel
                (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkAfterLrGetCapFreeBranchEnv
                  DirPutEnv ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩ seenBs)
                (6 * FineScale) := by
              unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkAfterLrGetCapFreeBranchEnv
              split_ifs
              · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel 15 1).seq hf).mono (by omega)
              · have hmid : PhaseGroupSpec fineCostModel
                    (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkSeenAppendReserveMidEnv seenBs)
                    (3 * FineScale) := by
                  have hnf : NonFreeBound
                      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkSeenAppendReserveMidEnv seenBs)
                      1 := by
                    intro evs hm
                    cases hm with
                    | fast _ hfo => exact Nat.le_trans (freeOnly_nonFree_zero_s3b hfo).le (by decide)
                    | grow spare _ =>
                      rw [nonFreeCount_append]
                      have h1 : nonFreeCount
                          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.kpkSeenAppendReserveEventsAt seenBs spare) ≤ 1 := by
                        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.kpkSeenAppendReserveEventsAt
                          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents
                        split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
                      have h2 : nonFreeCount
                          (LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.optDeallocBufEvents 37#64) = 0 := by
                        decide
                      omega
                  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
                have hputLr := s3_dirPut_opened_groups fineCostModel
                  (dir := StoresGhost.opened.kyber.lastResort) rfl
                  (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)
                  (seenBs ++ CryptoVerification.SignalSession.Cli.baseKeyEntry spkId baseKey)
                exact (hmid.seq hputLr).mono (by omega)
              · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq hf).mono (by omega)
            exact (hpreEv.seq hbr).mono (by omega)
        exact (hf.seq (hlrPre.seq hlrTail)).mono (by omega)
  exact (w4BoxedStoreStep_le_44_fine_groupSpec (by decide) (hpre.seq htail)).mono (by omega)

private theorem pinFreeEvents_freeOnlyAlign16_s3b (pin : VecPin) :
    FreeOnlyAlign16Evs (pinFreeEvents pin) := by
  unfold pinFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) pin.cap.toNat

private theorem sgnCapFreeEvents_freeOnlyAlign16_s3b (cap : BitVec 64) :
    FreeOnlyAlign16Evs (sgnCapFreeEvents cap) := by
  unfold sgnCapFreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) cap.toNat

private theorem vec104FreeEvents_freeOnlyAlign16_s3b (cap : BitVec 64) :
    FreeOnlyAlign16Evs (vec104FreeEvents cap) := by
  unfold vec104FreeEvents; split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) (cap.toNat * 104)

private theorem mkFreeEvents_freeOnlyAlign16_s3b (mk : MessageKeyGhost) :
    FreeOnlyAlign16Evs (mkFreeEvents mk) := by
  unfold mkFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16_s3b mk.cipher)
        (pinFreeEvents_freeOnlyAlign16_s3b mk.mac))
      (pinFreeEvents_freeOnlyAlign16_s3b mk.iv))
    (pinFreeEvents_freeOnlyAlign16_s3b mk.seed)

private theorem mkListFreeEvents_freeOnlyAlign16_s3b
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (mks.flatMap fun gk => mkFreeEvents gk.1) := by
  induction mks with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gk tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact mkFreeEvents_freeOnlyAlign16_s3b gk.1 ev h1
    · exact ih ev h2

private theorem dropVecMessageKeyEvents_freeOnlyAlign16_s3b (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (dropVecMessageKeyEvents cap mks) := by
  intro ev hev; dsimp only [dropVecMessageKeyEvents] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact mkListFreeEvents_freeOnlyAlign16_s3b mks ev h1
  · exact vec104FreeEvents_freeOnlyAlign16_s3b cap ev h2

private theorem chainPairFreeEvents_freeOnlyAlign16_s3b (gc : ChainGhost × ReceiverChain) :
    FreeOnlyAlign16Evs (chainPairFreeEvents gc) := by
  unfold chainPairFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16_s3b ⟨gc.1.srk.cap, gc.1.srk.ptr⟩)
        (pinFreeEvents_freeOnlyAlign16_s3b ⟨gc.1.priv.cap, gc.1.priv.ptr⟩))
      (sgnCapFreeEvents_freeOnlyAlign16_s3b (optCkCapVal gc.1.ck gc.2.chainKey)))
    (dropVecMessageKeyEvents_freeOnlyAlign16_s3b gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))

private theorem chainListFreeEvents_freeOnlyAlign16_s3b
    (cs : List (ChainGhost × ReceiverChain)) :
    FreeOnlyAlign16Evs (cs.flatMap chainPairFreeEvents) := by
  induction cs with
  | nil => simp only [List.flatMap_nil]; exact FreeOnlyAlign16Evs.nil
  | cons gc tl ih =>
    simp only [List.flatMap_cons]; intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact chainPairFreeEvents_freeOnlyAlign16_s3b gc ev h1
    · exact ih ev h2

private theorem dropSessionStructureLocal1Events_freeOnlyAlign16_s3b
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FreeOnlyAlign16Evs (dropSessionStructureLocal1Events G st) := by
  unfold dropSessionStructureLocal1Events ssFirst3FreeEvents ssTail3FreeEvents dropVecChainEvents
  have h1 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (pinFreeEvents_freeOnlyAlign16_s3b ⟨G.localIk.cap, G.localIk.ptr⟩)
      (pinFreeEvents_freeOnlyAlign16_s3b ⟨G.remoteIk.cap, G.remoteIk.ptr⟩))
    (pinFreeEvents_freeOnlyAlign16_s3b G.root)
  have h2 : FreeOnlyAlign16Evs (senderFreeEvents G.sender) := by
    cases G.sender with
    | none => exact FreeOnlyAlign16Evs.nil
    | some sg =>
      unfold senderFreeEvents
      exact FreeOnlyAlign16Evs.append
        (FreeOnlyAlign16Evs.append
          (FreeOnlyAlign16Evs.append
            (pinFreeEvents_freeOnlyAlign16_s3b ⟨sg.srk.cap, sg.srk.ptr⟩)
            (pinFreeEvents_freeOnlyAlign16_s3b ⟨sg.priv.cap, sg.priv.ptr⟩))
          (sgnCapFreeEvents_freeOnlyAlign16_s3b sg.ck.cap))
        (dropVecMessageKeyEvents_freeOnlyAlign16_s3b sg.mkCap [])
  have h3 : FreeOnlyAlign16Evs
      (((G.chains.zip st.receiverChains).flatMap chainPairFreeEvents) ++
        vec104FreeEvents G.chainsCap) := by
    intro ev hev
    rcases List.mem_append.mp hev with h3a | h3b
    · exact chainListFreeEvents_freeOnlyAlign16_s3b (G.chains.zip st.receiverChains) ev h3a
    · exact vec104FreeEvents_freeOnlyAlign16_s3b G.chainsCap ev h3b
  have h4 := FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (sgnCapFreeEvents_freeOnlyAlign16_s3b (optTailCapVal G.pending))
      (sgnCapFreeEvents_freeOnlyAlign16_s3b (optTailCapVal G.kyber)))
    (pinFreeEvents_freeOnlyAlign16_s3b ⟨G.alice.cap, G.alice.ptr⟩)
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append (FreeOnlyAlign16Evs.append h1 h2) h3) h4)
    (pinFreeEvents_freeOnlyAlign16_s3b G.pq)

private theorem recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
        SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeSeqFreeEnv g r)
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS := by
  unfold LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeSeqFreeEnv
    LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    exact LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.serializeSomeSeqFreeEnv_groupSpec
      fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hgv hdom)

private theorem optDeallocListEvs_freeOnly_s3b (pairs : List (Nat × Nat)) :
    FreeOnlyEvs (optDeallocListEvs pairs) := by
  induction pairs with
  | nil => exact fun _ h => nomatch h
  | cons p rest ih =>
    rcases p with ⟨req, al⟩
    intro ev hev
    simp only [optDeallocListEvs, List.mem_append] at hev
    rcases hev with he | he
    · split at he
      · nomatch he
      · unfold rustDeallocEvents at he; rw [List.mem_singleton] at he; exact ⟨al, req, he⟩
    · exact ih ev he

private theorem w4FailedTdCancelOf_fine_groupSpec_s3b {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseGroupSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w2TryDecryptFailTightGroupS_split_12 := by
  have hFail := w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 F K
    fc.td.dhCap fc.td.needGrow fc.td.withAddr fc.td.errAlloc fc.td.ctLen
    fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
    fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
    hDom.td_dom.caps_len hDom.td_dom.top_tight
  have hDrop : PhaseGroupSpec fineCostModel (· = optDeallocListEvs fc.failDropPairs) 0 :=
    (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h; exact optDeallocListEvs_freeOnly_s3b fc.failDropPairs
  have hCat := (hFail.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

end S3bHoleBHelpers

private theorem s3_hole_b (W : CliHooks) (i : Inputs)
    (peerAddr : CryptoVerification.SignalSession.Cli.MainHops.AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w4 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryRecvPrekeyParams)
    (hw4 : LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryRecvPrekeyDom
      (.recv peerAddr) i w4) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.W4BinaryRecvPrekeyWideSlotEnvFixed w4)
      binaryKitW4FixedGrpS := by
  let _ := hparse
  obtain ⟨hpeerVal, hpeer40, hfiles, hrd, hDom⟩ := hw4 peerAddr rfl
  obtain ⟨hikp, hspkCap, hopkCap, hkpkOtCap, hkpkLrCap⟩ := pqInputs_store_file_caps_s3b hi
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  let R := w4.base
  let P := LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.mkW4RecvPrekeyWideSlotParams R
  have hpeerValLen : R.peer.val.name.length ≤ 40 := hpeer40
  have hAddrG := LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_groupSpec
    fineCostModel R.peer.val hpeerValLen
  have hGetSess := dirGet_readPlain_groups_s3b R.rd R.files
    StoresGhost.opened.sessions (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
  have hGetPeers := dirGet_readPlain_groups_s3b R.rd R.files
    StoresGhost.opened.identity.peers R.peer.val.name
  have hOptDeser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget.OptLoadDeserEnv
        CryptoVerification.SignalSession.Cli.Slots.scopeKit
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.ofBytesEnv
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get R.rd R.files
          (CryptoVerification.SignalSession.Cli.addressText R.peer.val)))
      LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget.OptLoadDeserEnv
    cases StoresGhost.opened.sessions.get R.rd R.files
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        exact s3_phaseGroupSpec_exists fun r _ => by
          unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.ofBytesEnv
          exact (LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.recordDeserializeCancelEnv_fine_groupSpec
            (CryptoVerification.E2E.Record.encodeRecord r)).of_imp fun _ h => h.2
  have hLoadStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv
        R.rd R.files R.peer)
      (11056 + 51 * FineScale +
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS) :=
    (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) (hAddrG.seq (hGetSess.seq (hOptDeser.seq hf)))).mono (by omega)
  have hTrustStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv
        R.rd R.files R.peer w4.remoteIdKey)
      (16659 + 42 * FineScale) :=
    (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hGetPeers.seq hf)).mono (by omega)
  have hStrClone : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv R.peer.name)
      (3 * FineScale) := by
    unfold LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv
    exact (((PhaseGroupSpec.nil fineCostModel).of_imp fun _ h => h.2).or
      ((PhaseGroupSpec.rustAlloc_any fineCostModel R.peer.name.bytes.length 1).of_imp
        fun _ h => h.2)).mono (by omega)
  have hP1Ok : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP1OkEnv
        R.rd R.files R.peer w4.remoteIdKey)
      ((11056 + 51 * FineScale +
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS) +
        (16659 + 42 * FineScale)) :=
    hLoadStep.seq (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hTrustStep)
  have hP1Untrusted : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP1UntrustedEnv
        R.rd R.files R.peer w4.remoteIdKey)
      ((11056 + 51 * FineScale +
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS) +
        (16659 + 42 * FineScale) + 3 * FineScale) :=
    (hLoadStep.seq (hTrustStep.seq (hStrClone.seq hf))).mono (by omega)
  have hSaveStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv
        R.rd R.files R.peer w4.remoteIdKey)
      (16659 + 51 * FineScale) := by
    have hSaveTail : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
          StoresGhost.opened.identity R.peer.val w4.remoteIdKey
          (StoresGhost.opened.identity.peers.get R.rd R.files R.peer.val.name))
        (9 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
      cases StoresGhost.opened.identity.peers.get R.rd R.files R.peer.val.name with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok _ =>
        have hpks : PhaseGroupSpec fineCostModel
            LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
            (3 * FineScale) := PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
        have hput := s3_dirPutStr_opened_groups fineCostModel
          (dir := StoresGhost.opened.identity.peers) rfl R.peer.val.name w4.remoteIdKey.serialize
        exact (hf.seq (hpks.seq hput)).mono (by omega)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hGetPeers.seq hSaveTail)).mono (by omega)
  have hArchSer := recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b hDom.outer_dom.arch_valid
  have hOut0Ser := recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b hDom.outer_dom.out0_valid
  have hOut1Ser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.SerializePrev1SeqFreeEnv
        R.G_out1 R.sess_out1 R.enc_prev1)
      LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.serializePrev1FreshBobFineGrpS := by
    unfold LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.SerializePrev1SeqFreeEnv
    have hfb : LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.FreshBobCloneDom
        _ R.G_out1 R.sess_out1 :=
      ⟨hDom.outer_dom.out1_freshBob.rc_nil, hDom.outer_dom.out1_freshBob.gv,
        hDom.outer_dom.out1_freshBob.dom⟩
    have hcl := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneEnv_freshBobCloneDom_fine_groupSpec hfb
    have hvv := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.vecVecClone1Events_fine_groupSpec R.enc_prev1
    have hout := PhaseGroupSpec.rustAlloc_any fineCostModel
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
        R.G_out1 R.sess_out1 R.enc_prev1).length 1
    exact (hcl.seq (hvv.seq (hout.seq hf))).mono (by decide)
  have hSessStore0 : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySessStoreStepEnv
        R.peer R.g_out0 R.r_out0)
      (16659 + 12 * FineScale +
        LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS) := by
    have hput := s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
      (CryptoVerification.E2E.Record.encodeRecord R.r_out0)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hAddrG.seq (hOut0Ser.seq hput))).mono (by omega)
  have hSessStore1 : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySessStorePrev1StepEnv
        R.peer R.G_out1 R.sess_out1 R.enc_prev1)
      (16659 + 12 * FineScale +
        LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.serializePrev1FreshBobFineGrpS) := by
    have hput := s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
        R.G_out1 R.sess_out1 R.enc_prev1)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hAddrG.seq (hOut1Ser.seq hput))).mono (by omega)
  have hPromArch : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryPromoteArchiveEnv
        R.g_arch R.r_arch)
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS + 3 * FineScale) := by
    have h1 := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.promoteStateArchive_groupSpec
      fineCostModel hArchSer
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 192)
    have h2 : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryArchiveDirectEnv
          (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length)
        (6 * FineScale) := by
      have ha : PhaseGroupSpec fineCostModel
          (fun e => ∃ n ≤ (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length,
            e = LibsignalBinary.Heap.rustAllocEvents n 1)
          (3 * FineScale) :=
        s3_phaseGroupSpec_exists (P := fun n => n ≤ (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length)
          (E := fun n e => e = LibsignalBinary.Heap.rustAllocEvents n 1) fun n _ =>
          PhaseGroupSpec.rustAlloc_any fineCostModel n 1
      have hb := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 192
      exact (hf.seq (ha.seq (hb.seq hf))).mono (by unfold FineScale; omega)
    exact (h1.or h2).mono (by decide)
  have hDec : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.DecEnv x)
        LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.deserCancelFineGrpS :=
    fun x _ => LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.sessDeserializeCancelEnv_fine_groupSpec x.r_dec
  have hTr : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.TrialEnv x)
        (LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.w4RealTrialFineGrpS + 11056) := by
    intro x hx
    have hxd := hDom.trials_dom x hx
    have hcf := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4TryDecryptCloneFailWide_fine_groupSpec
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hxd.tr_gv hxd.tr_dom)
      (w4FailedTdCancelOf_fine_groupSpec_s3b hxd.tr_fail)
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.dropClonedSessionEvents_groupSpec
        fineCostModel x.G_tr x.ses_tr.state)
    exact (hf.or hcf).mono (by decide)
  have hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0 := by
    intro x _
    exact hf.of_imp fun _ h => by
      subst h
      exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.FreeOnlyAlign16Evs.toFreeOnlyEvs
        (dropSessionStructureLocal1Events_freeOnlyAlign16_s3b x.G_dec x.st_dec)
  have hTrials := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.archivedTrialLoop_le4_groupSpec
    fineCostModel hDom.outer_dom.trials_len4 hDec hTr hDrop
  have hCloneB : PhaseGroupSpec fineCostModel
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4CloneBDomEnv
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneDomFineGrpS :=
    (s3_phaseGroupSpec_exists fun (gs : CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost ×
        CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
        (hp : LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid gs.1 gs.2 ∧
          LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom 286196 gs.2) =>
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hp.1 hp.2).of_imp
      fun _ ⟨G, ses, hgv, hdom, hs⟩ => ⟨(G, ses), ⟨hgv, hdom⟩, hs⟩
  have hCloneAC : PhaseGroupSpec fineCostModel
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4CloneACDomEnv
      LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneFreshBobFineGrpS :=
    (s3_phaseGroupSpec_exists fun (gs : CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost ×
        CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
        (hp : LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.FreshBobCloneDom 16384 gs.1 gs.2) =>
      LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneEnv_freshBobCloneDom_fine_groupSpec hp).of_imp
      fun _ ⟨G, ses, hfb, hs⟩ => ⟨(G, ses), hfb, hs⟩
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv
      LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit.w2TryDecryptTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then
        LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4TryDecryptPathBEnv R.F R.K R.td_B
      else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := hDom.tdB_dom hpb
      exact LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit.w2TryDecryptTightEnv_linked_fine_groupSpec_split_12
        R.F R.K R.td_B.dhCap R.td_B.needGrow R.td_B.withAddr R.td_B.errAlloc R.td_B.ctLen
        R.td_B.stBytes R.td_B.w.pre_pb R.td_B.w.vn R.td_B.w.pb R.td_B.w.st0
        R.td_B.w.sckaMsg R.td_B.w.v R.td_B.w.xInit R.td_B.w.xNew R.td_B.w.xAdd
        R.td_B.w.xRk R.td_B.w.xSInto R.td_B.w.xCInto hd.caps_len hd.top_tight
  have hTdAC : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4RecvPrekeyTryDecACEnv R)
      LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit.w2TryDecryptSeeds12GroupS_split_12 := by
    unfold LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := (hDom.tdAC_dom hpac).base
      exact LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit.w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12
        R.F R.K R.td_AC.dhCap R.td_AC.needGrow R.td_AC.withAddr R.td_AC.errAlloc R.td_AC.ctLen
        R.td_AC.stBytes R.td_AC.w.pre_pb R.td_AC.w.vn R.td_AC.w.pb R.td_AC.w.st0
        R.td_AC.w.sckaMsg R.td_AC.w.v R.td_AC.w.xInit R.td_AC.w.xNew R.td_AC.w.xAdd
        R.td_AC.w.xRk R.td_AC.w.xSInto R.td_AC.w.xCInto hd.caps_len hd.top_tight
  have hCurFail : PhaseGroupSpec fineCostModel P.CurTrialFailEnv
      LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit.w2TryDecryptFailTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then
        LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4FailedTdCancelEnv R.F R.K R.fc_cur
      else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact w4FailedTdCancelOf_fine_groupSpec_s3b (hDom.cur_fail_dom hcs)
  have hCurCloneFail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.W4TryDecryptCloneFailWideEnv
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv R.G_cur R.st_cur)
        P.CurTrialFailEnv
        (· = LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.dropClonedSessionEvents R.G_cur R.st_cur))
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneDomFineGrpS +
        LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit.w2TryDecryptFailTightGroupS_split_12 +
        LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4ErrTailWideFineGrpS) := by
    rcases hDom.outer_dom.cur_dom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
    · have hEmpty : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.W4TryDecryptCloneFailWideEnv
            (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv R.G_cur R.st_cur)
            P.CurTrialFailEnv
            (· = LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.dropClonedSessionEvents R.G_cur R.st_cur))
          0 :=
        { groups_le := fun _ {_} hE => by
            rcases hE with h1 | ⟨_, _, _, h1, _⟩
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf)
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf) }
      exact hEmpty.mono (Nat.zero_le _)
    · have hst_eq' : ses_cur.state = R.st_cur := hst_eq
      rw [← hst_eq']
      exact LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4TryDecryptCloneFailWide_fine_groupSpec
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hgv hdom)
        hCurFail
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.dropClonedSessionEvents_groupSpec
          fineCostModel R.G_cur ses_cur.state)
  have hSpkGetStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv
        R.rd R.files R.spkId)
      (11056 + 216 * FineScale) := by
    have hopt : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.OptSpkDecodeEnv
          LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
          (StoresGhost.opened.signed.get R.rd R.files (CryptoVerification.SignalSession.Cli.keyName R.spkId)))
        (144 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.OptSpkDecodeEnv
      cases hget : StoresGhost.opened.signed.get R.rd R.files
        (CryptoVerification.SignalSession.Cli.keyName R.spkId) with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | cons b rest =>
          have hbs : (b :: rest).length ≤ 230 := by
            rw [hfiles, hrd] at hget; exact hspkCap R.spkId (b :: rest) hget
          exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.spkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.signed
            (CryptoVerification.SignalSession.Cli.keyName R.spkId)).seq
          (hopt.seq hf)))).mono (by omega)
  have hKpkGetStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv
        R.rd R.files R.kpkId)
      (11056 + 894 * FineScale) := by
    have hpassOt : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv
          (fun d k => DirGetEnv PathEnv (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv R.rd)
            R.rd R.files d (CryptoVerification.SignalSession.Cli.keyName k))
          LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
          R.rd R.files StoresGhost.opened.kyber.oneTime R.kpkId)
        (447 * FineScale) := by
      have hopt : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
            LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
            (StoresGhost.opened.kyber.oneTime.get R.rd R.files
              (CryptoVerification.SignalSession.Cli.keyName R.kpkId)))
          (375 * FineScale) := by
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
        cases hget : StoresGhost.opened.kyber.oneTime.get R.rd R.files
          (CryptoVerification.SignalSession.Cli.keyName R.kpkId) with
        | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | ok bs =>
          cases bs with
          | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          | cons b rest =>
            have hbs : (b :: rest).length ≤ 4900 := by
              rw [hfiles, hrd] at hget; exact hkpkOtCap R.kpkId (b :: rest) hget
            exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
      exact ((decimal_groups_s3b R.kpkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.kyber.oneTime
            (CryptoVerification.SignalSession.Cli.keyName R.kpkId)).seq
          (hopt.seq hf))).mono (by omega)
    have hpassLr : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv
          (fun d k => DirGetEnv PathEnv (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv R.rd)
            R.rd R.files d (CryptoVerification.SignalSession.Cli.keyName k))
          LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
          R.rd R.files StoresGhost.opened.kyber.lastResort R.kpkId)
        (447 * FineScale) := by
      have hopt : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
            LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
            (StoresGhost.opened.kyber.lastResort.get R.rd R.files
              (CryptoVerification.SignalSession.Cli.keyName R.kpkId)))
          (375 * FineScale) := by
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
        cases hget : StoresGhost.opened.kyber.lastResort.get R.rd R.files
          (CryptoVerification.SignalSession.Cli.keyName R.kpkId) with
        | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | ok bs =>
          cases bs with
          | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          | cons b rest =>
            have hbs : (b :: rest).length ≤ 4900 := by
              rw [hfiles, hrd] at hget; exact hkpkLrCap R.kpkId (b :: rest) hget
            exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
      exact ((decimal_groups_s3b R.kpkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.kyber.lastResort
            (CryptoVerification.SignalSession.Cli.keyName R.kpkId)).seq
          (hopt.seq hf))).mono (by omega)
    have hpoll : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.CliKpkGetPollEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv
          (fun d k => DirGetEnv PathEnv (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv R.rd)
            R.rd R.files d (CryptoVerification.SignalSession.Cli.keyName k))
          LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliSpkDecodeEnv
          R.rd R.files ⟨0#64, 0#64, 0#64, R.kpkId, StoresGhost.opened.kyber⟩)
        (894 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.CliKpkGetPollEnv
      dsimp only
      split
      · exact (hpassOt.seq hpassLr).mono (by omega)
      · exact hpassOt.mono (by omega)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) hpoll).mono (by omega)
  have hPkGetStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv
        R.rd R.files R.opkId)
      (11056 + 831 * FineScale) := by
    have hopt : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget.OptPkDecodeEnv
          LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.CliPkDecodeEnv
          (StoresGhost.opened.oneTime.get R.rd R.files (CryptoVerification.SignalSession.Cli.keyName R.opkId)))
        (759 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget.OptPkDecodeEnv
      cases hget : StoresGhost.opened.oneTime.get R.rd R.files
        (CryptoVerification.SignalSession.Cli.keyName R.opkId) with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | cons b rest =>
          have hbs : (b :: rest).length ≤ 125 := by
            rw [hfiles, hrd] at hget; exact hopkCap R.opkId (b :: rest) hget
          exact cliPkDecode_groups_s3b hbs
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.opkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.oneTime
            (CryptoVerification.SignalSession.Cli.keyName R.opkId)).seq
          (hopt.seq hf)))).mono (by omega)
  have hPkGetOpt := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_ite_nil
    R.hasOpk (fun _ => hPkGetStep)
  have hSelfKpStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv R.rd R.files)
      (11056 + 681 * FineScale) := by
    have hikp_r : ∀ bs,
        StoresGhost.opened.identity.own.get R.rd R.files (utf8 "identity-key-pair") = .ok bs →
          bs.length ≤ 105 := by
      rw [hfiles, hrd]; exact hikp
    exact ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage
        (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.boxAllocEnv_le_28_fine_groupSpec
          (boxSz := 16) (by decide))).seq
      ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.identity.own
          (utf8 "identity-key-pair")).seq
        ((s3_ikpTryFrom_groups fineCostModel hikp_r).seq hf))).mono (by omega)
  have hSelfRegStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv R.rd R.files)
      (11056 + 45 * FineScale) := by
    have hmal : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget.OptRegIdMalformedEnv
          (StoresGhost.opened.identity.own.get R.rd R.files (utf8 "registration-id")))
        (3 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget.OptRegIdMalformedEnv
      cases StoresGhost.opened.identity.own.get R.rd R.files (utf8 "registration-id") with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        dsimp only; split_ifs
        · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any fineCostModel 14 1
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.identity.own
          (utf8 "registration-id")).seq (hmal.seq hf))).mono (by omega)
  have hPk33 : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.SeqEnv (LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak.W4BoundedEvs 1 33)
        LibsignalBinary.Heap.FreeOnlyEvs)
      (3 * FineScale) :=
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 33).seq hf).mono
      (by omega)
  have hKemKp : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.SeqEnv
        LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.KemKeyPairFromPubPrivEnv
        LibsignalBinary.Heap.FreeOnlyEvs)
      (6 * FineScale) := by
    have hk : PhaseGroupSpec fineCostModel
        LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.KemKeyPairFromPubPrivEnv
        (6 * FineScale) :=
      (s3_phaseGroupSpec_append_eq fineCostModel
        (PhaseGroupSpec.rustAlloc_any fineCostModel 1568 1)
        (PhaseGroupSpec.rustAlloc_any fineCostModel 3168 1)).mono (by decide)
    exact (hk.seq hf).mono (by omega)
  have hTail21 : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.SeqEnv (LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak.W4BoundedEvs 1 21)
        LibsignalBinary.Heap.FreeOnlyEvs)
      (3 * FineScale) :=
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 21).seq hf).mono
      (by omega)
  have hInitBob : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryInitBobWideEnv
        R.F R.x_res R.hasOpk R.x_spqr)
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4InitBobSpqr9FineGrpS + 18 * FineScale) := by
    have hacc1 := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4PqxdhAccept_fine_groupSpec R.x_res R.hasOpk
    have hacc2 := ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec
      fineCostModel 6 192).seq hf).mono (show 6 * (3 * FineScale) + 0 ≤ 18 * FineScale by omega)
    have hacc := hacc1.or hacc2
    have hspqr := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.initialStateEnv_groupSpec fineCostModel R.F R.x_spqr
    have hbob := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BobSessionBuild9_groupSpec fineCostModel)
    exact (hacc.seq (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage
      (hspqr.seq hbob))).mono (by decide)
  have hKpkMarkStep := kpkMarkStepFixed_groups_s3b R.rd R.files R.kpkId R.spkId w4.baseKey
  have hPkRmStep : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryPkRemoveStepEnv
        R.rd R.files R.opkId)
      (11056 + 105 * FineScale) := by
    have htail : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget.OptPkRemoveTailEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutEnv
          ⟨0#64, 0#64, 0#64, R.opkId, StoresGhost.opened.oneTime⟩
          (StoresGhost.opened.oneTime.get R.rd R.files
            (CryptoVerification.SignalSession.Cli.keyName R.opkId)))
        (33 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget.OptPkRemoveTailEnv
      cases StoresGhost.opened.oneTime.get R.rd R.files
        (CryptoVerification.SignalSession.Cli.keyName R.opkId) with
      | error _ => exact hf.mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact hf.mono (Nat.zero_le _)
        | cons _ _ =>
          exact (hf.seq ((decimal_groups_s3b R.opkId).seq
            (s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.oneTime) rfl
              (CryptoVerification.SignalSession.Cli.keyName R.opkId) []))).mono (by omega)
    exact (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.opkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.oneTime
            (CryptoVerification.SignalSession.Cli.keyName R.opkId)).seq htail))).mono (by omega)
  have hPkRmOpt := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_ite_nil
    R.hasOpk (fun _ => hPkRmStep)
  have hP2B := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4StageP2MatchedCheck_fine_groupSpec.seq
    (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage
      (hf.or (hTrials.seq (hf.or (hPromArch.seq hf)))))
  have hP3B := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4StageP3Wide_fine_groupSpec hCloneB hTdB
  have hP4B := (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSaveStep).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSessStore0).seq hf)
  have hPathB := hP1Ok.seq ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP2B).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP3B).seq
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP4B)))
  have hP2A := (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPk33).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSpkGetStep).seq
      ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKpkGetStep).seq
        ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKemKp).seq
          ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hTail21).seq
            ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPkGetOpt).seq
              ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSelfKpStep).seq
                ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hInitBob).seq
                  ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSelfRegStep).seq
                    LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4ErrTailWide_fine_groupSpec))))))))
  have hP3AC := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4StageP3Wide_fine_groupSpec hCloneAC hTdAC
  have hP4A := (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSaveStep).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKpkMarkStep).seq
      ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPkRmOpt).seq
        ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSessStore0).seq hf)))
  have hPathA := hP1Ok.seq ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP2A).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP3AC).seq
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP4A)))
  have hP2C := (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hCurCloneFail).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hTrials).seq
      ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPk33).seq
        ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSpkGetStep).seq
          ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKpkGetStep).seq
            ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKemKp).seq
              ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hTail21).seq
                ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPkGetOpt).seq
                  ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSelfKpStep).seq
                    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hInitBob).seq
                      ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSelfRegStep).seq
                        ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPromArch).seq
                          LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4ErrTailWide_fine_groupSpec)))))))))))
  have hP4C := (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSaveStep).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hKpkMarkStep).seq
      ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hPkRmOpt).seq
        ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hSessStore1).seq hf)))
  have hPathC := hP1Ok.seq ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP2C).seq
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP3AC).seq
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.phaseGroupSpec_optStage hP4C)))
  exact (hf.or ((hP1Untrusted.or (hPathB.or (hPathA.or hPathC))).seq hf)).mono
    (show _ ≤ binaryKitW4FixedGrpS by decide)

/-- Binary-kit W4 (`recv-prekey`) `SingleSlotFineSpec` on
`(mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv` bounded by `binaryKitW4Fixed*`. -/
def binaryKitW4Fixed_fineSpec [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    SingleSlotFineSpec ((mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv) where
  cum := binaryKitW4FixedCum
  live := binaryKitW4FixedLive
  peak := binaryKitW4FixedPeak
  maxReq := binaryKitW4FixedMaxReq
  grpS := binaryKitW4FixedGrpS
  credit := by
    dsimp only [mkBinaryKitRealCalleeEnvsFixed]
    cases hgc : g.c with
    | keygen | init _ _ | send _ =>
      exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | recv peerAddr =>
      rw [hgc] at hparse
      exact s3_phaseCreditSpec_exists fun w4 hw4 => s3_hole_a W g.i peerAddr hi hparse w4 hw4
  live_le_peak := d3RecvW4Ext_live_le_peak
  groups := by
    dsimp only [mkBinaryKitRealCalleeEnvsFixed]
    cases hgc : g.c with
    | keygen | init _ _ | send _ =>
      exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _)
    | recv peerAddr =>
      rw [hgc] at hparse
      exact s3_phaseGroupSpec_exists fun w4 hw4 => s3_hole_b W g.i peerAddr hi hparse w4 hw4

/-! ## Whole-`main` Binary-Kit `FitsEnv` Closure -/

private def EntriesFromNormS4 (files : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, Arm64.normalizePath p = k ∧ (p, bs) ∈ files

private theorem entriesFromNorm_empty_s4 (files : List (String × List (BitVec 8))) :
    EntriesFromNormS4 files ({} : Arm64.FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem entriesFromNorm_setEntry_dir_s4 {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : EntriesFromNormS4 files fs) (pref : Arm64.FsPath) :
    EntriesFromNormS4 files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromNorm_foldl_dirs_s4 {files : List (String × List (BitVec 8))}
    (prefs : List Arm64.FsPath) {fs : Arm64.FsState} (h : EntriesFromNormS4 files fs) :
    EntriesFromNormS4 files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_setEntry_dir_s4 h hd)

private theorem entriesFromNorm_foldl_outer_dirs_s4 {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : Arm64.FsState} (h : EntriesFromNormS4 files fs) :
    EntriesFromNormS4 files
      (dirs.foldl
        (fun acc d => (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNorm_foldl_dirs_s4 _ h)

private theorem entriesFromNorm_setFile_s4 {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : EntriesFromNormS4 files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFromNormS4 files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold Arm64.FsState.setFile Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i heq
    have hk_eq : Arm64.normalizePath p = k := (beq_iff_eq.mp heq).symm
    injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, hk_eq, hmem⟩
  · exact h k bs' hk

private theorem entriesFromNorm_foldl_files_s4 {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : Arm64.FsState} (h : EntriesFromNormS4 allFiles fs) :
    EntriesFromNormS4 allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc :=
            ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
              (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFromNorm_foldl_dirs_s4
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast) h
    have hset := entriesFromNorm_setFile_s4 hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem initFsState_files_mem_norm_s4 {inputs : Arm64.Process.ProcessInputs} {q : String}
    {bs : List (BitVec 8)}
    (h : (Arm64.Process.initFsState inputs).files q = some (.file bs)) :
    ∃ p, Arm64.normalizePath p = Arm64.normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := entriesFromNorm_foldl_outer_dirs_s4 inputs.dirs (entriesFromNorm_empty_s4 inputs.files)
  have hf := entriesFromNorm_foldl_files_s4 inputs.files (fun _ hx => hx) hd
  unfold Arm64.FsState.files Arm64.FsState.getEntry at h
  split at h
  · cases h
  · exact hf (Arm64.normalizePath q) bs h

private theorem splitSlash_go_append_slash_s4 (cur a b : List Char) :
    Arm64.splitSlash.go cur (a ++ ('/' :: b)) =
      Arm64.splitSlash.go cur a ++ Arm64.splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, Arm64.splitSlash.go, ih []]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        Arm64.splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem normalizePath_append_slash_s4 (a b : String) :
    Arm64.normalizePath (a ++ "/" ++ b) = Arm64.normalizePath a ++ Arm64.normalizePath b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [htl, splitSlash_go_append_slash_s4 [] a.toList b.toList, List.filter_append]

private theorem norm_subdir_ne_ikp_s4 {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ "identity-key-pair") :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ ["identity-key-pair"] := by
  rw [normalizePath_append_slash_s4 dir sub, hdir, List.singleton_append]
  intro h
  injection h with hd _
  exact hne hd

private def kutf8_s4 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data_s4 : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem utf8_eq_kutf8_s4 (s : String) : utf8 s = kutf8_s4 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8_s4, List.utf8Encode, byteArray_toList_eq_data_s4]

private theorem ikp_encode_len_le_105_s4
    (P : CryptoVerification.E2E.PEParams) (st : CryptoVerification.SignalSession.PqParty) :
    (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
        st.me.idPriv.toList⟩).length ≤ 105 := by
  let pub := CryptoVerification.E2E.djbKey
    (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes
  let priv := st.me.idPriv.toList
  have hpub_len : pub.length = 33 := by simp [pub, CryptoVerification.E2E.djbKey]
  have hpriv_len : priv.length = 32 := st.me.idPriv.toList_length
  have hpub_ne : pub ≠ [] := by intro h; rw [h] at hpub_len; contradiction
  have hpriv_ne : priv ≠ [] := by intro h; rw [h] at hpriv_len; contradiction
  change (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode ⟨pub, priv⟩).length ≤ 105
  unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
    CryptoVerification.RecordCodecs.encodeProto3BytesField
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [hpub_ne, hpriv_ne, ↓reduceIte, List.length_append, hpub_len, hpriv_len]
  decide

private theorem cliIo_rd_eq_ok_nil_or_files_some_s4 {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
        (CryptoVerification.SignalSession.Cli.MainHops.pathStr path) = some (.file bs) := by
  change CryptoVerification.SignalSession.Cli.MainHops.cliRd
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files path =
        .ok bs at hrd
  unfold CryptoVerification.SignalSession.Cli.MainHops.cliRd at hrd; split at hrd
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

private theorem encodeDir_norm_ikp_len_le_105_s4
    {P : CryptoVerification.E2E.PEParams} {st : CryptoVerification.SignalSession.PqParty}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st)
    (hnorm : Arm64.normalizePath p = ["identity-key-pair"]) :
    bs.length ≤ 105 := by
  unfold CryptoVerification.SignalSession.encodeDir at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
    · injection h with _ hbs; subst hbs; exact ikp_encode_len_le_105_s4 P st
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact absurd hnorm (norm_subdir_ne_ikp_s4 (dir := "identities") (by decide) (by decide))
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact absurd hnorm (norm_subdir_ne_ikp_s4 (dir := "sessions") (by decide) (by decide))
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (norm_subdir_ne_ikp_s4 (dir := "signed-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (norm_subdir_ne_ikp_s4 (dir := "one-time-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (norm_subdir_ne_ikp_s4 (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq _; subst hp_eq
      exact absurd hnorm
        (norm_subdir_ne_ikp_s4 (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
    · injection h2 with hp_eq _; subst hp_eq
      unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
      rw [String.append_assoc] at hnorm
      exact absurd hnorm
        (norm_subdir_ne_ikp_s4 (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem bundle_norm_ne_ikp_s4 {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir) :
    Arm64.normalizePath p ≠ ["identity-key-pair"] := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _; subst hp; decide

private theorem cliIo_rd_ownIkp_le_105_of_cliPqInputs_s4
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105 := by
  intro bs hrd
  change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
  rcases cliIo_rd_eq_ok_nil_or_files_some_s4 hrd with rfl | hfile
  · exact Nat.zero_le 105
  · have hpth :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
          "identity-key-pair" := by
      change CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "identity-key-pair") =
        "identity-key-pair"
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [utf8_eq_kutf8_s4]
      rfl
    rw [hpth] at hfile
    obtain ⟨p, hp_norm, hp_mem⟩ := initFsState_files_mem_norm_s4 hfile
    have hikp_norm : Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
    rw [hikp_norm] at hp_norm
    have hp_files : (p, bs) ∈ i.files := hp_mem
    obtain ⟨st, _, hcase⟩ := hi
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
        ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
    · simp only [CryptoVerification.SignalSession.pqInitInputs,
        CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
      rcases hp_files with (hed | hbun) | hcoins
      · exact encodeDir_norm_ikp_len_le_105_s4 hed hp_norm
      · exact absurd hp_norm (bundle_norm_ne_ikp_s4 hbun)
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqSendInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact encodeDir_norm_ikp_len_le_105_s4 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact encodeDir_norm_ikp_len_le_105_s4 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact encodeDir_norm_ikp_len_le_105_s4 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact encodeDir_norm_ikp_len_le_105_s4 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)

private theorem max_mono_s4 {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem optStage_phaseCredit_s4 {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (CliSlotEnvelopeBridge.OptStageEnv P) c l p r :=
  CliRunPeakHelpers.phaseCredit_or_freeOnly_left SeqCreditKitLemmas.fineCostModel_modelHyps
    (fun _ hf => hf) h

private theorem optStage_groupSpec_s4 {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (CliSlotEnvelopeBridge.OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem binaryKitInit_imp_w3Fixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    ∀ evs, (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv g).initEnv evs →
      (match g.c with
       | .init _ _ => fun evs =>
         ∃ w : W3BinaryInitParams,
           W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
       | _ => fun _ => False) evs := by
  rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
  intro evs h
  cases gc with
  | keygen _ _ => exact False.elim h
  | send _ => exact False.elim h
  | recv _ => exact False.elim h
  | init peerAddr dir =>
    rcases h with ⟨w, hw, hevs⟩
    exact ⟨w, hw,
      (RealCliRunEnvMemFixed.w3InitBinaryKitSlotEnvFixed_eq_plain hi_g
        (hw peerAddr dir rfl).2.2.1).symm ▸ hevs⟩

private def binaryKitCalleeFineSpecs_s4 [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (Spk : SingleSlotFineSpec (decPkEnv g))
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    CliTopBudgetReal.CliRealCalleeFineSpecs
      (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv g) where
  initCum := w3InitRealCum + 4500000
  initLive := w3InitRealLive + 65536
  initPeak := w3InitRealPeak + 65536
  initMaxReq := w3InitRealMaxReq + 65536
  initGrpS := w3InitRealGrpS + 1500 * FineScale
  init_spec := PhaseCreditSpec.of_imp (binaryKitInit_imp_w3Fixed img S X W hi_g)
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs_s4 hi_g)).credit
  init_lp :=
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs_s4 hi_g)).live_le_peak
  init_grp := PhaseGroupSpec.of_imp
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs_s4 hi_g)).groups
    (binaryKitInit_imp_w3Fixed img S X W hi_g)
  encCum := w1SendRealDcanCum
  encLive := w1SendRealDcanPeak
  encPeak := w1SendRealDcanPeak
  encMaxReq := w1SendRealDcanMaxReq
  encGrpS := w1SendRealDcanGrpS
  enc_spec := (binaryKitW1_fineSpec img S X W g hi_g hparse).credit.mono
    (Nat.le_refl _) (binaryKitW1_fineSpec img S X W g hi_g hparse).live_le_peak
    (Nat.le_refl _) (Nat.le_refl _)
  enc_lp := Nat.le_refl _
  enc_grp := (binaryKitW1_fineSpec img S X W g hi_g hparse).groups
  decSigCum := w2RecvWhisperRealDcanCum
  decSigLive := w2RecvWhisperRealDcanPeak
  decSigPeak := w2RecvWhisperRealDcanPeak
  decSigMaxReq := w2RecvWhisperRealDcanMaxReq
  decSigGrpS := w2RecvWhisperRealDcanGrpS
  decSig_spec := (binaryKitW2_fineSpec img S X W g hi_g hparse).credit.mono
    (Nat.le_refl _) (binaryKitW2_fineSpec img S X W g hi_g hparse).live_le_peak
    (Nat.le_refl _) (Nat.le_refl _)
  decSig_lp := Nat.le_refl _
  decSig_grp := (binaryKitW2_fineSpec img S X W g hi_g hparse).groups
  pksmCum := WirePksmTightCredit.pksmCanonSliceCum SpqrDomainCapsAux.msgCapBytes
  pksmLive := WirePksmTightCredit.pksmCanonSliceLive SpqrDomainCapsAux.msgCapBytes
  pksmPeak := WirePksmTightCredit.pksmCanonSlicePeak SpqrDomainCapsAux.msgCapBytes
  pksmMaxReq := WirePksmTightCredit.pksmCanonSliceMaxReq SpqrDomainCapsAux.msgCapBytes
  pksmGrpS := WirePksmTightCredit.pksmCanonSliceGrpS SpqrDomainCapsAux.msgCapBytes
  pksm_spec := fun _ hrest => WirePksmTightCredit.pksmCanonSlice_fine_phaseCredit hrest
  pksm_lp := WirePksmTightCredit.pksmCanonSliceLive_le_peak SpqrDomainCapsAux.msgCapBytes
  pksm_grp := fun _ hrest => WirePksmTightCredit.pksmCanonSlice_fine_groupSpec hrest
  decPkCum := Spk.cum
  decPkLive := Spk.live
  decPkPeak := Spk.peak
  decPkMaxReq := Spk.maxReq
  decPkGrpS := Spk.grpS
  decPk_spec := Spk.credit
  decPk_lp := Spk.live_le_peak
  decPk_grp := Spk.groups

private def s4ExtRunCum : Nat :=
  CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmCum
    (WirePksmTightCredit.pksmCanonSliceCum SpqrDomainCapsAux.msgCapBytes)
    (w3InitRealCum + 4500000) w1SendRealDcanCum w2RecvWhisperRealDcanCum binaryKitW4FixedCum

private def s4ExtRunLive : Nat :=
  CliTopBudgetReal.cliRun1MiBCustomPksmLive
    (WirePksmTightCredit.pksmCanonSliceLive SpqrDomainCapsAux.msgCapBytes)
    (w3InitRealLive + 65536) w1SendRealDcanPeak w2RecvWhisperRealDcanPeak binaryKitW4FixedLive

private def s4ExtRunPeak : Nat :=
  CliTopBudgetReal.cliRun1MiBCustomPksmPeak
    (WirePksmTightCredit.pksmCanonSliceLive SpqrDomainCapsAux.msgCapBytes)
    (WirePksmTightCredit.pksmCanonSlicePeak SpqrDomainCapsAux.msgCapBytes)
    (w3InitRealPeak + 65536) w1SendRealDcanPeak w1SendRealDcanPeak
    w2RecvWhisperRealDcanPeak binaryKitW4FixedPeak

private def s4ExtRunMaxReq : Nat :=
  CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmMaxReq
    (WirePksmTightCredit.pksmCanonSliceMaxReq SpqrDomainCapsAux.msgCapBytes)
    (w3InitRealMaxReq + 65536) w1SendRealDcanMaxReq w2RecvWhisperRealDcanMaxReq binaryKitW4FixedMaxReq

private def s4ExtRunGrpS : Nat :=
  CliTopBudgetReal.cliRunOpenedCustomPksmGrpS SpqrDomainCapsAux.msgCapBytes
    (WirePksmTightCredit.pksmCanonSliceGrpS SpqrDomainCapsAux.msgCapBytes)
    (w3InitRealGrpS + 1500 * FineScale) w1SendRealDcanGrpS w2RecvWhisperRealDcanGrpS
    binaryKitW4FixedGrpS

private def s4BinaryExtRunGrpS : Nat :=
  s4ExtRunGrpS + 27 * FineScale

private def s4BinaryExtMainCum : Nat :=
  123250 + CliMainPeakSpec.m3PhaseDeltaCum_tight + s4ExtRunCum +
    CliFitsTraceArith.cliMaxDirtyEntries *
      (10 * max (4 * CliFitsTraceArith.cliMaxDirPathBytes +
        CliFitsTraceArith.cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    CliMainPeakSpec.m6DeltaCum

private def s4ExtMainLive : Nat :=
  CliTopBudgetSpec.cliMainTightLiveOf s4ExtRunLive

private def s4ExtMainPeak : Nat :=
  CliTopBudgetSpec.cliMainTightPeakOf s4ExtRunLive s4ExtRunPeak

private def s4ExtMainReq : Nat :=
  max (max (16 * 2048) 16384) (CliTopBudgetSpec.cliMainTightReqOf s4ExtRunMaxReq)

private def s4BinaryExtMainGrpS : Nat :=
  RealMainEnvAdapter.cliMainWidenedSetupFineGrpS + s4BinaryExtRunGrpS +
    CliFitsTraceArith.cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

private theorem binaryKitCalleeFineSpecs_ext_bounds_s4 [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (Spk : SingleSlotFineSpec (decPkEnv g))
    (hCaps : Spk.cum ≤ binaryKitW4FixedCum ∧
      Spk.live ≤ binaryKitW4FixedLive ∧
      Spk.peak ≤ binaryKitW4FixedPeak ∧
      Spk.maxReq ≤ binaryKitW4FixedMaxReq ∧
      Spk.grpS ≤ binaryKitW4FixedGrpS)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := binaryKitCalleeFineSpecs_s4 img S X W Spk hi_g hparse
    CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmCum
      SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤ s4ExtRunCum ∧
    CliTopBudgetReal.cliRun1MiBCustomPksmLive
      SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤ s4ExtRunLive ∧
    CliTopBudgetReal.cliRun1MiBCustomPksmPeak
      SE.pksmLive SE.pksmPeak SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
        s4ExtRunPeak ∧
    CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmMaxReq
      SE.pksmMaxReq SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤ s4ExtRunMaxReq ∧
    CliTopBudgetReal.cliRunOpenedCustomPksmGrpS SpqrDomainCapsAux.msgCapBytes
      SE.pksmGrpS SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤ s4ExtRunGrpS := by
  rcases hCaps with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [binaryKitCalleeFineSpecs_s4]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold s4ExtRunCum CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmCum
    exact Nat.add_le_add (Nat.le_refl _)
      (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _)
        (max_mono_s4 (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpc))))
  · unfold s4ExtRunLive CliTopBudgetReal.cliRun1MiBCustomPksmLive
    exact Nat.add_le_add (Nat.le_refl _)
      (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _)
        (max_mono_s4 (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpl))))
  · unfold s4ExtRunPeak CliTopBudgetReal.cliRun1MiBCustomPksmPeak
    exact max_mono_s4 (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _)
      (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _)
        (max_mono_s4 (Nat.le_refl _)
          (max_mono_s4 (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpp))))))
  · unfold s4ExtRunMaxReq CliSlotEnvelopeBridge.cliRunBinary1MiBCustomPksmMaxReq
    exact max_mono_s4 (Nat.le_refl _)
      (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _)
        (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _) hpr))))
  · unfold s4ExtRunGrpS CliTopBudgetReal.cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add (Nat.le_refl _)
      (max_mono_s4 (Nat.le_refl _) (max_mono_s4 (Nat.le_refl _)
        (max_mono_s4 (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpg))))

private theorem binaryKitExtMain_arith_bounds_s4 {lim : BudgetLimits}
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap) :
    s4ExtMainLive ≤ s4ExtMainPeak ∧
    CliFitsTraceArith.cliDecoupledRamNeed lim.staticBytes
      s4BinaryExtMainCum s4ExtMainPeak s4ExtMainReq
      ((s4BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ lim.physCap ∧
    CliFitsTraceArith.cliDecoupledVaNeed lim.staticBytes lim.staticCount
      s4BinaryExtMainCum s4ExtMainPeak s4ExtMainReq
      ((s4BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 := by
  have hram0 :
      CliFitsTraceArith.cliDecoupledRamNeed cliDefaultStaticBytes
        s4BinaryExtMainCum s4ExtMainPeak s4ExtMainReq
        ((s4BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB := by decide
  have hva0 :
      CliFitsTraceArith.cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
        s4BinaryExtMainCum s4ExtMainPeak s4ExtMainReq
        ((s4BinaryExtMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 := by decide
  refine ⟨?_, ?_, ?_⟩
  · unfold s4ExtMainLive s4ExtMainPeak
      CliTopBudgetSpec.cliMainTightLiveOf CliTopBudgetSpec.cliMainTightPeakOf
      CliMainPeakSpec.cliMainDeltaLive_tight CliMainPeakSpec.cliMainDeltaPeak_tight
    exact Nat.le_trans (Nat.add_le_add_left
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _)
  · exact Nat.le_trans
      (CliFitsTraceArith.cliDecoupledRamNeed_mono hsb
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  · exact Nat.le_trans
      (CliFitsTraceArith.cliDecoupledVaNeed_mono hsb hsc
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0

/-- Parametric-`decPkEnv` whole-`main` `FitsEnv fineCostModel` on
`RealCliMainBinaryEnvOf (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i` under `1 GiB`
`BudgetLimits`. -/
theorem realCliMainBinaryKitWithDecPk_fitsEnv_of_bounds [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop)
    (S_pk : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (decPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hparse).cum ≤ binaryKitW4FixedCum ∧
      (S_pk g hi_g hparse).live ≤ binaryKitW4FixedLive ∧
      (S_pk g hi_g hparse).peak ≤ binaryKitW4FixedPeak ∧
      (S_pk g hi_g hparse).maxReq ≤ binaryKitW4FixedMaxReq ∧
      (S_pk g hi_g hparse).grpS ≤ binaryKitW4FixedGrpS) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init
        (RealCliMainBinaryEnvOf (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i) := by
  intro i hi
  have hsm1024 :
      1024 ≤ LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
        fineCostModel := by
    rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]
    decide
  have hw (w : RealMainEnvAdapter.ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Heap.SeqEnv
        (CliSlotEnvelopeBridge.CliRunBinaryEnv cliIo.rd
          (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g)
          SpqrDomainCapsAux.sessionCapBytes w.g)
        (LibsignalBinary.Heap.SeqEnv (CliMainPeakSpec.M5PhaseEnv w.dirs)
          (CliMainPeakSpec.M6Env w.ok)))
      (s4ExtRunCum + CliFitsTraceArith.cliMaxDirtyEntries *
        (10 * max (4 * CliFitsTraceArith.cliMaxDirPathBytes +
          CliFitsTraceArith.cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        CliMainPeakSpec.m6DeltaCum)
      s4ExtRunLive
      (max s4ExtRunPeak
        (s4ExtRunLive +
          CliMainPeakSpec.m5DirStepDeltaPeak CliFitsTraceArith.cliMaxDirPathBytes
            CliFitsTraceArith.cliMaxAddrTextBytes))
      (max s4ExtRunMaxReq
        (max 1024 (CliMainPeakSpec.m5DirStepMaxReq CliFitsTraceArith.cliMaxDirPathBytes
          CliFitsTraceArith.cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Spk := S_pk w.g hi_g w.parse_ok
    let SE := binaryKitCalleeFineSpecs_s4 img S X W Spk hi_g w.parse_ok
    obtain ⟨h1, h2, h3, h4, _⟩ :=
      binaryKitCalleeFineSpecs_ext_bounds_s4 img S X W Spk (hCaps w.g hi_g w.parse_ok)
        hi_g w.parse_ok
    have hrun :=
      (CliSlotEnvelopeBridge.cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
        SE hi_g w.stdin_le w.parse_ok).mono h1 h2 h3 h4
    refine (hrun.seq
      ((CliSlotEnvelopeBridge.m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
        (CliMainPeakSpec.m6_phaseCredit_small1024 SeqCreditKitLemmas.fineCostModel_modelHyps
          hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono_s4 (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono_s4 (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : RealMainEnvAdapter.ValidPostSetupWitness i, w.g.i = i ∧
        LibsignalBinary.Heap.SeqEnv
          (CliSlotEnvelopeBridge.CliRunBinaryEnv cliIo.rd
            (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g)
            SpqrDomainCapsAux.sessionCapBytes w.g)
          (LibsignalBinary.Heap.SeqEnv (CliMainPeakSpec.M5PhaseEnv w.dirs)
            (CliMainPeakSpec.M6Env w.ok)) evs')
      (s4ExtRunCum + CliFitsTraceArith.cliMaxDirtyEntries *
        (10 * max (4 * CliFitsTraceArith.cliMaxDirPathBytes +
          CliFitsTraceArith.cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        CliMainPeakSpec.m6DeltaCum)
      s4ExtRunLive
      (max s4ExtRunPeak
        (s4ExtRunLive +
          CliMainPeakSpec.m5DirStepDeltaPeak CliFitsTraceArith.cliMaxDirPathBytes
            CliFitsTraceArith.cliMaxAddrTextBytes))
      (max s4ExtRunMaxReq
        (max 1024 (CliMainPeakSpec.m5DirStepMaxReq CliFitsTraceArith.cliMaxDirPathBytes
          CliFitsTraceArith.cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i)
      s4BinaryExtMainCum s4ExtMainLive s4ExtMainPeak s4ExtMainReq := by
    refine ((CliSlotEnvelopeBridge.cliMainBoundedSetup_phaseCredit_fine
        (CliDomainCaps.argv_length_le_of_cliPqInputs hi)).seq
      (optStage_phaseCredit_s4 hex)).mono ?_ ?_ ?_ ?_
    · unfold s4BinaryExtMainCum
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold s4ExtMainLive CliTopBudgetSpec.cliMainTightLiveOf
        CliMainPeakSpec.cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold s4ExtMainPeak CliTopBudgetSpec.cliMainTightPeakOf
        CliMainPeakSpec.cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold s4ExtMainReq CliTopBudgetSpec.cliMainTightReqOf
        CliMainPeakSpec.cliMainMaxReq
      have h16k :
          max 16384 (CliMainPeakSpec.m3PhaseMaxReq SpqrDomainCapsAux.msgCapBytes
            SpqrDomainCapsAux.sessionCapBytes) =
          CliMainPeakSpec.m3PhaseMaxReq SpqrDomainCapsAux.msgCapBytes
            SpqrDomainCapsAux.sessionCapBytes := by
        unfold CliMainPeakSpec.m3PhaseMaxReq SpqrDomainCapsAux.msgCapBytes
          SpqrDomainCapsAux.sessionCapBytes
        decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : RealMainEnvAdapter.ValidPostSetupWitness i, w.g.i = i ∧
        LibsignalBinary.Heap.SeqEnv
          (CliSlotEnvelopeBridge.CliRunBinaryEnv cliIo.rd
            (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g)
            SpqrDomainCapsAux.sessionCapBytes w.g)
          (LibsignalBinary.Heap.SeqEnv (CliMainPeakSpec.M5PhaseEnv w.dirs)
            (CliMainPeakSpec.M6Env w.ok)) evs')
      (s4BinaryExtRunGrpS +
        CliFitsTraceArith.cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Spk := S_pk w.g hi_g w.parse_ok
        let SE := binaryKitCalleeFineSpecs_s4 img S X W Spk hi_g w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          binaryKitCalleeFineSpecs_ext_bounds_s4 img S X W Spk (hCaps w.g hi_g w.parse_ok)
            hi_g w.parse_ok
        have hinit_sub :
            234 * FineScale + SE.initGrpS ≤ s4ExtRunGrpS - 15 * FineScale := by
          dsimp only [SE, binaryKitCalleeFineSpecs_s4]
          decide
        have hrun := RealMainBinaryEnvAdapterD3.cliRunBinaryEnv_fine_groupSpec_of_cap
          SE w.stdin_le
          (by decide : 15 * FineScale ≤ s4ExtRunGrpS)
          hinit_sub h5
        have hm5 := (CliGroupBounds.m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (LibsignalBinary.Heap.SeqEnv
              (CliSlotEnvelopeBridge.CliRunBinaryEnv cliIo.rd
                (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g)
                SpqrDomainCapsAux.sessionCapBytes w.g)
              (LibsignalBinary.Heap.SeqEnv (CliMainPeakSpec.M5PhaseEnv w.dirs)
                (CliMainPeakSpec.M6Env w.ok)))
            (s4BinaryExtRunGrpS +
              CliFitsTraceArith.cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (CliGroupBounds.m6Env_groupSpec fineCostModel w.ok))).mono
            (by unfold s4BinaryExtRunGrpS
                generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkBinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i)
      s4BinaryExtMainGrpS :=
    ((CliSlotEnvelopeBridge.cliMainBoundedSetup_fine_groupSpec
        (CliDomainCaps.argv_length_le_of_cliPqInputs hi)).seq
      (optStage_groupSpec_s4 hex_grp)).mono
      (by unfold s4BinaryExtMainGrpS
          generalize FineScale = fs; omega)
  obtain ⟨hlp, hram, hva⟩ := binaryKitExtMain_arith_bounds_s4 hsb hsc hcap1G
  exact CliFitsTraceArith.fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- Concrete `cliBudgetLimits` (`1 GiB`) whole-`main` `FitsEnv fineCostModel` on
`realCliMainBinaryKitEnvOfFixed img S X W i`. -/
theorem realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (realCliMainBinaryKitEnvOfFixed img S X W i) :=
  realCliMainBinaryKitWithDecPk_fitsEnv_of_bounds
    rfl (Nat.le_refl _) (Nat.le_refl _) (by unfold cliBudgetLimits cliOneGiB; decide)
    img S X W (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv)
    (binaryKitW4Fixed_fineSpec img S X W)
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

end LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
