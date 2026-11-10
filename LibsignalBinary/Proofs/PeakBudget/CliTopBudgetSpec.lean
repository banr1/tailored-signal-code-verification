/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget

/-!
# Whole-`main` `< 1 GiB` and `VA ≤ 2 ^ 48` Peak Budget Specification

Top-level whole-`main` allocator budget specification for the `signal-session` CLI binary on
`fineCostModel`:
1. External `PhaseGroupSpec fineCostModel` bounds for `R0OpenedEnv`, `InitArmEnv`, `R2Env`,
   `RecvArmEnv`, `RunArmEnv`, and `CliRunTightEnv`.
2. Four-slot `CliRunFineSlotSpecs` bundle and whole-`main` `PhaseCreditSpec`, `PhaseGroupSpec`,
   `FitsTrace`, and `FitsEnv` compositions.
3. Per-mode `< 1 GiB` RAM and `VA ≤ 2 ^ 48` theorems across all six CLI modes (`reject`, `keygen`,
   `init`, `send`, `recv_whisper`, `recv_prekey`), plus unified and parametric-deserialization
   residual-headroom theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec

open Arm64 ProofLib
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV RunCall addrParse cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkLen)
open LibsignalBinary.Heap
  (AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (CliPqDomainCaps dirDomainCaps_opened_own)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount
   cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds
   fitsTrace_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec cliMainEnv_groupSpec cliMainSetupEnv_le_3_fine_groupSpec
   cliMainSetupFineGrpS cliPathEnv_groupSpec phaseGroupSpec_exists_guarded)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainEnv cliMainDeltaCum_tight cliMainDeltaLive_tight cliMainDeltaPeak_tight
   cliMainMaxReq cliMain_phaseCredit_fine m3PhaseDeltaLive m3PhaseDeltaPeak
   m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOfR0Env CliRunOpenedEnv CliRunWrapperEnvs
   CliRunWrapperSlotSpecs DeserCloneStepEnv InitArmEnv JoinEnv KemDeserStepEnv
   PksmTryFromSliceEnv R0OpenedEnv R1aEnv R1bEnv R1bKpkStageEnv R1bOpkDeserStageEnv
   R1bSpkStageEnv R1cEnv R2ConcatTailEnv R2Env R3aEnv R3bEnv RecvArmEnv RecvBadEnv
   RunArmEnv SigTryFromSliceEnv SplitIdEnv SplitSignedEnv TempFileBracketEnv
   addressTryParseDeltaCum addressTryParseDeltaLive addressTryParseDeltaPeak
   addressTryParseMaxReq cliRunOpenedDeltaLive cliRunOpenedDeltaPeak cliRunOpenedMaxReq
   cliRunOpenedTightDeltaCum fineCostModel_cliRunTightHyps initArmDeltaCum
   initArmDeltaLive initArmDeltaPeak initArmMaxReq initArm_phaseCredit_of_paths
   initBundlePaths_phaseCredit join_phaseCredit pksmSliceCum pksmSliceLive
   pksmSliceMaxReq pksmSlicePeak pksmTryFromBoundedEnv_eq_sliceEnv
   r0Opened_phaseCredit_of_path r2DeltaLive r2DeltaPeak r2MaxReq r2TightDeltaCum
   r2_tight_phaseCredit r3a_phaseCredit r3b_slice_phaseCredit sigSliceCum
   sigSliceLive sigSliceMaxReq sigSlicePeak sigTryFromBoundedEnv_eq_sliceEnv
   tempFilePostCum tempFilePostLive tempFilePostMaxReq tempFilePostPeak
   utf8_address_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (deallocBytes1OfLen phaseCredit_or_freeOnly_left phaseCredit_runDispatch)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (CliRunSpqrAndInitCaps CliRunTightEnv CliRunTightEnvOf CliRunTightSpqrCaps
   c09bTightSpqrCum c09bTightSpqrLive c09bTightSpqrMaxReq c09bTightSpqrPeak
   cliIo_rd_runFiles_length_le_of_filesBounded cliRun1MiBSlotCum cliRun1MiBSlotLive
   cliRun1MiBSlotMaxReq cliRun1MiBSlotPeak cliRunOpenedDeltaLive_le_peak
   cliRunOpened_1MiB_eq_slotProfile cliRunTight_phaseCredit_fine
   r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBMaxReq r0Opened1MiBPeak
   w2CliOpenedCum w2CliOpenedLive w2CliOpenedMaxReq w2CliOpenedPeak
   w3CliOpenedCum w3CliOpenedLive w3CliOpenedMaxReq w3CliOpenedPeak)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq path_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (PhaseGroupSpec fineStepReserveOfGroups)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
  (spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak
   spqrSendTightGroupS spqrSendTightMaxReq w1CliOpenedTightSendCum
   w1CliOpenedTightSendLive w1CliOpenedTightSendMaxReq w1CliOpenedTightSendPeak)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (fineCostModel_wireGroupHyps fineCostModel_wireLowInterceptHyps
   sigTryFromCapDeltaGrpS sigTryFromDeltaGrpS_le_cap sigTryFrom_phaseGroup)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (pksmTryFromCapDeltaGrpS pksmTryFromDeltaGrpS_le_cap pksmTryFrom_phaseGroup)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget (cliConcat2Events)

/-! ## 1. `signal_session::run` (`CliRunOpenedEnv`) `PhaseGroupSpec fineCostModel` -/

private theorem grp_scale_add (a b fs : Nat) : a * fs + b * fs = (a + b) * fs :=
  (Nat.add_mul a b fs).symm

private theorem max_zero_left_le {x y : Nat} (h : x ≤ y) : max 0 x ≤ y :=
  Nat.max_le.mpr ⟨Nat.zero_le y, h⟩

private theorem max_le_of_both {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c :=
  Nat.max_le.mpr ⟨ha, hb⟩

theorem deallocBytes1OfLen_fine_groupSpec (n : Nat) :
    PhaseGroupSpec fineCostModel (· = deallocBytes1OfLen n) 0 := by
  unfold deallocBytes1OfLen
  split
  · exact PhaseGroupSpec.nil fineCostModel
  · exact PhaseGroupSpec.rustDealloc fineCostModel n 1

theorem splitIdEnv_fine_groupSpec (file : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitIdEnv file) (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))

theorem splitSignedEnv_fine_groupSpec (file : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitSignedEnv file) (6 * FineScale) := by
  have h1 := splitIdEnv_fine_groupSpec file
  have h2 := ((PhaseGroupSpec.freeOnly fineCostModel).or h1).mono
    (max_zero_left_le (Nat.le_refl _))
  exact (h1.seq h2).mono (Nat.le_of_eq (grp_scale_add 3 3 FineScale))

theorem kemDeserStepEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel KemDeserStepEnv (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel kemPkLen 1).or
    (PhaseGroupSpec.nil fineCostModel)).mono
    (max_le_of_both (Nat.le_refl _) (Nat.zero_le _))

theorem deserCloneStepEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel DeserCloneStepEnv (9 * FineScale) := by
  have h64 := PhaseGroupSpec.rustAlloc_any fineCostModel 64 1
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((h64.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _)))).mono (max_zero_left_le (Nat.le_refl _))
  have hmid := (kemDeserStepEnv_fine_groupSpec.seq htail).mono
    (Nat.le_of_eq (grp_scale_add 3 3 FineScale))
  have hmain := (h64.seq hmid).mono (Nat.le_of_eq (grp_scale_add 3 6 FineScale))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hmain).mono
    (max_zero_left_le (Nat.le_refl _))

theorem tempFileBracketEnv_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    {Body : List (BitVec 8) → List AllocEvent → Prop} {g_b : Nat}
    (hbody : ∀ bs, PhaseGroupSpec fineCostModel (Body bs) g_b) :
    PhaseGroupSpec fineCostModel (TempFileBracketEnv rd files dir name Body)
      (12 * FineScale + g_b) := by
  have hp := cliPathEnv_groupSpec fineCostModel dir name
  have hpost : PhaseGroupSpec fineCostModel
      (match rd files (pathOf dir name) with
       | .error () => fun evs2 =>
         FreeOnlyEvs evs2 ∨ SeqEnv FreeOnlyEvs (SeqEnv (· = rustAllocEvents 22 1) FreeOnlyEvs) evs2
       | .ok bs => SeqEnv
         (SeqCreditKit.ConcatEnv
           (SeqCreditKit.ConcatEnv (· = allocBytes1Events bs) (SeqEnv FreeOnlyEvs (Body bs)))
           (· = deallocBytes1OfLen bs.length)) FreeOnlyEvs)
      (3 * FineScale + g_b) := by
    cases rd files (pathOf dir name) with
    | error _ =>
      have h22 := (PhaseGroupSpec.rustAlloc_any fineCostModel 22 1).seq
        (PhaseGroupSpec.freeOnly fineCostModel)
      have herr := (PhaseGroupSpec.freeOnly fineCostModel).or
        ((PhaseGroupSpec.freeOnly fineCostModel).seq h22)
      refine herr.mono ?_
      generalize FineScale = fs
      omega
    | ok bs =>
      have ha := allocBytes1Events_groupSpec fineCostModel bs
      have hb := (PhaseGroupSpec.freeOnly fineCostModel).seq (hbody bs)
      have hc := (ha.concat hb).concat (deallocBytes1OfLen_fine_groupSpec bs.length)
      refine (hc.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono ?_
      generalize FineScale = fs
      omega
  refine (hp.seq hpost).mono ?_
  generalize FineScale = fs
  omega

theorem addressEvents_tryParse_fine_groupSpec (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (· = addressEvents uuidTryParse bs) (3 * FineScale) := by
  unfold addressEvents
  cases addrParse uuidTryParse bs with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some a => exact PhaseGroupSpec.rustAlloc_any fineCostModel a.name.length 1

theorem r0OpenedEnv_fine_groupSpec (rd : ReadRule) (files : FsFiles) :
    PhaseGroupSpec fineCostModel (R0OpenedEnv rd files) (15 * FineScale) := by
  have hbr := tempFileBracketEnv_fine_groupSpec rd files
    StoresGhost.opened.identity.own.path (utf8 "address")
    (fun ownB => ((PhaseGroupSpec.freeOnly fineCostModel).or
      (addressEvents_tryParse_fine_groupSpec ownB)).mono (max_zero_left_le (Nat.le_refl _)))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hbr).mono
    (max_zero_left_le (Nat.le_of_eq (grp_scale_add 12 3 FineScale)))

theorem r1aEnv_fine_groupSpec (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1aEnv rd files dir) (12 * FineScale) := by
  have hbr := tempFileBracketEnv_fine_groupSpec rd files dir (utf8 "identity-key")
    (fun _ => PhaseGroupSpec.freeOnly fineCostModel)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hbr).mono
    (max_zero_left_le (Nat.le_of_eq (Nat.add_zero _)))

theorem r1bEnv_fine_groupSpec (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1bEnv rd files dir) (72 * FineScale) := by
  have hopkBr := tempFileBracketEnv_fine_groupSpec rd files dir (utf8 "one-time-pre-key")
    (fun opkBs => ((PhaseGroupSpec.freeOnly fineCostModel).or
      (splitIdEnv_fine_groupSpec opkBs)).mono (max_zero_left_le (Nat.le_refl _)))
  have hopk : PhaseGroupSpec fineCostModel (R1bOpkDeserStageEnv rd files dir) (24 * FineScale) := by
    refine (hopkBr.seq deserCloneStepEnv_fine_groupSpec).mono ?_
    generalize FineScale = fs
    omega
  have hkpk : PhaseGroupSpec fineCostModel (R1bKpkStageEnv rd files dir) (42 * FineScale) := by
    have hbr := tempFileBracketEnv_fine_groupSpec rd files dir (utf8 "kyber-pre-key")
      (fun kpkBs => (splitSignedEnv_fine_groupSpec kpkBs).seq
        (((PhaseGroupSpec.freeOnly fineCostModel).or hopk).mono
          (max_zero_left_le (Nat.le_refl _))))
    refine hbr.mono ?_
    generalize FineScale = fs
    omega
  have hspk : PhaseGroupSpec fineCostModel (R1bSpkStageEnv rd files dir) (60 * FineScale) := by
    have hbr := tempFileBracketEnv_fine_groupSpec rd files dir (utf8 "signed-pre-key")
      (fun spkBs => (splitSignedEnv_fine_groupSpec spkBs).seq
        (((PhaseGroupSpec.freeOnly fineCostModel).or hkpk).mono
          (max_zero_left_le (Nat.le_refl _))))
    refine hbr.mono ?_
    generalize FineScale = fs
    omega
  have hreg := tempFileBracketEnv_fine_groupSpec rd files dir (utf8 "registration-id")
    (fun regBs => ((PhaseGroupSpec.freeOnly fineCostModel).or
      (((splitIdEnv_fine_groupSpec regBs).or hspk).mono
        (max_le_of_both (Nat.mul_le_mul_right FineScale (by decide : 3 ≤ 60)) (Nat.le_refl _)))).mono
      (max_zero_left_le (Nat.le_refl _)))
  refine hreg.mono ?_
  generalize FineScale = fs
  omega

theorem initArmEnv_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    {InitEnv : List AllocEvent → Prop} {g_init : Nat}
    (hinit : PhaseGroupSpec fineCostModel InitEnv g_init) :
    PhaseGroupSpec fineCostModel (InitArmEnv rd files dir InitEnv)
      (84 * FineScale + g_init) := by
  have hr1c : PhaseGroupSpec fineCostModel (R1cEnv InitEnv) g_init :=
    (hinit.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  have htail2 := ((PhaseGroupSpec.freeOnly fineCostModel).or hr1c).mono
    (max_zero_left_le (Nat.le_refl _))
  have htail1 := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((r1bEnv_fine_groupSpec rd files dir).seq htail2)).mono
    (max_zero_left_le (Nat.le_refl _))
  refine ((r1aEnv_fine_groupSpec rd files dir).seq htail1).mono ?_
  generalize FineScale = fs
  omega

theorem cliConcat2Events_fine_groupSpec (bs0 bs1 : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (· = cliConcat2Events bs0 bs1) (3 * FineScale) := by
  unfold cliConcat2Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact PhaseGroupSpec.rustAlloc_any fineCostModel (bs0.length + bs1.length) 1

theorem r2ConcatTailEnv_fine_groupSpec (wireOutCap : Nat) :
    PhaseGroupSpec fineCostModel (R2ConcatTailEnv wireOutCap) (3 * FineScale) := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs => ∃ bs0 : List (BitVec 8), bs0.length ≤ 1 ∧
        ∃ bs1 : List (BitVec 8), bs1.length ≤ wireOutCap ∧
          SeqEnv (· = cliConcat2Events bs0 bs1) FreeOnlyEvs evs)
      (3 * FineScale) :=
    phaseGroupSpec_exists_guarded fineCostModel fun bs0 _ =>
      phaseGroupSpec_exists_guarded fineCostModel fun bs1 _ =>
        ((cliConcat2Events_fine_groupSpec bs0 bs1).seq
          (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hex).mono
    (max_zero_left_le (Nat.le_refl _))

theorem r2Env_fine_groupSpec {EncEnv : List AllocEvent → Prop} {g_enc : Nat}
    (wireOutCap : Nat)
    (henc : PhaseGroupSpec fineCostModel EncEnv g_enc) :
    PhaseGroupSpec fineCostModel (R2Env EncEnv wireOutCap) (g_enc + 3 * FineScale) :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or
    (henc.seq (r2ConcatTailEnv_fine_groupSpec wireOutCap))).mono
    (max_zero_left_le (Nat.le_refl _))

theorem sigTryFromSlice_fine_groupSpec {rest : List (BitVec 8)} {stdinCap : Nat}
    (hrest : rest.length ≤ stdinCap) :
    PhaseGroupSpec fineCostModel (SigTryFromSliceEnv rest)
      (sigTryFromCapDeltaGrpS stdinCap) := by
  let x : TryFromGhost := ⟨0#64, rest, 0#64⟩
  have h := sigTryFrom_phaseGroup fineCostModel_wireGroupHyps x
  rw [sigTryFromBoundedEnv_eq_sliceEnv x] at h
  exact h.mono (sigTryFromDeltaGrpS_le_cap hrest)

theorem pksmTryFromSlice_fine_groupSpec {rest : List (BitVec 8)} {stdinCap : Nat}
    (hrest : rest.length ≤ stdinCap) :
    PhaseGroupSpec fineCostModel (PksmTryFromSliceEnv rest)
      (pksmTryFromCapDeltaGrpS stdinCap) := by
  let x : PksmGhost := ⟨0#64, rest, 0#64⟩
  have h := pksmTryFrom_phaseGroup fineCostModel_wireGroupHyps x
  rw [pksmTryFromBoundedEnv_eq_sliceEnv x] at h
  exact h.mono (pksmTryFromDeltaGrpS_le_cap hrest)

theorem r3aEnv_fine_groupSpec {rest : List (BitVec 8)} {DecSigEnv : List AllocEvent → Prop}
    {stdinCap g_decSig : Nat} (hrest : rest.length ≤ stdinCap)
    (hdec : PhaseGroupSpec fineCostModel DecSigEnv g_decSig) :
    PhaseGroupSpec fineCostModel (R3aEnv rest DecSigEnv)
      (sigTryFromCapDeltaGrpS stdinCap + g_decSig) := by
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((hdec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _)))).mono (max_zero_left_le (Nat.le_refl _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((sigTryFromSlice_fine_groupSpec hrest).seq htail)).mono
    (max_zero_left_le (Nat.le_refl _))

theorem r3bEnv_fine_groupSpec {rest : List (BitVec 8)} {DecPkEnv : List AllocEvent → Prop}
    {stdinCap g_decPk : Nat} (hrest : rest.length ≤ stdinCap)
    (hdec : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (R3bEnv (PksmTryFromSliceEnv rest) DecPkEnv)
      (pksmTryFromCapDeltaGrpS stdinCap + g_decPk) := by
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((hdec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _)))).mono (max_zero_left_le (Nat.le_refl _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((pksmTryFromSlice_fine_groupSpec hrest).seq htail)).mono
    (max_zero_left_le (Nat.le_refl _))

theorem recvArmEnv_fine_groupSpec {stdin : List (BitVec 8)}
    {DecSigEnv DecPkEnv : List AllocEvent → Prop}
    {stdinCap g_decSig g_decPk : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hdecSig : PhaseGroupSpec fineCostModel DecSigEnv g_decSig)
    (hdecPk : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel
      (RecvArmEnv stdin DecSigEnv PksmTryFromSliceEnv DecPkEnv)
      (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig)
        (pksmTryFromCapDeltaGrpS stdinCap + g_decPk)) := by
  unfold RecvArmEnv
  rcases stdin with _ | ⟨b, rest⟩
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  · have hrest : rest.length ≤ stdinCap := Nat.le_of_succ_le hstdin
    by_cases hb2 : b = 2#8
    · simp only [hb2, ↓reduceIte]
      exact (r3aEnv_fine_groupSpec hrest hdecSig).mono (Nat.le_max_left _ _)
    · simp only [hb2, ↓reduceIte]
      by_cases hb3 : b = 3#8
      · simp only [hb3, ↓reduceIte]
        exact (r3bEnv_fine_groupSpec hrest hdecPk).mono (Nat.le_max_right _ _)
      · simp only [hb3, ↓reduceIte]
        exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

def cliRunArmFineGrpS (stdinCap g_init g_enc g_decSig g_decPk : Nat) : Nat :=
  max (84 * FineScale + g_init)
    (max (g_enc + 3 * FineScale)
      (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig)
        (pksmTryFromCapDeltaGrpS stdinCap + g_decPk)))

def cliRunOpenedFineGrpS (stdinCap g_init g_enc g_decSig g_decPk : Nat) : Nat :=
  15 * FineScale + cliRunArmFineGrpS stdinCap g_init g_enc g_decSig g_decPk

theorem cliRunOfR0_fine_groupSpec
    {R0StageEnv ArmEnv : List AllocEvent → Prop} {g_r0 g_arm : Nat}
    (hr0 : PhaseGroupSpec fineCostModel R0StageEnv g_r0)
    (harm : PhaseGroupSpec fineCostModel ArmEnv g_arm) :
    PhaseGroupSpec fineCostModel
      (fun evs => FreeOnlyEvs evs ∨ SeqEnv R0StageEnv (SeqEnv ArmEnv JoinEnv) evs)
      (g_r0 + g_arm) := by
  have hj : PhaseGroupSpec fineCostModel JoinEnv 0 := PhaseGroupSpec.freeOnly fineCostModel
  have haj := (harm.seq hj).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or (hr0.seq haj)).mono
    (max_zero_left_le (Nat.le_refl _))

/-! ## 2. `fineCostModel` Slot Bundles and Whole-`main` Discharge -/

/-- Single-slot `fineCostModel` credit and group bundle. -/
structure SingleSlotFineSpec (SlotEnv : List AllocEvent → Prop) where
  (cumB liveB peakB maxReq grpS : Nat)
  credit_spec : PhaseCreditSpec fineCostModel SlotEnv cumB liveB peakB maxReq
  live_le_peak : liveB ≤ peakB
  group_spec : PhaseGroupSpec fineCostModel SlotEnv grpS

/-- Four-slot `fineCostModel` credit and group bundle for `CliRunWrapperEnvs` (`initiate`, `encrypt`, `decryptSignal`, `decryptPrekey`). -/
structure CliRunFineSlotSpecs (W : CliRunWrapperEnvs) where
  (initCum initLive initPeak initMaxReq initGrpS : Nat)
  init_spec : PhaseCreditSpec fineCostModel W.initEnv initCum initLive initPeak initMaxReq
  init_lp : initLive ≤ initPeak
  init_grp : PhaseGroupSpec fineCostModel W.initEnv initGrpS
  (encCum encLive encPeak encMaxReq encGrpS : Nat)
  enc_spec : PhaseCreditSpec fineCostModel W.encEnv encCum encLive encPeak encMaxReq
  enc_lp : encLive ≤ encPeak
  enc_grp : PhaseGroupSpec fineCostModel W.encEnv encGrpS
  (decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat)
  decSig_spec : PhaseCreditSpec fineCostModel W.decSigEnv decSigCum decSigLive decSigPeak decSigMaxReq
  decSig_lp : decSigLive ≤ decSigPeak
  decSig_grp : PhaseGroupSpec fineCostModel W.decSigEnv decSigGrpS
  (decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat)
  decPk_spec : PhaseCreditSpec fineCostModel W.decPkEnv decPkCum decPkLive decPkPeak decPkMaxReq
  decPk_lp : decPkLive ≤ decPkPeak
  decPk_grp : PhaseGroupSpec fineCostModel W.decPkEnv decPkGrpS

def CliRunFineSlotSpecs.toWrapperSlotSpecs {W : CliRunWrapperEnvs}
    (SW : CliRunFineSlotSpecs W) : CliRunWrapperSlotSpecs fineCostModel W where
  initCum := SW.initCum
  initLive := SW.initLive
  initPeak := SW.initPeak
  initMaxReq := SW.initMaxReq
  init_spec := SW.init_spec
  init_lp := SW.init_lp
  encCum := SW.encCum
  encLive := SW.encLive
  encPeak := SW.encPeak
  encMaxReq := SW.encMaxReq
  enc_spec := SW.enc_spec
  enc_lp := SW.enc_lp
  decSigCum := SW.decSigCum
  decSigLive := SW.decSigLive
  decSigPeak := SW.decSigPeak
  decSigMaxReq := SW.decSigMaxReq
  decSig_spec := SW.decSig_spec
  decSig_lp := SW.decSig_lp
  decPkCum := SW.decPkCum
  decPkLive := SW.decPkLive
  decPkPeak := SW.decPkPeak
  decPkMaxReq := SW.decPkMaxReq
  decPk_spec := SW.decPk_spec
  decPk_lp := SW.decPk_lp

/-- Whole-`run` `PhaseGroupSpec fineCostModel` for `CliRunTightEnvOf W`. -/
theorem cliRunTight_fine_groupSpec
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap wireOutCap : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hstdin : g.i.stdin.length ≤ stdinCap) :
    PhaseGroupSpec fineCostModel (CliRunTightEnvOf W wireOutCap g)
      (cliRunOpenedFineGrpS stdinCap SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS) := by
  have harm : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs wireOutCap g.i.stdin g.c)
      (cliRunArmFineGrpS stdinCap SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS) := by
    cases g.c with
    | keygen _ _ =>
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | init _ dir =>
      exact (initArmEnv_fine_groupSpec cliIo.rd (runFiles g.i) dir SW.init_grp).mono
        (Nat.le_max_left _ _)
    | send _ =>
      exact (r2Env_fine_groupSpec wireOutCap SW.enc_grp).mono
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    | recv _ =>
      exact (recvArmEnv_fine_groupSpec hstdin SW.decSig_grp SW.decPk_grp).mono
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact cliRunOfR0_fine_groupSpec (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm

/-- Whole-`run` `1 MiB` `PhaseCreditSpec fineCostModel` for `CliRunTightEnv W`. -/
theorem cliRunTight_1MiB_fine_phaseCredit
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    (SW : CliRunFineSlotSpecs (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (cliRun1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum)
      (cliRun1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive)
      (cliRun1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak)
      (cliRun1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq) := by
  have h := cliRunTight_phaseCredit_fine (wireOutCap := sessionCapBytes)
    SW.toWrapperSlotSpecs hcaps hspqr
  obtain ⟨hc, hl, hp, hr⟩ := cliRunOpened_1MiB_eq_slotProfile SW.toWrapperSlotSpecs
  dsimp only [CliRunFineSlotSpecs.toWrapperSlotSpecs] at h hc hl hp hr
  rwa [hc, hl, hp, hr] at h

/-- Closed-form whole-`main` `Δcum` at `1 MiB` / `cliMaxDirtyEntries = 4`, `maxDir = 64`, `maxName = 64`. -/
def cliMainTightCumOf (runCumCap : Nat) : Nat :=
  cliMainDeltaCum_tight runCumCap cliMaxDirtyEntries cliMaxDirPathBytes cliMaxAddrTextBytes

/-- Closed-form whole-`main` `Δlive` at `(msgCapBytes, sessionCapBytes)`. -/
def cliMainTightLiveOf (runLiveCap : Nat) : Nat :=
  cliMainDeltaLive_tight msgCapBytes sessionCapBytes runLiveCap

/-- Closed-form whole-`main` `Δpeak` at `(msgCapBytes, sessionCapBytes, 64, 64)`. -/
def cliMainTightPeakOf (runLiveCap runPeakCap : Nat) : Nat :=
  cliMainDeltaPeak_tight msgCapBytes sessionCapBytes runLiveCap runPeakCap
    cliMaxDirPathBytes cliMaxAddrTextBytes

/-- Closed-form whole-`main` `maxReq` at `(msgCapBytes, sessionCapBytes, 64, 64)`. -/
def cliMainTightReqOf (runReqCap : Nat) : Nat :=
  cliMainMaxReq msgCapBytes sessionCapBytes runReqCap cliMaxDirPathBytes cliMaxAddrTextBytes

/-- Closed-form whole-`main` scaled group count `grpS` at `cliMaxDirtyEntries = 4`. -/
def cliMainTightGrpSOf (runGrpSCap : Nat) : Nat :=
  cliMainSetupFineGrpS + runGrpSCap + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

/-- Closed-form whole-`main` integer group ceiling `(grpS + FineScale - 1) / FineScale`. -/
def cliMainTightGrpCountOf (runGrpSCap : Nat) : Nat :=
  (cliMainTightGrpSOf runGrpSCap + FineScale - 1) / FineScale

/-- Closed-form whole-`main` `stepReserve` bound from `(runReqCap, runGrpSCap)`. -/
def cliMainTightStepReserveOf (runReqCap runGrpSCap : Nat) : Nat :=
  fineStepReserveOfGroups (cliMainTightReqOf runReqCap) 16 (cliMainTightGrpCountOf runGrpSCap)

/-- Closed-form whole-`main` physical RAM need (`cliDecoupledRamNeed`). -/
def cliMainTightRamNeedOf (runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat) : Nat :=
  cliDecoupledRamNeed cliDefaultStaticBytes
    (cliMainTightCumOf runCumCap)
    (cliMainTightPeakOf runLiveCap runPeakCap)
    (cliMainTightReqOf runReqCap)
    (cliMainTightGrpCountOf runGrpSCap)

/-- Closed-form whole-`main` 48-bit virtual address need (`cliDecoupledVaNeed`). -/
def cliMainTightVaNeedOf (runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat) : Nat :=
  cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
    (cliMainTightCumOf runCumCap)
    (cliMainTightPeakOf runLiveCap runPeakCap)
    (cliMainTightReqOf runReqCap)
    (cliMainTightGrpCountOf runGrpSCap)

private theorem cliMainDeltaCum_tight_mono {c1 c2 d1 d2 maxDir maxName : Nat}
    (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    cliMainDeltaCum_tight c1 d1 maxDir maxName ≤ cliMainDeltaCum_tight c2 d2 maxDir maxName := by
  unfold cliMainDeltaCum_tight
  have hm :
      d1 * (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) ≤
        d2 * (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) :=
    Nat.mul_le_mul_right _ hd
  omega

private theorem cliMainDeltaLive_le_tightPeak_of_le
    {stdinCap fileCap l1 l2 p2 maxDir maxName : Nat} (hl : l1 ≤ l2) :
    cliMainDeltaLive_tight stdinCap fileCap l1 ≤
      cliMainDeltaPeak_tight stdinCap fileCap l2 p2 maxDir maxName := by
  unfold cliMainDeltaLive_tight cliMainDeltaPeak_tight
  have h1 : l1 ≤ max p2 (l2 + m5DirStepDeltaPeak maxDir maxName) :=
    Nat.le_trans hl (Nat.le_trans (Nat.le_add_right l2 _) (Nat.le_max_right _ _))
  exact Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)

private theorem cliMainDeltaPeak_tight_mono
    {stdinCap fileCap l1 l2 p1 p2 maxDir maxName : Nat}
    (hl : l1 ≤ l2) (hp : p1 ≤ p2) :
    cliMainDeltaPeak_tight stdinCap fileCap l1 p1 maxDir maxName ≤
      cliMainDeltaPeak_tight stdinCap fileCap l2 p2 maxDir maxName := by
  unfold cliMainDeltaPeak_tight
  have hinner :
      max p1 (l1 + m5DirStepDeltaPeak maxDir maxName) ≤
        max p2 (l2 + m5DirStepDeltaPeak maxDir maxName) :=
    Nat.max_le.mpr
      ⟨Nat.le_trans hp (Nat.le_max_left _ _),
       Nat.le_trans (Nat.add_le_add_right hl _) (Nat.le_max_right _ _)⟩
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans (Nat.add_le_add_left hinner _) (Nat.le_max_right _ _)⟩

private theorem cliMainMaxReq_mono {stdinCap fileCap r1 r2 maxDir maxName : Nat}
    (hr : r1 ≤ r2) :
    cliMainMaxReq stdinCap fileCap r1 maxDir maxName ≤
      cliMainMaxReq stdinCap fileCap r2 maxDir maxName := by
  unfold cliMainMaxReq
  have hinner :
      max r1 (max 1024 (m5DirStepMaxReq maxDir maxName)) ≤
        max r2 (max 1024 (m5DirStepMaxReq maxDir maxName)) :=
    Nat.max_le.mpr ⟨Nat.le_trans hr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans hinner (Nat.le_max_right _ _)⟩

private theorem cliMainGrpCount_le_of_le {gRun gCap numDirty : Nat}
    (hg : gRun ≤ gCap) (hd : numDirty ≤ cliMaxDirtyEntries) :
    (cliMainSetupFineGrpS + gRun + numDirty * (12 * FineScale) + 3 * FineScale +
      FineScale - 1) / FineScale ≤ cliMainTightGrpCountOf gCap := by
  unfold cliMainTightGrpCountOf cliMainTightGrpSOf
  have hm : numDirty * (12 * FineScale) ≤ cliMaxDirtyEntries * (12 * FineScale) :=
    Nat.mul_le_mul_right _ hd
  exact Nat.div_le_div_right (by omega)

/-- Whole-`main` `PhaseCreditSpec` and `PhaseGroupSpec` composition on `fineCostModel`. -/
theorem cliMain_fine_credit_and_groups_of_run
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {runCum runLive runPeak runMaxReq runGrpS : Nat}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (hrunSpec : PhaseCreditSpec fineCostModel (RunEnv g) runCum runLive runPeak runMaxReq)
    (hrunGrp : PhaseGroupSpec fineCostModel (RunEnv g) runGrpS) :
    PhaseCreditSpec fineCostModel (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (cliMainTightCumOf runCum)
      (cliMainTightLiveOf runLive)
      (cliMainTightPeakOf runLive runPeak)
      (cliMainTightReqOf runMaxReq) ∧
    PhaseGroupSpec fineCostModel (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (cliMainTightGrpSOf runGrpS) := by
  have hcr := cliMain_phaseCredit_fine
    (uuidParse := uuidParse) (needStdin := needStdin) (ok := ok)
    fineCostModel_modelHyps hcaps haddr hdirs.2 hrunSpec
  have hcr' :
      PhaseCreditSpec fineCostModel (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
        (cliMainTightCumOf runCum)
        (cliMainTightLiveOf runLive)
        (cliMainTightPeakOf runLive runPeak)
        (cliMainTightReqOf runMaxReq) :=
    hcr.mono
      (cliMainDeltaCum_tight_mono (Nat.le_refl _) hdirs.1)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hgr := cliMainEnv_groupSpec fineCostModel (dirs := dirs) (ok := ok)
    (cliMainSetupEnv_le_3_fine_groupSpec uuidParse hcaps.argv_le addrOpt needStdin) hrunGrp
  have hgr' :
      PhaseGroupSpec fineCostModel (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
        (cliMainTightGrpSOf runGrpS) := by
    refine hgr.mono ?_
    unfold cliMainTightGrpSOf
    have hm :
        ((dirs.map (fun dn => dn.2.length)).sum) * (12 * FineScale) ≤
          cliMaxDirtyEntries * (12 * FineScale) :=
      Nat.mul_le_mul_right _ hdirs.1
    omega
  exact ⟨hcr', hgr'⟩

/-- Whole-`main` `FitsTrace fineCostModel` discharge from `RunEnv` bounds. -/
theorem cliMain_fitsTrace_of_runFineBounds
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {runCum runLive runPeak runMaxReq runGrpS : Nat}
    {runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (hrunSpec : PhaseCreditSpec fineCostModel (RunEnv g) runCum runLive runPeak runMaxReq)
    (hrunGrp : PhaseGroupSpec fineCostModel (RunEnv g) runGrpS)
    (hrc : runCum ≤ runCumCap)
    (hrl : runLive ≤ runLiveCap)
    (hrp : runPeak ≤ runPeakCap)
    (hrr : runMaxReq ≤ runReqCap)
    (hrg : runGrpS ≤ runGrpSCap)
    (hramCap : cliMainTightRamNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ cliOneGiB)
    (hvaCap : cliMainTightVaNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim (cliMainTightStepReserveOf runReqCap runGrpSCap) fullLog := by
  have hcr := cliMain_phaseCredit_fine
    (uuidParse := uuidParse) (needStdin := needStdin) (ok := ok)
    fineCostModel_modelHyps hcaps haddr hdirs.2 hrunSpec
  have hgr := cliMainEnv_groupSpec fineCostModel (dirs := dirs) (ok := ok)
    (cliMainSetupEnv_le_3_fine_groupSpec uuidParse hcaps.argv_le addrOpt needStdin) hrunGrp
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        (cliMainTightCumOf runCumCap)
        (cliMainTightPeakOf runLiveCap runPeakCap)
        (cliMainTightReqOf runReqCap)
        (cliMainTightGrpCountOf runGrpSCap) ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hramCap hcap)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (cliMainTightCumOf runCumCap)
        (cliMainTightPeakOf runLiveCap runPeakCap)
        (cliMainTightReqOf runReqCap)
        (cliMainTightGrpCountOf runGrpSCap) ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hvaCap
  exact fitsTrace_fineCostModel_of_group_literal_bounds
    hcr hgr
    (cliMainDeltaCum_tight_mono hrc hdirs.1)
    (cliMainDeltaLive_le_tightPeak_of_le hrl)
    (cliMainDeltaPeak_tight_mono hrl hrp)
    (cliMainMaxReq_mono hrr)
    (cliMainGrpCount_le_of_le hrg hdirs.1)
    henf hram hva hEnv

/-- Whole-`main` `FitsEnv fineCostModel` discharge from `RunEnv` bounds. -/
theorem cliMain_fitsEnv_of_runFineBounds
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {runCum runLive runPeak runMaxReq runGrpS : Nat}
    {runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (hrunSpec : PhaseCreditSpec fineCostModel (RunEnv g) runCum runLive runPeak runMaxReq)
    (hrunGrp : PhaseGroupSpec fineCostModel (RunEnv g) runGrpS)
    (hrc : runCum ≤ runCumCap)
    (hrl : runLive ≤ runLiveCap)
    (hrp : runPeak ≤ runPeakCap)
    (hrr : runMaxReq ≤ runReqCap)
    (hrg : runGrpS ≤ runGrpSCap)
    (hramCap : cliMainTightRamNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ cliOneGiB)
    (hvaCap : cliMainTightVaNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok) := by
  have hcr := cliMain_phaseCredit_fine
    (uuidParse := uuidParse) (needStdin := needStdin) (ok := ok)
    fineCostModel_modelHyps hcaps haddr hdirs.2 hrunSpec
  have hgr := cliMainEnv_groupSpec fineCostModel (dirs := dirs) (ok := ok)
    (cliMainSetupEnv_le_3_fine_groupSpec uuidParse hcaps.argv_le addrOpt needStdin) hrunGrp
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        (cliMainTightCumOf runCumCap)
        (cliMainTightPeakOf runLiveCap runPeakCap)
        (cliMainTightReqOf runReqCap)
        (cliMainTightGrpCountOf runGrpSCap) ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hramCap hcap)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (cliMainTightCumOf runCumCap)
        (cliMainTightPeakOf runLiveCap runPeakCap)
        (cliMainTightReqOf runReqCap)
        (cliMainTightGrpCountOf runGrpSCap) ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hvaCap
  exact fitsEnv_fineCostModel_of_group_literal_bounds
    hcr hgr
    (cliMainDeltaCum_tight_mono hrc hdirs.1)
    (cliMainDeltaLive_le_tightPeak_of_le hrl)
    (cliMainDeltaPeak_tight_mono hrl hrp)
    (cliMainMaxReq_mono hrr)
    (cliMainGrpCount_le_of_le hrg hdirs.1)
    henf hram hva

/-! ## 3. Per-Mode Whole-`main` `< 2 ^ 30` (`1 GiB`) & `VA ≤ 2 ^ 48` Theorems (All 6 Modes) -/

private theorem r0Opened_1MiB_fine_phaseCredit {g : RunCall}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i) :
    PhaseCreditSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
  r0Opened_phaseCredit_of_path fineCostModel_modelHyps
    (path_phaseCredit fineCostModel_modelHyps
      dirDomainCaps_opened_own.path_len_le utf8_address_length_le)
    (fun bs hrd => cliIo_rd_runFiles_length_le_of_filesBounded hcaps.files_bounded _ bs hrd)

private theorem cliRunOfR0_singleArm_fine_phaseCredit
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {c_arm l_arm p_arm r_arm : Nat}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (harm : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      c_arm l_arm p_arm r_arm)
    (hlp_arm : l_arm ≤ p_arm) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (r0Opened1MiBCum + c_arm)
      (r0Opened1MiBLive + l_arm)
      (max r0Opened1MiBPeak (r0Opened1MiBLive + p_arm))
      (max r0Opened1MiBMaxReq r_arm) :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ h => h)
    (phaseCredit_runDispatch fineCostModel_modelHyps
      (r0Opened_1MiB_fine_phaseCredit hcaps)
      harm (fun _ h => h) hlp_arm)

/-! ### 3.0 Mode 0: `reject` (Early Exit `RunEnv = fun _ => FreeOnlyEvs`) -/

def CliRejectRunEnv (_g : RunCall) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs

def cliRejectStepReserve : Nat := cliMainTightStepReserveOf 0 0

theorem cliMain_reject_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse CliRejectRunEnv g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRejectStepReserve fullLog :=
  cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)
    (PhaseGroupSpec.freeOnly fineCostModel)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0)
    (by decide) (by decide) hEnv

theorem cliMain_reject_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse CliRejectRunEnv g addrOpt needStdin dirs ok) :=
  cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)
    (PhaseGroupSpec.freeOnly fineCostModel)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 0)
    (by decide) (by decide)

/-! ### 3.1 Mode 1: `keygen` (`g.c = .keygen me n`, Zero Stateful Slot Assumptions) -/

def cliKeygenRunGrpSCap : Nat := 15 * FineScale
def cliKeygenStepReserve : Nat := cliMainTightStepReserveOf r0Opened1MiBMaxReq cliKeygenRunGrpSCap

theorem cliRunTight_keygen_fine_specs
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {me : AddrV} {n : Nat}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .keygen me n) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq ∧
    PhaseGroupSpec fineCostModel (CliRunTightEnv W g) cliKeygenRunGrpSCap := by
  have harm_cr : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      0 0 0 0 := by
    unfold RunArmEnv; rw [hc]
    exact PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have harm_gr : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c) 0 := by
    unfold RunArmEnv; rw [hc]
    exact PhaseGroupSpec.freeOnly fineCostModel
  have hcr : PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    (cliRunOfR0_singleArm_fine_phaseCredit hcaps harm_cr (Nat.le_refl 0)).mono
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (Nat.add_zero _))
      (by decide)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
  have hgr : PhaseGroupSpec fineCostModel (CliRunTightEnv W g) cliKeygenRunGrpSCap :=
    (cliRunOfR0_fine_groupSpec (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm_gr).mono
      (Nat.le_of_eq (Nat.add_zero _))
  exact ⟨hcr, hgr⟩

theorem cliMain_keygen_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {me : AddrV} {n : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .keygen me n)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliKeygenStepReserve fullLog := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_keygen_fine_specs (W := W) hcaps hc
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) hEnv

theorem cliMain_keygen_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {me : AddrV} {n : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .keygen me n)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_keygen_fine_specs (W := W) hcaps hc
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide)

/-! ### 3.2 Mode 2: `init` (`g.c = .init peer dir`, W3 `initiate`) -/

def cliInitSlotCumCap : Nat := 29000000
def cliInitSlotLiveCap : Nat := 16000000
def cliInitSlotPeakCap : Nat := 17000000
def cliInitSlotReqCap : Nat := 4194304
def cliInitSlotGrpSCap : Nat := 7000 * FineScale

def cliInitRunCumCap : Nat :=
  r0Opened1MiBCum + initArmDeltaCum (pathDeltaCum 26 16) 1637 cliInitSlotCumCap
def cliInitRunLiveCap : Nat :=
  r0Opened1MiBLive + initArmDeltaLive (pathDeltaLive 26 16) cliInitSlotLiveCap
def cliInitRunPeakCap : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 cliInitSlotPeakCap)
def cliInitRunReqCap : Nat :=
  max r0Opened1MiBMaxReq (initArmMaxReq (pathMaxReq 26 16) 1637 cliInitSlotReqCap)
def cliInitRunGrpSCap : Nat := 99 * FineScale + cliInitSlotGrpSCap
def cliInitStepReserve : Nat := cliMainTightStepReserveOf cliInitRunReqCap cliInitRunGrpSCap

theorem cliRunTight_init_fine_specs
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV} {dir : List (BitVec 8)}
    (SInit : SingleSlotFineSpec (W g).initEnv)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (hc : g.c = .init peer dir) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (r0Opened1MiBCum + initArmDeltaCum (pathDeltaCum 26 16) 1637 SInit.cumB)
      (r0Opened1MiBLive + initArmDeltaLive (pathDeltaLive 26 16) SInit.liveB)
      (max r0Opened1MiBPeak
        (r0Opened1MiBLive +
          initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SInit.peakB))
      (max r0Opened1MiBMaxReq (initArmMaxReq (pathMaxReq 26 16) 1637 SInit.maxReq)) ∧
    PhaseGroupSpec fineCostModel (CliRunTightEnv W g) (99 * FineScale + SInit.grpS) := by
  have hpaths := initBundlePaths_phaseCredit fineCostModel_modelHyps hspqr.init_caps
  obtain ⟨hpIk, hpReg, hpSpk, hpKpk, hpOpk, hbc⟩ := hpaths peer dir hc
  have harm_cr : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (initArmDeltaCum (pathDeltaCum 26 16) 1637 SInit.cumB)
      (initArmDeltaLive (pathDeltaLive 26 16) SInit.liveB)
      (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SInit.peakB)
      (initArmMaxReq (pathMaxReq 26 16) 1637 SInit.maxReq) := by
    unfold RunArmEnv; rw [hc]
    exact initArm_phaseCredit_of_paths fineCostModel_modelHyps
      hpIk hpReg hpSpk hpKpk hpOpk hbc SInit.credit_spec SInit.live_le_peak
  have hlp_arm :
      initArmDeltaLive (pathDeltaLive 26 16) SInit.liveB ≤
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SInit.peakB :=
    Nat.le_trans
      (Nat.add_le_add_left
        (Nat.le_trans (Nat.add_le_add_left SInit.live_le_peak _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  have harm_gr : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (84 * FineScale + SInit.grpS) := by
    unfold RunArmEnv; rw [hc]
    exact initArmEnv_fine_groupSpec cliIo.rd (runFiles g.i) dir SInit.group_spec
  have hgr : PhaseGroupSpec fineCostModel (CliRunTightEnv W g) (99 * FineScale + SInit.grpS) :=
    (cliRunOfR0_fine_groupSpec
      (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm_gr).mono
      (by generalize FineScale = fs; omega)
  exact ⟨cliRunOfR0_singleArm_fine_phaseCredit hcaps harm_cr hlp_arm, hgr⟩

private theorem initRun_bounds_mono {c l p r g : Nat}
    (hc : c ≤ cliInitSlotCumCap) (hl : l ≤ cliInitSlotLiveCap)
    (hp : p ≤ cliInitSlotPeakCap) (hr : r ≤ cliInitSlotReqCap)
    (hg : g ≤ cliInitSlotGrpSCap) :
    r0Opened1MiBCum + initArmDeltaCum (pathDeltaCum 26 16) 1637 c ≤ cliInitRunCumCap ∧
    r0Opened1MiBLive + initArmDeltaLive (pathDeltaLive 26 16) l ≤ cliInitRunLiveCap ∧
    max r0Opened1MiBPeak
      (r0Opened1MiBLive +
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 p) ≤ cliInitRunPeakCap ∧
    max r0Opened1MiBMaxReq (initArmMaxReq (pathMaxReq 26 16) 1637 r) ≤ cliInitRunReqCap ∧
    99 * FineScale + g ≤ cliInitRunGrpSCap := by
  refine ⟨?_, ?_, ?_, ?_, Nat.add_le_add_left hg _⟩
  · unfold cliInitRunCumCap initArmDeltaCum; omega
  · unfold cliInitRunLiveCap initArmDeltaLive; omega
  · unfold cliInitRunPeakCap initArmDeltaPeak
    have h1 :
        max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
          (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + p) ≤
        max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
          (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + cliInitSlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left hp _) (Nat.le_max_right _ _)⟩
    have h2 :
        max (CliRunArmsPeak.r1aDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
          (CliRunArmsPeak.r1aDeltaLive (pathDeltaLive 26 16) +
            max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
              (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + p)) ≤
        max (CliRunArmsPeak.r1aDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
          (CliRunArmsPeak.r1aDeltaLive (pathDeltaLive 26 16) +
            max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
              (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + cliInitSlotPeakCap)) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (Nat.add_le_add_left h2 _) (Nat.le_max_right _ _)⟩
  · unfold cliInitRunReqCap initArmMaxReq
    have h1 :
        max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) r ≤
          max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) cliInitSlotReqCap :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩
    have h2 :
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) r) ≤
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) cliInitSlotReqCap) :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h1 (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h2 (Nat.le_max_right _ _)⟩

theorem cliMain_init_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {dir : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SInit : SingleSlotFineSpec (W g).initEnv)
    (hSlot : SInit.cumB ≤ cliInitSlotCumCap ∧ SInit.liveB ≤ cliInitSlotLiveCap ∧
      SInit.peakB ≤ cliInitSlotPeakCap ∧ SInit.maxReq ≤ cliInitSlotReqCap ∧
      SInit.grpS ≤ cliInitSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (hc : g.c = .init peer dir)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliInitStepReserve fullLog := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_init_fine_specs SInit hcaps hspqr hc
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    initRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

theorem cliMain_init_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {dir : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SInit : SingleSlotFineSpec (W g).initEnv)
    (hSlot : SInit.cumB ≤ cliInitSlotCumCap ∧ SInit.liveB ≤ cliInitSlotLiveCap ∧
      SInit.peakB ≤ cliInitSlotPeakCap ∧ SInit.maxReq ≤ cliInitSlotReqCap ∧
      SInit.grpS ≤ cliInitSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (hc : g.c = .init peer dir)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_init_fine_specs SInit hcaps hspqr hc
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    initRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

/-! ### 3.3 Mode 3: `send` (`g.c = .send peer`, W1 + `SpqrSendTightSpec`) -/

def cliSendSlotCumCap : Nat := 72000000
def cliSendSlotLiveCap : Nat := 18000000
def cliSendSlotPeakCap : Nat := 22000000
def cliSendSlotReqCap : Nat := 4194304
def cliSendSlotGrpSCap : Nat := 13000 * FineScale

/-- Checks that `w1CliOpenedTightSend*` fits inside `cliSendSlot*Cap` at `1 MiB` `ptext` / `2 MiB` session. -/
theorem w1CliOpenedTightSend_1MiB_deser0_le_caps :
    w1CliOpenedTightSendCum msgCapBytes 9619 sessionCapBytes 0 12000000 10000000 10000000 ≤
      cliSendSlotCumCap ∧
    w1CliOpenedTightSendLive msgCapBytes sessionCapBytes 0 3000000 3000000 3000000 ≤
      cliSendSlotLiveCap ∧
    w1CliOpenedTightSendPeak msgCapBytes sessionCapBytes 0 0
      3000000 5000000 3000000 5000000 5000000 ≤ cliSendSlotPeakCap ∧
    w1CliOpenedTightSendMaxReq msgCapBytes sessionCapBytes 0
      sessionCapBytes sessionCapBytes sessionCapBytes ≤ cliSendSlotReqCap ∧
    24 * FineScale + spqrSendTightGroupS + 1500 * FineScale ≤ cliSendSlotGrpSCap := by
  decide

def cliSendRunCumCap : Nat :=
  r0Opened1MiBCum + r2TightDeltaCum cliSendSlotCumCap sessionCapBytes
def cliSendRunLiveCap : Nat :=
  r0Opened1MiBLive + r2DeltaLive fineCostModel cliSendSlotLiveCap sessionCapBytes
def cliSendRunPeakCap : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      r2DeltaPeak fineCostModel cliSendSlotLiveCap cliSendSlotPeakCap sessionCapBytes)
def cliSendRunReqCap : Nat :=
  max r0Opened1MiBMaxReq (r2MaxReq cliSendSlotReqCap sessionCapBytes)
def cliSendRunGrpSCap : Nat := 18 * FineScale + cliSendSlotGrpSCap
def cliSendStepReserve : Nat := cliMainTightStepReserveOf cliSendRunReqCap cliSendRunGrpSCap

theorem cliRunTight_send_fine_specs
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV}
    (SEnc : SingleSlotFineSpec (W g).encEnv)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .send peer) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (r0Opened1MiBCum + r2TightDeltaCum SEnc.cumB sessionCapBytes)
      (r0Opened1MiBLive + r2DeltaLive fineCostModel SEnc.liveB sessionCapBytes)
      (max r0Opened1MiBPeak
        (r0Opened1MiBLive + r2DeltaPeak fineCostModel SEnc.liveB SEnc.peakB sessionCapBytes))
      (max r0Opened1MiBMaxReq (r2MaxReq SEnc.maxReq sessionCapBytes)) ∧
    PhaseGroupSpec fineCostModel (CliRunTightEnv W g) (18 * FineScale + SEnc.grpS) := by
  have harm_cr : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (r2TightDeltaCum SEnc.cumB sessionCapBytes)
      (r2DeltaLive fineCostModel SEnc.liveB sessionCapBytes)
      (r2DeltaPeak fineCostModel SEnc.liveB SEnc.peakB sessionCapBytes)
      (r2MaxReq SEnc.maxReq sessionCapBytes) := by
    unfold RunArmEnv; rw [hc]
    exact r2_tight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
      SEnc.credit_spec
  have hlp_arm :
      r2DeltaLive fineCostModel SEnc.liveB sessionCapBytes ≤
        r2DeltaPeak fineCostModel SEnc.liveB SEnc.peakB sessionCapBytes :=
    Nat.le_max_right _ _
  have harm_gr : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (SEnc.grpS + 3 * FineScale) := by
    unfold RunArmEnv; rw [hc]
    exact r2Env_fine_groupSpec sessionCapBytes SEnc.group_spec
  have hgr : PhaseGroupSpec fineCostModel (CliRunTightEnv W g) (18 * FineScale + SEnc.grpS) :=
    (cliRunOfR0_fine_groupSpec
      (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm_gr).mono
      (by generalize FineScale = fs; omega)
  exact ⟨cliRunOfR0_singleArm_fine_phaseCredit hcaps harm_cr hlp_arm, hgr⟩

private theorem sendRun_bounds_mono {c l p r g : Nat}
    (hc : c ≤ cliSendSlotCumCap) (hl : l ≤ cliSendSlotLiveCap)
    (hp : p ≤ cliSendSlotPeakCap) (hr : r ≤ cliSendSlotReqCap)
    (hg : g ≤ cliSendSlotGrpSCap) :
    r0Opened1MiBCum + r2TightDeltaCum c sessionCapBytes ≤ cliSendRunCumCap ∧
    r0Opened1MiBLive + r2DeltaLive fineCostModel l sessionCapBytes ≤ cliSendRunLiveCap ∧
    max r0Opened1MiBPeak
      (r0Opened1MiBLive + r2DeltaPeak fineCostModel l p sessionCapBytes) ≤ cliSendRunPeakCap ∧
    max r0Opened1MiBMaxReq (r2MaxReq r sessionCapBytes) ≤ cliSendRunReqCap ∧
    18 * FineScale + g ≤ cliSendRunGrpSCap := by
  refine ⟨?_, ?_, ?_, ?_, Nat.add_le_add_left hg _⟩
  · unfold cliSendRunCumCap r2TightDeltaCum; omega
  · unfold cliSendRunLiveCap r2DeltaLive; omega
  · unfold cliSendRunPeakCap r2DeltaPeak
    have h1 :
        max p (l + CliRunArmsPeak.r2TailPeak fineCostModel sessionCapBytes) ≤
          max cliSendSlotPeakCap
            (cliSendSlotLiveCap + CliRunArmsPeak.r2TailPeak fineCostModel sessionCapBytes) :=
      Nat.max_le.mpr
        ⟨Nat.le_trans hp (Nat.le_max_left _ _),
         Nat.le_trans (Nat.add_le_add_right hl _) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
  · unfold cliSendRunReqCap r2MaxReq
    have h1 :
        max r (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) ≤
          max cliSendSlotReqCap (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) :=
      Nat.max_le.mpr ⟨Nat.le_trans hr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h1 (Nat.le_max_right _ _)⟩

theorem cliMain_send_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SEnc : SingleSlotFineSpec (W g).encEnv)
    (hSlot : SEnc.cumB ≤ cliSendSlotCumCap ∧ SEnc.liveB ≤ cliSendSlotLiveCap ∧
      SEnc.peakB ≤ cliSendSlotPeakCap ∧ SEnc.maxReq ≤ cliSendSlotReqCap ∧
      SEnc.grpS ≤ cliSendSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .send peer)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliSendStepReserve fullLog := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_send_fine_specs SEnc hcaps hc
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    sendRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

theorem cliMain_send_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SEnc : SingleSlotFineSpec (W g).encEnv)
    (hSlot : SEnc.cumB ≤ cliSendSlotCumCap ∧ SEnc.liveB ≤ cliSendSlotLiveCap ∧
      SEnc.peakB ≤ cliSendSlotPeakCap ∧ SEnc.maxReq ≤ cliSendSlotReqCap ∧
      SEnc.grpS ≤ cliSendSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .send peer)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_send_fine_specs SEnc hcaps hc
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    sendRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

/-! ### 3.4 Mode 4: `recv_whisper` (`g.c = .recv peer`, `g.i.stdin = 2#8 :: rest`, W2) -/

def cliRecvWhisperSlotCumCap : Nat := 66500000
def cliRecvWhisperSlotLiveCap : Nat := 16500000
def cliRecvWhisperSlotPeakCap : Nat := 20500000
def cliRecvWhisperSlotReqCap : Nat := 5322344
def cliRecvWhisperSlotGrpSCap : Nat := 20000 * FineScale

def cliRecvWhisperRunCumCap : Nat :=
  r0Opened1MiBCum + (sigSliceCum msgCapBytes + cliRecvWhisperSlotCumCap)
def cliRecvWhisperRunLiveCap : Nat :=
  r0Opened1MiBLive + (sigSliceLive msgCapBytes + cliRecvWhisperSlotLiveCap)
def cliRecvWhisperRunPeakCap : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + cliRecvWhisperSlotPeakCap))
def cliRecvWhisperRunReqCap : Nat :=
  max r0Opened1MiBMaxReq (max (sigSliceMaxReq msgCapBytes) cliRecvWhisperSlotReqCap)
def cliRecvWhisperRunGrpSCap : Nat :=
  15 * FineScale + (sigTryFromCapDeltaGrpS msgCapBytes + cliRecvWhisperSlotGrpSCap)
def cliRecvWhisperStepReserve : Nat :=
  cliMainTightStepReserveOf cliRecvWhisperRunReqCap cliRecvWhisperRunGrpSCap

theorem cliRunTight_recvWhisper_fine_specs
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV} {rest : List (BitVec 8)}
    (SDecSig : SingleSlotFineSpec (W g).decSigEnv)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 2#8 :: rest) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (r0Opened1MiBCum + (sigSliceCum msgCapBytes + SDecSig.cumB))
      (r0Opened1MiBLive + (sigSliceLive msgCapBytes + SDecSig.liveB))
      (max r0Opened1MiBPeak
        (r0Opened1MiBLive +
          max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SDecSig.peakB)))
      (max r0Opened1MiBMaxReq (max (sigSliceMaxReq msgCapBytes) SDecSig.maxReq)) ∧
    PhaseGroupSpec fineCostModel (CliRunTightEnv W g)
      (15 * FineScale + (sigTryFromCapDeltaGrpS msgCapBytes + SDecSig.grpS)) := by
  have hrest : rest.length ≤ msgCapBytes := by
    have hlen := hcaps.stdin_le
    rw [hst, List.length_cons] at hlen
    exact Nat.le_of_succ_le hlen
  have harm_cr : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (sigSliceCum msgCapBytes + SDecSig.cumB)
      (sigSliceLive msgCapBytes + SDecSig.liveB)
      (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SDecSig.peakB))
      (max (sigSliceMaxReq msgCapBytes) SDecSig.maxReq) := by
    unfold RunArmEnv; rw [hc, hst]
    unfold RecvArmEnv; simp only [↓reduceIte]
    exact r3a_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      hrest SDecSig.credit_spec SDecSig.live_le_peak
  have hlp_arm :
      sigSliceLive msgCapBytes + SDecSig.liveB ≤
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SDecSig.peakB) :=
    Nat.le_trans (Nat.add_le_add_left SDecSig.live_le_peak _) (Nat.le_max_right _ _)
  have harm_gr : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (sigTryFromCapDeltaGrpS msgCapBytes + SDecSig.grpS) := by
    unfold RunArmEnv; rw [hc, hst]
    unfold RecvArmEnv; simp only [↓reduceIte]
    exact r3aEnv_fine_groupSpec hrest SDecSig.group_spec
  exact ⟨cliRunOfR0_singleArm_fine_phaseCredit hcaps harm_cr hlp_arm,
    cliRunOfR0_fine_groupSpec (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm_gr⟩

private theorem recvWhisperRun_bounds_mono {c l p r g : Nat}
    (hc : c ≤ cliRecvWhisperSlotCumCap) (hl : l ≤ cliRecvWhisperSlotLiveCap)
    (hp : p ≤ cliRecvWhisperSlotPeakCap) (hr : r ≤ cliRecvWhisperSlotReqCap)
    (hg : g ≤ cliRecvWhisperSlotGrpSCap) :
    r0Opened1MiBCum + (sigSliceCum msgCapBytes + c) ≤ cliRecvWhisperRunCumCap ∧
    r0Opened1MiBLive + (sigSliceLive msgCapBytes + l) ≤ cliRecvWhisperRunLiveCap ∧
    max r0Opened1MiBPeak
      (r0Opened1MiBLive + max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + p)) ≤
        cliRecvWhisperRunPeakCap ∧
    max r0Opened1MiBMaxReq (max (sigSliceMaxReq msgCapBytes) r) ≤ cliRecvWhisperRunReqCap ∧
    15 * FineScale + (sigTryFromCapDeltaGrpS msgCapBytes + g) ≤ cliRecvWhisperRunGrpSCap := by
  refine ⟨?_, ?_, ?_, ?_, Nat.add_le_add_left (Nat.add_le_add_left hg _) _⟩
  · unfold cliRecvWhisperRunCumCap; omega
  · unfold cliRecvWhisperRunLiveCap; omega
  · unfold cliRecvWhisperRunPeakCap
    have h1 :
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + p) ≤
          max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + cliRecvWhisperSlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left hp _) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
  · unfold cliRecvWhisperRunReqCap
    have h1 :
        max (sigSliceMaxReq msgCapBytes) r ≤
          max (sigSliceMaxReq msgCapBytes) cliRecvWhisperSlotReqCap :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h1 (Nat.le_max_right _ _)⟩

theorem cliMain_recvWhisper_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {rest : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SDecSig : SingleSlotFineSpec (W g).decSigEnv)
    (hSlot : SDecSig.cumB ≤ cliRecvWhisperSlotCumCap ∧
      SDecSig.liveB ≤ cliRecvWhisperSlotLiveCap ∧
      SDecSig.peakB ≤ cliRecvWhisperSlotPeakCap ∧
      SDecSig.maxReq ≤ cliRecvWhisperSlotReqCap ∧
      SDecSig.grpS ≤ cliRecvWhisperSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 2#8 :: rest)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRecvWhisperStepReserve fullLog := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_recvWhisper_fine_specs SDecSig hcaps hc hst
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    recvWhisperRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

theorem cliMain_recvWhisper_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {rest : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SDecSig : SingleSlotFineSpec (W g).decSigEnv)
    (hSlot : SDecSig.cumB ≤ cliRecvWhisperSlotCumCap ∧
      SDecSig.liveB ≤ cliRecvWhisperSlotLiveCap ∧
      SDecSig.peakB ≤ cliRecvWhisperSlotPeakCap ∧
      SDecSig.maxReq ≤ cliRecvWhisperSlotReqCap ∧
      SDecSig.grpS ≤ cliRecvWhisperSlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 2#8 :: rest)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_recvWhisper_fine_specs SDecSig hcaps hc hst
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    recvWhisperRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

/-! ### 3.5 Mode 5: `recv_prekey` (`g.c = .recv peer`, `g.i.stdin = 3#8 :: rest`, W4) -/

def cliRecvPrekeySlotCumCap : Nat := 303600000
def cliRecvPrekeySlotLiveCap : Nat := 13500000
def cliRecvPrekeySlotPeakCap : Nat := 16200000
def cliRecvPrekeySlotReqCap : Nat := 4194304
def cliRecvPrekeySlotGrpSCap : Nat := 91300 * FineScale

def cliRecvPrekeyRunCumCap : Nat :=
  r0Opened1MiBCum + (pksmSliceCum msgCapBytes + cliRecvPrekeySlotCumCap)
def cliRecvPrekeyRunLiveCap : Nat :=
  r0Opened1MiBLive + (pksmSliceLive msgCapBytes + cliRecvPrekeySlotLiveCap)
def cliRecvPrekeyRunPeakCap : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + cliRecvPrekeySlotPeakCap))
def cliRecvPrekeyRunReqCap : Nat :=
  max r0Opened1MiBMaxReq (max (pksmSliceMaxReq msgCapBytes) cliRecvPrekeySlotReqCap)
def cliRecvPrekeyRunGrpSCap : Nat :=
  15 * FineScale + (pksmTryFromCapDeltaGrpS msgCapBytes + cliRecvPrekeySlotGrpSCap)
def cliRecvPrekeyStepReserve : Nat :=
  cliMainTightStepReserveOf cliRecvPrekeyRunReqCap cliRecvPrekeyRunGrpSCap

theorem cliRunTight_recvPrekey_fine_specs
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall} {peer : AddrV} {rest : List (BitVec 8)}
    (SDecPk : SingleSlotFineSpec (W g).decPkEnv)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 3#8 :: rest) :
    PhaseCreditSpec fineCostModel (CliRunTightEnv W g)
      (r0Opened1MiBCum + (pksmSliceCum msgCapBytes + SDecPk.cumB))
      (r0Opened1MiBLive + (pksmSliceLive msgCapBytes + SDecPk.liveB))
      (max r0Opened1MiBPeak
        (r0Opened1MiBLive +
          max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + SDecPk.peakB)))
      (max r0Opened1MiBMaxReq (max (pksmSliceMaxReq msgCapBytes) SDecPk.maxReq)) ∧
    PhaseGroupSpec fineCostModel (CliRunTightEnv W g)
      (15 * FineScale + (pksmTryFromCapDeltaGrpS msgCapBytes + SDecPk.grpS)) := by
  have hrest : rest.length ≤ msgCapBytes := by
    have hlen := hcaps.stdin_le
    rw [hst, List.length_cons] at hlen
    exact Nat.le_of_succ_le hlen
  have harm_cr : PhaseCreditSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (pksmSliceCum msgCapBytes + SDecPk.cumB)
      (pksmSliceLive msgCapBytes + SDecPk.liveB)
      (max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + SDecPk.peakB))
      (max (pksmSliceMaxReq msgCapBytes) SDecPk.maxReq) := by
    unfold RunArmEnv; rw [hc, hst]
    unfold RecvArmEnv
    have hne : (3#8 : BitVec 8) ≠ 2#8 := by decide
    simp only [hne, ↓reduceIte]
    exact r3b_slice_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      hrest SDecPk.credit_spec SDecPk.live_le_peak
  have hlp_arm :
      pksmSliceLive msgCapBytes + SDecPk.liveB ≤
        max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + SDecPk.peakB) :=
    Nat.le_trans (Nat.add_le_add_left SDecPk.live_le_peak _) (Nat.le_max_right _ _)
  have harm_gr : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (W g).toCalleeEnvs sessionCapBytes g.i.stdin g.c)
      (pksmTryFromCapDeltaGrpS msgCapBytes + SDecPk.grpS) := by
    unfold RunArmEnv; rw [hc, hst]
    unfold RecvArmEnv
    have hne : (3#8 : BitVec 8) ≠ 2#8 := by decide
    simp only [hne, ↓reduceIte]
    exact r3bEnv_fine_groupSpec hrest SDecPk.group_spec
  exact ⟨cliRunOfR0_singleArm_fine_phaseCredit hcaps harm_cr hlp_arm,
    cliRunOfR0_fine_groupSpec (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)) harm_gr⟩

private theorem recvPrekeyRun_bounds_mono {c l p r g : Nat}
    (hc : c ≤ cliRecvPrekeySlotCumCap) (hl : l ≤ cliRecvPrekeySlotLiveCap)
    (hp : p ≤ cliRecvPrekeySlotPeakCap) (hr : r ≤ cliRecvPrekeySlotReqCap)
    (hg : g ≤ cliRecvPrekeySlotGrpSCap) :
    r0Opened1MiBCum + (pksmSliceCum msgCapBytes + c) ≤ cliRecvPrekeyRunCumCap ∧
    r0Opened1MiBLive + (pksmSliceLive msgCapBytes + l) ≤ cliRecvPrekeyRunLiveCap ∧
    max r0Opened1MiBPeak
      (r0Opened1MiBLive + max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + p)) ≤
        cliRecvPrekeyRunPeakCap ∧
    max r0Opened1MiBMaxReq (max (pksmSliceMaxReq msgCapBytes) r) ≤ cliRecvPrekeyRunReqCap ∧
    15 * FineScale + (pksmTryFromCapDeltaGrpS msgCapBytes + g) ≤ cliRecvPrekeyRunGrpSCap := by
  refine ⟨?_, ?_, ?_, ?_, Nat.add_le_add_left (Nat.add_le_add_left hg _) _⟩
  · unfold cliRecvPrekeyRunCumCap; omega
  · unfold cliRecvPrekeyRunLiveCap; omega
  · unfold cliRecvPrekeyRunPeakCap
    have h1 :
        max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + p) ≤
          max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + cliRecvPrekeySlotPeakCap) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left hp _) (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
  · unfold cliRecvPrekeyRunReqCap
    have h1 :
        max (pksmSliceMaxReq msgCapBytes) r ≤
          max (pksmSliceMaxReq msgCapBytes) cliRecvPrekeySlotReqCap :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h1 (Nat.le_max_right _ _)⟩

theorem cliMain_recvPrekey_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {rest : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SDecPk : SingleSlotFineSpec (W g).decPkEnv)
    (hSlot : SDecPk.cumB ≤ cliRecvPrekeySlotCumCap ∧
      SDecPk.liveB ≤ cliRecvPrekeySlotLiveCap ∧
      SDecPk.peakB ≤ cliRecvPrekeySlotPeakCap ∧
      SDecPk.maxReq ≤ cliRecvPrekeySlotReqCap ∧
      SDecPk.grpS ≤ cliRecvPrekeySlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 3#8 :: rest)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliRecvPrekeyStepReserve fullLog := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_recvPrekey_fine_specs SDecPk hcaps hc hst
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    recvPrekeyRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

theorem cliMain_recvPrekey_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {peer : AddrV} {rest : List (BitVec 8)}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SDecPk : SingleSlotFineSpec (W g).decPkEnv)
    (hSlot : SDecPk.cumB ≤ cliRecvPrekeySlotCumCap ∧
      SDecPk.liveB ≤ cliRecvPrekeySlotLiveCap ∧
      SDecPk.peakB ≤ cliRecvPrekeySlotPeakCap ∧
      SDecPk.maxReq ≤ cliRecvPrekeySlotReqCap ∧
      SDecPk.grpS ≤ cliRecvPrekeySlotGrpSCap)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hc : g.c = .recv peer)
    (hst : g.i.stdin = 3#8 :: rest)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨hcr, hgr⟩ := cliRunTight_recvPrekey_fine_specs SDecPk hcaps hc hst
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    recvPrekeyRun_bounds_mono hSlot.1 hSlot.2.1 hSlot.2.2.1 hSlot.2.2.2.1 hSlot.2.2.2.2
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

/-! ## 4. Unified Whole-`main` `< 1 GiB` Theorems -/

/-- Parametric-`DeserEnv` numerical cap predicate on `CliRunFineSlotSpecs W` with residual
deserialization parameters `(deserCum, deserLive, deserPeak, deserMaxReq, deserGrpS)`. -/
def CliRunDeserParamSlotCaps
    (deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat)
    {W : CliRunWrapperEnvs} (SW : CliRunFineSlotSpecs W) : Prop :=
  SW.initCum ≤ cliInitSlotCumCap + deserCum ∧
  SW.initLive ≤ cliInitSlotLiveCap + deserLive ∧
  SW.initPeak ≤ cliInitSlotPeakCap + deserPeak ∧
  SW.initMaxReq ≤ max cliInitSlotReqCap deserMaxReq ∧
  SW.initGrpS ≤ cliInitSlotGrpSCap + deserGrpS ∧
  SW.encCum ≤ cliSendSlotCumCap + deserCum ∧
  SW.encLive ≤ cliSendSlotLiveCap + deserLive ∧
  SW.encPeak ≤ cliSendSlotPeakCap + deserPeak ∧
  SW.encMaxReq ≤ max cliSendSlotReqCap deserMaxReq ∧
  SW.encGrpS ≤ cliSendSlotGrpSCap + deserGrpS ∧
  SW.decSigCum ≤ cliRecvWhisperSlotCumCap + deserCum ∧
  SW.decSigLive ≤ cliRecvWhisperSlotLiveCap + deserLive ∧
  SW.decSigPeak ≤ cliRecvWhisperSlotPeakCap + deserPeak ∧
  SW.decSigMaxReq ≤ max cliRecvWhisperSlotReqCap deserMaxReq ∧
  SW.decSigGrpS ≤ cliRecvWhisperSlotGrpSCap + deserGrpS ∧
  SW.decPkCum ≤ cliRecvPrekeySlotCumCap + deserCum ∧
  SW.decPkLive ≤ cliRecvPrekeySlotLiveCap + deserLive ∧
  SW.decPkPeak ≤ cliRecvPrekeySlotPeakCap + deserPeak ∧
  SW.decPkMaxReq ≤ max cliRecvPrekeySlotReqCap deserMaxReq ∧
  SW.decPkGrpS ≤ cliRecvPrekeySlotGrpSCap + deserGrpS

/-- Canonical `deser = 0` tight four-slot cap predicate for `cliMain_fits{Trace,Env}_fineCostModel`. -/
abbrev CliRunTightSlotCaps {W : CliRunWrapperEnvs} (SW : CliRunFineSlotSpecs W) : Prop :=
  CliRunDeserParamSlotCaps 0 0 0 0 0 SW

def cliUnifiedDeserRunCumCap (dc : Nat) : Nat :=
  cliRun1MiBSlotCum
    (cliInitSlotCumCap + dc)
    (cliSendSlotCumCap + dc)
    (cliRecvWhisperSlotCumCap + dc)
    (cliRecvPrekeySlotCumCap + dc)

def cliUnifiedDeserRunLiveCap (dl : Nat) : Nat :=
  cliRun1MiBSlotLive
    (cliInitSlotLiveCap + dl)
    (cliSendSlotLiveCap + dl)
    (cliRecvWhisperSlotLiveCap + dl)
    (cliRecvPrekeySlotLiveCap + dl)

def cliUnifiedDeserRunPeakCap (dl dp : Nat) : Nat :=
  cliRun1MiBSlotPeak
    (cliInitSlotPeakCap + dp)
    (cliSendSlotLiveCap + dl)
    (cliSendSlotPeakCap + dp)
    (cliRecvWhisperSlotPeakCap + dp)
    (cliRecvPrekeySlotPeakCap + dp)

def cliUnifiedDeserRunReqCap (dr : Nat) : Nat :=
  cliRun1MiBSlotMaxReq
    (max cliInitSlotReqCap dr)
    (max cliSendSlotReqCap dr)
    (max cliRecvWhisperSlotReqCap dr)
    (max cliRecvPrekeySlotReqCap dr)

def cliUnifiedDeserRunGrpSCap (dg : Nat) : Nat :=
  cliRunOpenedFineGrpS msgCapBytes
    (cliInitSlotGrpSCap + dg)
    (cliSendSlotGrpSCap + dg)
    (cliRecvWhisperSlotGrpSCap + dg)
    (cliRecvPrekeySlotGrpSCap + dg)

private theorem max4_mono {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    max a1 (max b1 (max c1 d1)) ≤ max a2 (max b2 (max c2 d2)) :=
  Nat.max_le.mpr
    ⟨Nat.le_trans ha (Nat.le_max_left _ _),
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans hb (Nat.le_max_left _ _),
          Nat.le_trans
            (Nat.max_le.mpr
              ⟨Nat.le_trans hc (Nat.le_max_left _ _),
               Nat.le_trans hd (Nat.le_max_right _ _)⟩)
            (Nat.le_max_right _ _)⟩)
       (Nat.le_max_right _ _)⟩

private theorem cliUnifiedDeser_bounds_mono
    {dc dl dp dr dg : Nat} {W : CliRunWrapperEnvs} {SW : CliRunFineSlotSpecs W}
    (hCaps : CliRunDeserParamSlotCaps dc dl dp dr dg SW) :
    cliRun1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ≤
      cliUnifiedDeserRunCumCap dc ∧
    cliRun1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ≤
      cliUnifiedDeserRunLiveCap dl ∧
    cliRun1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ≤
      cliUnifiedDeserRunPeakCap dl dp ∧
    cliRun1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq ≤
      cliUnifiedDeserRunReqCap dr ∧
    cliRunOpenedFineGrpS msgCapBytes SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS ≤
      cliUnifiedDeserRunGrpSCap dg := by
  rcases hCaps with
    ⟨hic, hil, hip, hir, hig,
     hec, hel, hep, her, heg,
     hsc, hsl, hsp, hsr, hsg,
     hpc, hpl, hpp, hpr, hpg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cliUnifiedDeserRunCumCap, cliRun1MiBSlotCum, initArmDeltaCum, r2TightDeltaCum]
    exact Nat.add_le_add_left
      (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  · simp only [cliUnifiedDeserRunLiveCap, cliRun1MiBSlotLive, initArmDeltaLive, r2DeltaLive]
    exact Nat.add_le_add_left
      (max4_mono (by omega) (by omega) (by omega) (by omega)) _
  · unfold cliRun1MiBSlotPeak cliUnifiedDeserRunPeakCap
    have hp_init :
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SW.initPeak ≤
          initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637
            (cliInitSlotPeakCap + dp) := by
      unfold initArmDeltaPeak
      have h1 :
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + SW.initPeak) ≤
          max (CliRunArmsPeak.r1bDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637)
            (CliRunArmsPeak.r1bDeltaLive (pathDeltaLive 26 16) + (cliInitSlotPeakCap + dp)) :=
        Nat.max_le.mpr
          ⟨Nat.le_max_left _ _,
           Nat.le_trans (Nat.add_le_add_left hip _) (Nat.le_max_right _ _)⟩
      exact Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left h1 _) (Nat.le_max_right _ _)⟩
    have hp_enc :
        r2DeltaPeak fineCostModel SW.encLive SW.encPeak sessionCapBytes ≤
          r2DeltaPeak fineCostModel (cliSendSlotLiveCap + dl) (cliSendSlotPeakCap + dp)
            sessionCapBytes := by
      unfold r2DeltaPeak
      exact Nat.max_le.mpr
        ⟨Nat.le_trans hep (Nat.le_max_left _ _),
         Nat.le_trans (Nat.add_le_add_right hel _) (Nat.le_max_right _ _)⟩
    have hp_sig :
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SW.decSigPeak) ≤
          max (sigSlicePeak msgCapBytes)
            (sigSliceLive msgCapBytes + (cliRecvWhisperSlotPeakCap + dp)) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left hsp _) (Nat.le_max_right _ _)⟩
    have hp_pk :
        max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + SW.decPkPeak) ≤
          max (pksmSlicePeak msgCapBytes)
            (pksmSliceLive msgCapBytes + (cliRecvPrekeySlotPeakCap + dp)) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left hpp _) (Nat.le_max_right _ _)⟩
    have h4 := max4_mono hp_init hp_enc hp_sig hp_pk
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (Nat.add_le_add_left h4 _) (Nat.le_max_right _ _)⟩
  · unfold cliRun1MiBSlotMaxReq cliUnifiedDeserRunReqCap initArmMaxReq r2MaxReq
    have hr_init :
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) SW.initMaxReq) ≤
        max (CliRunArmsPeak.r1aMaxReq (pathMaxReq 26 16) 1637)
          (max (CliRunArmsPeak.r1bMaxReq (pathMaxReq 26 16) 1637) (max cliInitSlotReqCap dr)) :=
      Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans
           (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hir (Nat.le_max_right _ _)⟩)
           (Nat.le_max_right _ _)⟩
    have hr_enc :
        max SW.encMaxReq (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) ≤
          max (max cliSendSlotReqCap dr) (CliRunArmsPeak.r2TailMaxReq sessionCapBytes) :=
      Nat.max_le.mpr ⟨Nat.le_trans her (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    have hr_sig :
        max (sigSliceMaxReq msgCapBytes) SW.decSigMaxReq ≤
          max (sigSliceMaxReq msgCapBytes) (max cliRecvWhisperSlotReqCap dr) :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hsr (Nat.le_max_right _ _)⟩
    have hr_pk :
        max (pksmSliceMaxReq msgCapBytes) SW.decPkMaxReq ≤
          max (pksmSliceMaxReq msgCapBytes) (max cliRecvPrekeySlotReqCap dr) :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hpr (Nat.le_max_right _ _)⟩
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
       Nat.le_trans (max4_mono hr_init hr_enc hr_sig hr_pk) (Nat.le_max_right _ _)⟩
  · unfold cliRunOpenedFineGrpS cliUnifiedDeserRunGrpSCap cliRunArmFineGrpS
    exact Nat.add_le_add_left
      (max4_mono
        (Nat.add_le_add_left hig _)
        (Nat.add_le_add_right heg _)
        (Nat.add_le_add_left hsg _)
        (Nat.add_le_add_left hpg _)) _

/-- Canonical whole-`main` `stepReserve` bound at `deser = 0`. -/
def cliMainStepReserve : Nat :=
  cliMainTightStepReserveOf (cliUnifiedDeserRunReqCap 0) (cliUnifiedDeserRunGrpSCap 0)

/-- Whole-`main` `FitsTrace fineCostModel`: under `1 GiB` (`physCap ≥ 2 ^ 30`) and reachable
CLI/PQXDH/SPQR domain caps, every trace of `CliMainEnv uuidParse (CliRunTightEnv W)` across all six
CLI modes satisfies `FitsTrace fineCostModel lim cliMainStepReserve`. -/
theorem cliMain_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunTightSlotCaps SW)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliMainStepReserve fullLog := by
  have hcr := cliRunTight_1MiB_fine_phaseCredit SW hcaps hspqr
  have hgr := cliRunTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedDeser_bounds_mono hSlots
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

/-- Whole-`main` `FitsEnv fineCostModel` at `fineCostModel.init` under `1 GiB` (`physCap ≥ 2 ^ 30`) across all six CLI modes. -/
theorem cliMain_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunTightSlotCaps SW)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  have hcr := cliRunTight_1MiB_fine_phaseCredit SW hcaps hspqr
  have hgr := cliRunTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedDeser_bounds_mono hSlots
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

theorem cliMain_fitsEnv_cliBudgetLimits
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunTightSlotCaps SW)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) :=
  cliMain_fitsEnv_fineCostModel rfl (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    SW hSlots hcaps hspqr haddr hdirs

/-! ## 5. Parametric-`DeserEnv` Residual-Headroom Whole-`main` `< 1 GiB` Theorems -/

def cliDeserMaxCum : Nat := 2000000
def cliDeserMaxLive : Nat := 1000000
def cliDeserMaxPeak : Nat := 1500000
def cliDeserMaxReq : Nat := sessionCapBytes
def cliDeserMaxGrpS : Nat := 250 * FineScale

def cliMainDeserParamStepReserve : Nat :=
  cliMainTightStepReserveOf
    (cliUnifiedDeserRunReqCap cliDeserMaxReq)
    (cliUnifiedDeserRunGrpSCap cliDeserMaxGrpS)

private theorem deserParamSlotCaps_mono
    {dc1 dl1 dp1 dr1 dg1 dc2 dl2 dp2 dr2 dg2 : Nat}
    {W : CliRunWrapperEnvs} {SW : CliRunFineSlotSpecs W}
    (h : CliRunDeserParamSlotCaps dc1 dl1 dp1 dr1 dg1 SW)
    (hc : dc1 ≤ dc2) (hl : dl1 ≤ dl2) (hp : dp1 ≤ dp2) (hr : dr1 ≤ dr2) (hg : dg1 ≤ dg2) :
    CliRunDeserParamSlotCaps dc2 dl2 dp2 dr2 dg2 SW := by
  rcases h with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
     h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact
    ⟨Nat.le_trans h1 (Nat.add_le_add_left hc _),
     Nat.le_trans h2 (Nat.add_le_add_left hl _),
     Nat.le_trans h3 (Nat.add_le_add_left hp _),
     Nat.le_trans h4 (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩),
     Nat.le_trans h5 (Nat.add_le_add_left hg _),
     Nat.le_trans h6 (Nat.add_le_add_left hc _),
     Nat.le_trans h7 (Nat.add_le_add_left hl _),
     Nat.le_trans h8 (Nat.add_le_add_left hp _),
     Nat.le_trans h9 (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩),
     Nat.le_trans h10 (Nat.add_le_add_left hg _),
     Nat.le_trans h11 (Nat.add_le_add_left hc _),
     Nat.le_trans h12 (Nat.add_le_add_left hl _),
     Nat.le_trans h13 (Nat.add_le_add_left hp _),
     Nat.le_trans h14 (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩),
     Nat.le_trans h15 (Nat.add_le_add_left hg _),
     Nat.le_trans h16 (Nat.add_le_add_left hc _),
     Nat.le_trans h17 (Nat.add_le_add_left hl _),
     Nat.le_trans h18 (Nat.add_le_add_left hp _),
     Nat.le_trans h19 (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hr (Nat.le_max_right _ _)⟩),
     Nat.le_trans h20 (Nat.add_le_add_left hg _)⟩

/-- Whole-`main` `FitsTrace fineCostModel` under `1 GiB` physical RAM and `≤ 2 ^ 48` VA with
residual deserialization headroom `(deserCum ≤ 2,000,000, deserLive ≤ 1,000,000,
deserPeak ≤ 1,500,000, deserMaxReq ≤ 2 MiB, deserGrpS ≤ 250 * FineScale)`. -/
theorem cliMain_deserParam_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunDeserParamSlotCaps deserCum deserLive deserPeak deserMaxReq deserGrpS SW)
    (hDeser : deserCum ≤ cliDeserMaxCum ∧ deserLive ≤ cliDeserMaxLive ∧
      deserPeak ≤ cliDeserMaxPeak ∧ deserMaxReq ≤ cliDeserMaxReq ∧
      deserGrpS ≤ cliDeserMaxGrpS)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliMainDeserParamStepReserve fullLog := by
  have hcr := cliRunTight_1MiB_fine_phaseCredit SW hcaps hspqr
  have hgr := cliRunTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le
  have hSlotsMax := deserParamSlotCaps_mono hSlots
    hDeser.1 hDeser.2.1 hDeser.2.2.1 hDeser.2.2.2.1 hDeser.2.2.2.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedDeser_bounds_mono hSlotsMax
  exact cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

/-- Whole-`main` `FitsEnv fineCostModel` at `fineCostModel.init` under `1 GiB` with residual deserialization headroom. -/
theorem cliMain_deserParam_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunDeserParamSlotCaps deserCum deserLive deserPeak deserMaxReq deserGrpS SW)
    (hDeser : deserCum ≤ cliDeserMaxCum ∧ deserLive ≤ cliDeserMaxLive ∧
      deserPeak ≤ cliDeserMaxPeak ∧ deserMaxReq ≤ cliDeserMaxReq ∧
      deserGrpS ≤ cliDeserMaxGrpS)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunTightEnv W) g addrOpt needStdin dirs ok) := by
  have hcr := cliRunTight_1MiB_fine_phaseCredit SW hcaps hspqr
  have hgr := cliRunTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le
  have hSlotsMax := deserParamSlotCaps_mono hSlots
    hDeser.1 hDeser.2.1 hDeser.2.2.1 hDeser.2.2.2.1 hDeser.2.2.2.2
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedDeser_bounds_mono hSlotsMax
  exact cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs hcr hgr
    h1 h2 h3 h4 h5 (by decide) (by decide)

/-! ## 6. Closed-Numeral `< 1 GiB` and `VA ≤ 2 ^ 48` Summary Check -/

theorem cliAllModes_and_deserParam_fit_oneGiB :
    cliMainTightRamNeedOf 0 0 0 0 0 ≤ cliOneGiB ∧
    cliMainTightRamNeedOf r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak
      r0Opened1MiBMaxReq cliKeygenRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightRamNeedOf cliInitRunCumCap cliInitRunLiveCap cliInitRunPeakCap
      cliInitRunReqCap cliInitRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightRamNeedOf cliSendRunCumCap cliSendRunLiveCap cliSendRunPeakCap
      cliSendRunReqCap cliSendRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightRamNeedOf cliRecvWhisperRunCumCap cliRecvWhisperRunLiveCap
      cliRecvWhisperRunPeakCap cliRecvWhisperRunReqCap cliRecvWhisperRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightRamNeedOf cliRecvPrekeyRunCumCap cliRecvPrekeyRunLiveCap
      cliRecvPrekeyRunPeakCap cliRecvPrekeyRunReqCap cliRecvPrekeyRunGrpSCap ≤ cliOneGiB ∧
    cliMainTightRamNeedOf (cliUnifiedDeserRunCumCap 0) (cliUnifiedDeserRunLiveCap 0)
      (cliUnifiedDeserRunPeakCap 0 0) (cliUnifiedDeserRunReqCap 0)
      (cliUnifiedDeserRunGrpSCap 0) ≤ cliOneGiB ∧
    cliMainTightRamNeedOf (cliUnifiedDeserRunCumCap cliDeserMaxCum)
      (cliUnifiedDeserRunLiveCap cliDeserMaxLive)
      (cliUnifiedDeserRunPeakCap cliDeserMaxLive cliDeserMaxPeak)
      (cliUnifiedDeserRunReqCap cliDeserMaxReq)
      (cliUnifiedDeserRunGrpSCap cliDeserMaxGrpS) ≤ cliOneGiB := by
  decide

end LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
