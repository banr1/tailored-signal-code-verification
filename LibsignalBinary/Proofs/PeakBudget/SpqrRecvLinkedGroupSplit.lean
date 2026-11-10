/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738

/-!
# Linked `PhaseGroupSpec` Split and `try_decrypt` `PhaseCreditSpec` Bounds

Lifts the branch-split `PhaseGroupSpec` bounds from `SpqrRecvTightGroupSplit` and the unconditional-history
`PhaseCreditSpec` bounds from `W2Seg4CmkSeeds738` to `SpqrRecvC07TightLinkedEnv` and
`SpqrRecvC07C09aTightLinkedEnv`, discharging `SpqrRecvTightDomain` internally from `TopStateTight`
via `spqrRecvTightDomain_of_topStateTight_and_link`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (W2TryDecryptTightEnv w2Seg4CmkFineGrpS w2Seg4CmkStepEnv_groupSpec
   w2TryDecryptEnv_of_seg4_groupSpec w2TryDecryptFailEnv_of_seg4_groupSpec
   w2TryDecryptTightEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire (c09aStatesRecvTightCreditSpec_inst)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvC07TightLinkedEnv spqrRecvC07TightLinkedEnv_proto_eq
   spqrRecvTightDomain_of_topStateTight_and_link)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
  (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split
   spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split_rawEnv spqrRecvTightGroupS_split
   w2TryDecryptTightGroupS_split w2TryDecryptTightGroupS_split_10
   w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvEnv StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (W2TryDecryptEnv W2TryDecryptFailEnv w2CmkChainTightLive w2TryDecryptMaxReq
   w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak (DoublingChainLe)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (W2TryDecryptFailSeedsEnv W2TryDecryptFailTightEnv W2TryDecryptSeedsEnv
   w2TryDecryptFailTightEnv_fine_groupSpec w2TryDecryptFail_fine_phaseCreditSpec_seeds738
   w2TryDecryptFail_genSeeds_fine_phaseCreditSpec w2TryDecryptGenSeeds738Cum
   w2TryDecryptSeeds738Cum w2TryDecryptSeedsEnv_fine_groupSpec
   w2TryDecrypt_fine_phaseCreditSpec_seeds738 w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)

/-! ## Closed Group-Split Constants -/

/-- Failed-trial `W2TryDecryptFailTightEnv` scaled group bound parametric in `maxSteps`. -/
def w2TryDecryptFailTightGroupS_split (maxSteps : Nat) : Nat :=
  24 * FineScale + 6 * 16659 + 11056 + w2Seg4CmkFineGrpS maxSteps + spqrRecvTightGroupS_split

/-- Closed failed-trial `W2TryDecryptFailTightEnv` scaled group bound for `maxSteps ≤ 12` (`508,147,025`, `7,754` groups).
-/
def w2TryDecryptFailTightGroupS_split_12 : Nat := 508147025

/-- Closed `W2TryDecryptSeedsEnv 12` scaled group bound for `maxSteps ≤ 12` (`476,208,581`, `7,267` groups).
-/
def w2TryDecryptSeeds12GroupS_split_12 : Nat := 476208581

theorem spqrRecvTightGroupS_split_eq : spqrRecvTightGroupS_split = 470785855 := by decide

theorem w2TryDecryptTightGroupS_split_12_eq :
    w2TryDecryptTightGroupS_split 12 = 509326673 := by decide

theorem w2TryDecryptTightGroupS_split_12_def_eq :
    w2TryDecryptTightGroupS_split_12 = 509326673 := by decide

theorem w2TryDecryptTightGroupS_split_10_eq :
    w2TryDecryptTightGroupS_split 10 = 508933457 := by decide

theorem w2TryDecryptTightGroupS_split_10_def_eq :
    w2TryDecryptTightGroupS_split_10 = 508933457 := by decide

theorem w2TryDecryptFailTightGroupS_split_12_eq :
    w2TryDecryptFailTightGroupS_split 12 = w2TryDecryptFailTightGroupS_split_12 := by decide

theorem w2TryDecryptSeeds12GroupS_split_12_eq :
    42 * FineScale + 6 * 16659 + 11056 + (12 * 16659 + 12 * (3 * FineScale)) +
      spqrRecvTightGroupS_split = w2TryDecryptSeeds12GroupS_split_12 := by decide

/-! ## Existential Witness Combinators for `PhaseGroupSpec` -/

/-- Lifts a uniform `PhaseGroupSpec` bound across an existential ghost witness `∃ a, E a evs`. -/
theorem phaseGroup_exists {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, E a evs) g where
  groups_le st0 {_} := fun ⟨a, ha⟩ => (h a).groups_le st0 ha

theorem phaseGroup_exists_prop {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 {_} := fun ⟨a, hp, ha⟩ => (h a hp).groups_le st0 ha

/-! ## Linked `spqr::recv` `PhaseGroupSpec` Split Bounds -/

/-- Branch-split `PhaseGroupSpec` (`470,785,855` scaled units) for `SpqrRecvC07TightLinkedEnv` at
`StatesRecvProtoEnv`, discharging `SpqrRecvTightDomain` from `TopStateTight`. -/
theorem spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      spqrRecvTightGroupS_split where
  groups_le st_m {_} hEnv := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    exact (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).groups_le
      st_m hTight

theorem spqrRecvC07C09aTightLinkedEnv_phaseGroupSpec_tight_split
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07C09aTightLinkedEnv F K
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      spqrRecvTightGroupS_split :=
  spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

theorem spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      spqrRecvTightGroupS_split where
  groups_le st_m {_} hEnv := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    exact (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).groups_le
      st_m hTight

/-! ## Linked `try_decrypt` `PhaseGroupSpec` Split Bounds -/

/-- Linked `maxSteps`-parametric `PhaseGroupSpec` for `W2TryDecryptTightEnv` under `TopStateTight`.
-/
theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightGroupS_split maxSteps) :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split_rawEnv
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightGroupS_split maxSteps) :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

/-- Closed `509,326,673` linked `PhaseGroupSpec` for `W2TryDecryptTightEnv` when `caps.length ≤ 12`.
-/
theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_12 :=
  (w2TryDecryptTightEnv_linked_fine_groupSpec_split F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

theorem w2TryDecryptTightEnv_c07c09a_linked_fine_groupSpec_split_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07C09aTightLinkedEnv F K
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_12 :=
  w2TryDecryptTightEnv_linked_fine_groupSpec_split_12 F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop

theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split_rawEnv_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_12 :=
  (w2TryDecryptTightEnv_linked_fine_groupSpec_split_rawEnv F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split_10
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 10)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_10 :=
  (w2TryDecryptTightEnv_linked_fine_groupSpec_split F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

theorem w2TryDecryptTightEnv_linked_fine_groupSpec_split_rawEnv_10
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 10)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_10 :=
  (w2TryDecryptTightEnv_linked_fine_groupSpec_split_rawEnv F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

/-- Linked `maxSteps`-parametric failed-trial `PhaseGroupSpec` for `W2TryDecryptFailTightEnv`. -/
theorem w2TryDecryptFailTightEnv_linked_fine_groupSpec_split
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptFailTightGroupS_split maxSteps) :=
  w2TryDecryptFailTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

/-- Closed `508,147,025` linked failed-trial `PhaseGroupSpec` when `caps.length ≤ 12`. -/
theorem w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptFailTightGroupS_split_12 :=
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

theorem w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_rawEnv_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptFailTightGroupS_split_12 :=
  (w2TryDecryptFailTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)).mono
    (by decide)

/-- Linked `maxSeeds`-parametric `PhaseGroupSpec` for `W2TryDecryptSeedsEnv`. -/
theorem w2TryDecryptSeedsEnv_linked_fine_groupSpec_split
    (F : ShaCompress) (K : MlKem)
    (maxSeeds dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptSeedsEnv maxSeeds dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (42 * FineScale + 6 * 16659 + 11056 +
        (maxSeeds * 16659 + maxSteps * (3 * FineScale)) + spqrRecvTightGroupS_split) :=
  w2TryDecryptSeedsEnv_fine_groupSpec maxSeeds dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

theorem w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ 12)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptSeedsEnv 12 dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptSeeds12GroupS_split_12 :=
  (w2TryDecryptSeedsEnv_linked_fine_groupSpec_split F K 12 dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop).mono
    (by decide)

theorem w2TryDecryptEnv_linked_fine_groupSpec_split
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (63 * FineScale + (3 * FineScale * 2000 + maxSteps * (3 * FineScale)) +
        spqrRecvTightGroupS_split) :=
  w2TryDecryptEnv_of_seg4_groupSpec fineCostModel dhCap needGrow caps withAddr errAlloc ctLen
    (w2Seg4CmkStepEnv_groupSpec fineCostModel hcaps)
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

theorem w2TryDecryptFailEnv_linked_fine_groupSpec_split
    (F : ShaCompress) (K : MlKem)
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hcaps : caps.length ≤ maxSteps)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (45 * FineScale + (3 * FineScale * 2000 + maxSteps * (3 * FineScale)) +
        spqrRecvTightGroupS_split) :=
  w2TryDecryptFailEnv_of_seg4_groupSpec fineCostModel dhCap needGrow caps withAddr errAlloc ctLen
    (w2Seg4CmkStepEnv_groupSpec fineCostModel hcaps)
    (spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)

/-! ## Linked Unconditional-History `spqr::recv` and `try_decrypt` `PhaseCreditSpec` Bounds -/

/-- Linked unconditional-history `PhaseCreditSpec` (`23,313,687 / 605,066 / 621,350`) for `SpqrRecvC07TightLinkedEnv`.
-/
theorem spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 (max rRecv 302480) where
  req_align evs hEnv ev hev := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    exact (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).req_align
      evs hTight ev hev
  credit_le st_m {_} hEnv := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    exact (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).credit_le
      st_m hTight

theorem spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 :=
  (spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist F K
    (c09aStatesRecvTightCreditSpec_inst F) (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 := by
  rw [← spqrRecvC07TightLinkedEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

/-- Linked unconditional-history `PhaseCreditSpec` for `W2TryDecryptSeedsEnv 738` under `TopStateTight`.
-/
theorem w2TryDecrypt_spqrC07_linked_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

/-- Linked unconditional-history failed-trial `PhaseCreditSpec` for `W2TryDecryptFailSeedsEnv 738` under `TopStateTight`.
-/
theorem w2TryDecryptFail_spqrC07_linked_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738_rawEnv
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738_rawEnv
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

/-- General-`maxSeeds` linked unconditional-history `PhaseCreditSpec` for `W2TryDecryptSeedsEnv`. -/
theorem w2TryDecrypt_genSeeds_spqrC07_c09a_linked_uncondHist_phaseCreditSpec
    (F : ShaCompress) (K : MlKem)
    {maxSeeds dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptSeedsEnv maxSeeds dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum maxSeeds dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecrypt_genSeeds_fine_phaseCreditSpec hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecryptFail_genSeeds_spqrC07_c09a_linked_uncondHist_phaseCreditSpec
    (F : ShaCompress) (K : MlKem)
    {maxSeeds dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailSeedsEnv maxSeeds dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum maxSeeds dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecryptFail_genSeeds_fine_phaseCreditSpec hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
