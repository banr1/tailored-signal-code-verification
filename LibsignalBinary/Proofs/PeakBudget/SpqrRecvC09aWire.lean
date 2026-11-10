/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec

/-!
# Concrete Tight Credit and Group Specs for SPQR `spqr::recv`

Instantiates the parametric `<States>::recv` credit and slot-group interfaces across
`SpqrRecvPeakSpec`, `SpqrRecvTightBranches`, `SpqrRecvTightSpec`, and `SpqrRecvGroupSpec` with the
concrete `<States>::recv` bounds from `SpqrStatesRecvPeakSpec`. Establishes equivalence between
`StatesRecvProtoEnv` and `StatesRecvEnv` after `States.from_pb`, closed `PhaseCreditSpec` and
`PhaseGroupSpec` bounds for `spqr::recv`, and `FitsEnv fineCostModel` corollaries.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawPqState rawV1State)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (PhaseGroupSpec fitsEnv_fineCostModel_of_phaseCredit_groups)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps nonVacLimits)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (SpqrLowInterceptHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
  (StatesRecvTightGroupSpec c07TightGroupSpec_inst spqrRecvOrderingEqual_phaseGroupSpec_tight
   spqrRecvParts_c07_128_phaseGroupSpec_tight spqrRecvParts_c07_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
  (SpqrRecvEqualCallEnv SpqrRecvPartsEnv StatesRecvCreditSpec equalDeltaCum equalDeltaLive
   equalDeltaPeak equalMaxReq fineCredit fineCredit_le_of_phaseCreditSpec spqrRecvDeltaCum
   spqrRecvDeltaLive spqrRecvDeltaPeak spqrRecvMaxReq spqrRecvOrderingEqual_phaseCreditSpec
   spqrRecvParts_phaseCreditSpec spqrRecv_evalLog_footprint_le spqrRecv_fineCredit_le)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvEqualC07TightEnv SpqrRecvEqualTightEnv SpqrRecvTightDomain
   SpqrRecvTightEnv StatesRecvTightCreditSpec V1ChainAndEncodeTightEnv spqrRecvC07TightEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey (KeyHistorySmallOrReserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (spqrRecvOrderingEqual_c07_phaseCreditSpec_tight
   spqrRecvOrderingEqual_c07_phaseCreditSpec_tight_smallHist
   spqrRecvParts_c07_phaseCreditSpec_tight_c09a spqrRecvParts_c07_phaseCreditSpec_tight_exact
   spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist spqrRecv_c07_evalLog_footprint_le_tight
   spqrRecv_c07_fineCredit_le_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
  (StatesRecvEnv StatesRecvProtoEnv nonVacLimits250MiB statesRecvProtoEnv_eq_of_from_pb
   statesRecvProtoEnv_tight_creditSpec statesRecvProtoEnv_tight_groupSpec statesRecvTightGroupS
   statesRecv_phaseCreditSpec statesRecv_small8k_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidChainParamsPB)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)

/-! ## Concrete `<States>::recv` Credit and Group Instances -/

/-- Regime-uniform `StatesRecvCreditSpec` for `StatesRecvEnv` under `ModelHyps M`. -/
def c09aStatesRecvCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) :
    StatesRecvCreditSpec M F StatesRecvEnv where
  kCum := 436
  cCum := 12000000
  kLive := 374
  cLive := 10200000
  kPeak := 374
  cPeak := 10200000
  kReq := 2
  cReq := 2080
  spec_of_pts st0 msg hpts := statesRecv_phaseCreditSpec hM st0 msg hpts

/-- Tightened `StatesRecvCreditSpec` for `StatesRecvEnv` when `8195 ≤ smallMaxReq M` (`cLive = cPeak = 280,000`).
-/
def c09aStatesRecvSmall8kCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall8k : 8195 ≤ HasFineReallocCredit.smallMaxReq M) (F : ShaCompress) :
    StatesRecvCreditSpec M F StatesRecvEnv where
  kCum := 436
  cCum := 12000000
  kLive := 374
  cLive := 280000
  kPeak := 374
  cPeak := 280000
  kReq := 2
  cReq := 2080
  spec_of_pts st0 msg hpts := statesRecv_small8k_phaseCreditSpec hM hsmall8k st0 msg hpts

def c09aStatesRecvFineCreditSpec (F : ShaCompress) :
    StatesRecvCreditSpec fineCostModel F StatesRecvEnv :=
  c09aStatesRecvSmall8kCreditSpec fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide) F

/-- `StatesRecvTightCreditSpec` for `StatesRecvProtoEnv` (`cRecv = 1,647,247`, `rRecv = 93,776`). -/
theorem c09aStatesRecvTightCreditSpec_inst (F : ShaCompress) :
    StatesRecvTightCreditSpec F StatesRecvProtoEnv 1647247 93776 :=
  ⟨fun st0 msg hpts hpts640 hraw46 =>
    (statesRecvProtoEnv_tight_creditSpec st0 msg hpts hpts640 hraw46).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)⟩

/-- `StatesRecvTightGroupSpec` for `StatesRecvProtoEnv` (`244,580,352`, i.e. `3,732` groups). -/
theorem c09aStatesRecvTightGroupSpec_inst (F : ShaCompress) :
    StatesRecvTightGroupSpec F StatesRecvProtoEnv statesRecvTightGroupS :=
  ⟨fun st0 msg hpts hpts640 hraw46 =>
    statesRecvProtoEnv_tight_groupSpec st0 msg hpts hpts640 hraw46⟩

/-! ## `SpqrRecvPeakSpec` Corollaries -/

theorem spqrRecvOrderingEqual_c09a_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {rawPre maxJumpCap maxOooCap d : Nat}
    (hraw : rawPqState pre_pb ≤ rawPre)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (rawPre + 1058) + 36 * maxOooCap < 2 ^ d) :
    let S := c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F
    PhaseCreditSpec M
      (SpqrRecvEqualCallEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (equalDeltaCum M S rawPre maxJumpCap maxOooCap d)
      (equalDeltaLive M S rawPre maxOooCap)
      (equalDeltaPeak M S rawPre maxOooCap)
      (equalMaxReq S rawPre maxOooCap) :=
  spqrRecvOrderingEqual_phaseCreditSpec hM hLow
    (Nat.le_trans (by decide : 72 ≤ 8195) hLow.hSmallMaxGe) F K
    (c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F)
    hraw hinner hJump hOoo hd

theorem spqrRecvParts_c09a_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    {maxJumpCap maxOooCap d : Nat}
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (201 * stBytes.length + 1058) + 36 * maxOooCap < 2 ^ d) :
    let S := c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F
    PhaseCreditSpec M
      (SpqrRecvPartsEnv F K StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v
        xInit xNew xAdd xRk xSInto xCInto)
      (spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d)
      (spqrRecvDeltaLive M S stBytes.length maxOooCap)
      (spqrRecvDeltaPeak M S stBytes.length maxOooCap)
      (spqrRecvMaxReq S stBytes.length maxOooCap) :=
  spqrRecvParts_phaseCreditSpec hM hLow F K
    (c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hJump hOoo hd

theorem spqrRecv_c09a_fineCredit_le
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    {maxJumpCap maxOooCap d : Nat}
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (201 * stBytes.length + 1058) + 36 * maxOooCap < 2 ^ d)
    (s0 : M.σ) {evs : List AllocEvent}
    (hevs : SpqrRecvPartsEnv F K StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v
      xInit xNew xAdd xRk xSInto xCInto evs) :
    let S := c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F
    fineCredit M (M.stepEvents evs s0) ≤
      fineCredit M s0 +
        spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d +
        spqrRecvDeltaPeak M S stBytes.length maxOooCap :=
  spqrRecv_fineCredit_le hM hLow F K
    (c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hJump hOoo hd s0 hevs

theorem spqrRecv_c09a_evalLog_footprint_le
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    {maxJumpCap maxOooCap d : Nat}
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (201 * stBytes.length + 1058) + 36 * maxOooCap < 2 ^ d)
    {evs : List AllocEvent}
    (hevs : SpqrRecvPartsEnv F K StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v
      xInit xNew xAdd xRk xSInto xCInto evs) :
    let S := c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F
    M.footprint (M.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := M) +
        spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d +
        spqrRecvDeltaPeak M S stBytes.length maxOooCap :=
  spqrRecv_evalLog_footprint_le hM hLow F K
    (c09aStatesRecvSmall8kCreditSpec hM hLow.hSmallMaxGe F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hJump hOoo hd hevs

/-! ## Tight Envelopes and `StatesRecvProtoEnv = StatesRecvEnv` Bridges -/

/-- Closed `Ordering::Equal` tight envelope specialized to `StatesRecvProtoEnv`. -/
def SpqrRecvEqualC07C09aTightEnv (F : ShaCompress) (K : MlKem)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvEqualC07TightEnv F K StatesRecvProtoEnv
    pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evs

theorem spqrRecvEqualC07C09aTightEnv_nil (F : ShaCompress) (K : MlKem)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvEqualC07C09aTightEnv F K pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto [] :=
  Or.inl FreeOnlyEvs.nil

/-- Closed `spqr::recv` tight envelope specialized to `StatesRecvProtoEnv`. -/
def SpqrRecvC07C09aTightEnv (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvC07TightEnv F K StatesRecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem spqrRecvC07C09aTightEnv_nil (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvC07C09aTightEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] :=
  spqrRecvC07TightEnv_nil F K StatesRecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto

/-- Inside `SpqrRecvEqualTightEnv`, `<States>::recv` is guarded by
`States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0`, under which `StatesRecvProtoEnv`
coincides with `StatesRecvEnv`. -/
theorem spqrRecvEqualTightEnv_proto_eq
    (F : ShaCompress) (K : MlKem)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvProtoEnv
      pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto =
    SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto := by
  have hInner :
      (fun evsAfterFrom =>
        FreeOnlyEvs evsAfterFrom ∨
          (States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
            SeqEnv (StatesRecvProtoEnv st0 sckaMsg)
              (fun evsAfterRecv =>
                FreeOnlyEvs evsAfterRecv ∨
                  (States.recv K st0 sckaMsg = .ok v ∧
                    xSInto.st = v.state ∧
                    V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                      xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)) =
      (fun evsAfterFrom =>
        FreeOnlyEvs evsAfterFrom ∨
          (States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
            SeqEnv (StatesRecvEnv st0 sckaMsg)
              (fun evsAfterRecv =>
                FreeOnlyEvs evsAfterRecv ∨
                  (States.recv K st0 sckaMsg = .ok v ∧
                    xSInto.st = v.state ∧
                    V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                      xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)) := by
    funext evsAfterFrom
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · rw [statesRecvProtoEnv_eq_of_from_pb hfrom sckaMsg]
    · exact propext
        ⟨Or.imp id fun h => absurd h.1 hfrom,
         Or.imp id fun h => absurd h.1 hfrom⟩
  unfold SpqrRecvEqualTightEnv
  rw [hInner]

theorem spqrRecvEqualC07TightEnv_proto_eq
    (F : ShaCompress) (K : MlKem)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvEqualC07TightEnv F K StatesRecvProtoEnv
      pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto =
    SpqrRecvEqualC07TightEnv F K StatesRecvEnv
      pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto := by
  funext evs
  unfold SpqrRecvEqualC07TightEnv
  rw [spqrRecvEqualTightEnv_proto_eq]

theorem spqrRecvTightEnv_proto_eq
    (F : ShaCompress) (K : MlKem)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =
    SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto := by
  unfold SpqrRecvTightEnv
  rw [spqrRecvEqualTightEnv_proto_eq]

theorem spqrRecvC07TightEnv_proto_eq
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvC07TightEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =
    SpqrRecvC07TightEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto := by
  funext evs
  unfold SpqrRecvC07TightEnv
  rw [spqrRecvTightEnv_proto_eq]

/-! ## Closed `spqr::recv` `PhaseCreditSpec` Bounds -/

/-- Closed `Ordering::Equal` `PhaseCreditSpec` without `KeyHistory` reserve assumptions
(`Δcum = 21,753,058`, `Δlive = 605,066`, `Δpeak = 621,350`, `maxReq = 302,480`). -/
theorem spqrRecvOrderingEqual_c07_c09a_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualC07TightEnv F K StatesRecvProtoEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      21753058 605066 621350 302480 :=
  (spqrRecvOrderingEqual_c07_phaseCreditSpec_tight F K (c09aStatesRecvTightCreditSpec_inst F)
    hv1Pts hv1Raw hAddLinks hRkLinks hParams hPrev hOutCap).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- Closed `Ordering::Equal` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk`
(`Δcum = 21,743,519`, `Δlive = Δpeak = 294,391`, `maxReq = 286,196`). -/
theorem spqrRecvOrderingEqual_c07_c09a_phaseCreditSpec_tight_smallHist
    (F : ShaCompress) (K : MlKem)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualC07TightEnv F K StatesRecvProtoEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      21743519 294391 294391 286196 :=
  (spqrRecvOrderingEqual_c07_phaseCreditSpec_tight_smallHist F K
    (c09aStatesRecvTightCreditSpec_inst F)
    hv1Pts hv1Raw hAddLinks hRkLinks hParams hHist hOutCap).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- Exact closed `spqr::recv` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk`
(`Δcum = 23,050,735`, `Δlive = Δpeak = 294,391`, `maxReq = 286,196`). -/
theorem spqrRecvParts_c07_c09a_phaseCreditSpec_tight_exact
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23050735 294391 294391 286196 :=
  (spqrRecvParts_c07_phaseCreditSpec_tight_exact F K (c09aStatesRecvTightCreditSpec_inst F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- Closed `spqr::recv` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk`
(`Δcum = 23,313,687`, `Δlive = Δpeak = 294,391`, `maxReq = 286,196`). -/
theorem spqrRecvParts_c07_c09a_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391 286196 :=
  (spqrRecvParts_c07_phaseCreditSpec_tight_c09a F K (c09aStatesRecvTightCreditSpec_inst F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrRecvParts_c07_c09a_phaseCreditSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 294391 294391 286196 := by
  rw [← spqrRecvC07TightEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_phaseCreditSpec_tight F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist

/-- Closed `spqr::recv` `PhaseCreditSpec` without assumptions on `xRk.G`
(`Δcum = 23,313,687`, `Δlive = 605,066`, `Δpeak = 621,350`, `maxReq = 302,480`). -/
theorem spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 :=
  (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K
    (c09aStatesRecvTightCreditSpec_inst F) (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 := by
  rw [← spqrRecvC07TightEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom

/-- Affine `fineCredit fineCostModel` upper bound for `SpqrRecvC07TightEnv` at `StatesRecvProtoEnv`.
-/
theorem spqrRecv_c07_c09a_fineCredit_le_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + 23313687 + 294391 :=
  spqrRecv_c07_fineCredit_le_tight F K (c09aStatesRecvTightCreditSpec_inst F) (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist s0 hevs

theorem spqrRecv_c07_c09a_fineCredit_le_tight_exact
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (s0 : fineCostModel.σ) {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCredit fineCostModel (fineCostModel.stepEvents evs s0) ≤
      fineCredit fineCostModel s0 + 23050735 + 294391 :=
  fineCredit_le_of_phaseCreditSpec
    (spqrRecvParts_c07_c09a_phaseCreditSpec_tight_exact F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    (Nat.le_refl 294391) s0 hevs

/-- Footprint upper bound on `fineCostModel.evalLog` for `SpqrRecvC07TightEnv` at `StatesRecvProtoEnv`.
-/
theorem spqrRecv_c07_c09a_evalLog_footprint_le_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := fineCostModel) + 23313687 + 294391 :=
  spqrRecv_c07_evalLog_footprint_le_tight F K (c09aStatesRecvTightCreditSpec_inst F) (by decide)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist hevs

theorem spqrRecv_c07_c09a_evalLog_footprint_le_tight_exact
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    {evs : List AllocEvent}
    (hevs : SpqrRecvC07TightEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    fineCostModel.footprint (fineCostModel.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := fineCostModel) + 23050735 + 294391 :=
  (spqrRecvParts_c07_c09a_phaseCreditSpec_tight_exact F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist
  ).evalLog_footprint_le_of_live_le_peak (Nat.le_refl 294391) hevs

/-! ## Closed `spqr::recv` `PhaseGroupSpec` Bounds -/

/-- Closed `Ordering::Equal` `PhaseGroupSpec` (`ΔgrpS = 684,955,440`, `10,452` groups). -/
theorem spqrRecvOrderingEqual_c07_c09a_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvEqualC07TightEnv F K StatesRecvProtoEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      684955440 := by
  unfold SpqrRecvEqualC07TightEnv
  exact (spqrRecvOrderingEqual_phaseGroupSpec_tight F K
    (c07TightGroupSpec_inst F) (c09aStatesRecvTightGroupSpec_inst F)
    hv1Pts hv1Raw hParams hPrev).mono (by decide)

/-- Closed `spqr::recv` `PhaseGroupSpec` (`ΔgrpS = 701,273,904`, `10,701` groups). -/
theorem spqrRecvParts_c07_c09a_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      701273904 :=
  (spqrRecvParts_c07_phaseGroupSpec_tight F K (c09aStatesRecvTightGroupSpec_inst F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono (by decide)

theorem spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      701273904 := by
  rw [← spqrRecvC07TightEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom

/-- Uniform `≤ 128`-op codec variant of `spqrRecvParts_c07_c09a_phaseGroupSpec_tight` (`741,185,328`, `11,310` groups).
-/
theorem spqrRecvParts_c07_128_c09a_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      741185328 :=
  (spqrRecvParts_c07_128_phaseGroupSpec_tight F K (c09aStatesRecvTightGroupSpec_inst F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono (by decide)

/-! ## `FitsEnv fineCostModel` Corollaries -/

/-- `FitsEnv fineCostModel` bound for `SpqrRecvC07TightEnv` under `nonVacLimits250MiB` (`10,701` groups).
-/
theorem spqrRecvParts_c07_c09a_fitsEnv_groups_250mb
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    FitsEnv fineCostModel nonVacLimits250MiB fineCostModel.init
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 10701)
    (spqrRecvParts_c07_c09a_phaseCreditSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    (Nat.le_refl 294391) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

theorem spqrRecvParts_c07_c09a_rawEnv_fitsEnv_groups_250mb
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    FitsEnv fineCostModel nonVacLimits250MiB fineCostModel.init
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto) := by
  rw [← spqrRecvC07TightEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_fitsEnv_groups_250mb F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist

/-- Unconditional-`xRk.G` `FitsEnv fineCostModel` bound under `nonVacLimits250MiB`. -/
theorem spqrRecvParts_c07_c09a_uncondHist_fitsEnv_groups_250mb
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    FitsEnv fineCostModel nonVacLimits250MiB fineCostModel.init
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 10701)
    (spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    (by decide) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

theorem spqrRecvParts_c07_c09a_fitsEnv_groups
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk) :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init
      (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 10701)
    (spqrRecvParts_c07_c09a_phaseCreditSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    (Nat.le_refl 294391) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
