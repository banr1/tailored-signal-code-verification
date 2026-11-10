/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget

/-!
# Branch-Budget and Linked-Envelope Closure Helpers for `spqr::recv`

Discharges the 27 branch budget (`FitsEnv`) and envelope-closure obligations of
`SpqrRecvBranchHyps` (`FinalPlacedBudgetAux.lean`) for any target envelope closed under
`SpqrRecvTightLinkedEnv`, together with codec and `<States>::recv` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB Direction EpochSecret Message MlKem PqRatchetState States V1Recv V1State
   VersionNegotiationPB chainFrom spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost chainNewVal)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost initV1State)
open CryptoVerification.SpqrV1.Top.Recv (v1ChainAfterKey)
open CryptoVerification.SpqrV1.Top.StateSize
  (Chain.addEpoch_raw_le Chain.new_raw_le chainFrom_raw_le optRaw rawChain)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvC07TightLinkedEnv SpqrRecvGhostLink
   SpqrRecvTightLinkedEnv exists_ghosts_spqrRecvGhostLink mkDefaultChainAddEpochGhost
   mkDefaultChainRecvKeyGhost spqrRecvC07TightLinkedEnv_nil_exists
   spqrRecvGhostLink_of_chain0 spqrRecvGhostLink_of_chainFrom_error
   spqrRecvGhostLink_of_v1ChainAfterKey)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec (OptChainAddEpochEnv V0ChainInitEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (spqrRecvTightEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (ChainAddEpochEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv chainIntoPbAllocEnv_imp_chainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (ChainRecvKeyEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (pqRatchetStateEncodeToVecEnv_events pqRatchetStateEncodeToVecEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromEnv ChainFromVersionNegotiationEnv chainFromAllocEnv_imp_chainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (SpqrRecvBranchHyps fitsEnv_step_of_extend fitsEnv_step_of_prefix)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4PlacedBudgetAux (v1ChainAfterKeyEvents)

/-! ## Default Ghost Witnesses and `v1ChainAfterKey` Helpers -/

def defaultStates (F : ShaCompress) : States spqrPolyApi (spqrAuthApi F) :=
  initV1State F .a2b []

def defaultMessage : Message spqrPolyApi :=
  { epoch := 0#64, payload := .none }

def defaultV1Recv (F : ShaCompress) : V1Recv spqrPolyApi (spqrAuthApi F) :=
  { key := none, state := defaultStates F }

def defaultInitInnerGhost : InitInnerGhost :=
  { out := 0#64, v := .v0, d := .a2b, akPtr := 1#64, authKey := [] }

def defaultChainNewGhost : ChainNewGhost :=
  { out := 0#64
    ikmRO := false
    ikmA := 0#64
    initialKey := []
    dir := .a2b
    params := default }

def defaultStatesIntoPbGhost (F : ShaCompress) : StatesIntoPbGhost F :=
  ⟨0#64, 0#64, defaultStates F⟩

def defaultChainIntoPbCall : ChainIntoPbCall :=
  ⟨0#64, 0#64, (mkDefaultChainRecvKeyGhost default).G, default⟩

/-- Optional `<Chain>::add_epoch` ghost matching `v1ChainAfterKeyEvents`. -/
def mkV1ChainAddEpochGhost (selfPtr esPtr : BitVec 64) (G0 : ChainGhost)
    (kw0 kw1 : BitVec 64) (chain0 : Chain) : Option EpochSecret → ChainAddEpochGhost
  | none => mkDefaultChainAddEpochGhost chain0
  | some es => ⟨selfPtr, esPtr, G0, ⟨kw0, kw1⟩, chain0, es⟩

@[simp]
theorem mkV1ChainAddEpochGhost_self (selfPtr esPtr : BitVec 64) (G0 : ChainGhost)
    (kw0 kw1 : BitVec 64) (chain0 : Chain) (key : Option EpochSecret) :
    (mkV1ChainAddEpochGhost selfPtr esPtr G0 kw0 kw1 chain0 key).self = chain0 := by
  cases key <;> rfl

private theorem seqEnv_assoc {E₁ E₂ : List AllocEvent → Prop} {a b ab : List AllocEvent}
    (h₁ : E₁ a) (h₂ : E₂ b)
    (heq : ab = a ++ b := by
      (try simp only [List.append_assoc, List.nil_append, List.append_nil])
      all_goals exact rfl) :
    SeqEnv E₁ E₂ ab :=
  heq ▸ SeqEnv.append h₁ h₂

private theorem exists_chainFromEnv (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    ∃ evs : List AllocEvent, ChainFromEnv pb vn evs := by
  cases pb with
  | some _ => exact ⟨[], FreeOnlyEvs.nil⟩
  | none =>
    cases vn with
    | none => exact ⟨[], rfl⟩
    | some v =>
      dsimp only [ChainFromEnv, ChainFromVersionNegotiationEnv]
      by_cases h : ((Direction.fromI32? v.direction).isSome && v.chainParams.isSome) = true
      · exact ⟨LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents, by simp [h]⟩
      · exact ⟨[], by simp [h]⟩

private theorem exists_chainIntoPbEnv (x : ChainIntoPbCall) :
    ∃ evs : List AllocEvent, ChainIntoPbEnv x evs := by
  by_cases h : x.chain.links = []
  · refine ⟨[], chainIntoPbAllocEnv_imp_chainIntoPbEnv ?_⟩
    unfold ChainIntoPbAllocEnv
    simp [h]
  · refine ⟨rustAllocEvents (x.chain.links.length * 112) 8,
      chainIntoPbAllocEnv_imp_chainIntoPbEnv ?_⟩
    unfold ChainIntoPbAllocEnv
    simp [h]

private theorem exists_greater_link_and_cap (F : ShaCompress) (K : MlKem)
    {stBytes : Bytes} {pre_pb : PqRatchetState} (sckaMsg : Message spqrPolyApi)
    (hdec : spqrDecodeState stBytes = .ok pre_pb) :
    ∃ (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost),
      SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk ∧
      rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      ChainRecvKeyEnv (spqrHkdfWith F) xRk [] := by
  cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation with
  | error _err =>
    let cDef := chainNewVal (spqrHkdfWith F) [] .a2b default
    have hcDef_raw : rawChain cDef.intoPb ≤ 296 :=
      Chain.new_raw_le (spqrHkdfWith F) [] .a2b default rfl
    refine ⟨mkDefaultChainAddEpochGhost cDef, mkDefaultChainRecvKeyGhost cDef,
      spqrRecvGhostLink_of_chainFrom_error hdec hcf, ?_, rfl⟩
    change rawChain cDef.intoPb ≤ optRaw rawChain pre_pb.chain + 296
    omega
  | ok ch0 =>
    have hch0_raw := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    exact ⟨mkDefaultChainAddEpochGhost ch0, mkDefaultChainRecvKeyGhost ch0,
      spqrRecvGhostLink_of_chain0 hdec hcf rfl rfl, hch0_raw, rfl⟩

private theorem v1ChainAfterKey_rawChain_le_1058 (F : ShaCompress)
    {pre_pb : PqRatchetState} {chain0 chain1 : Chain} {key : Option EpochSecret}
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hAfter : v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1) :
    rawChain chain1.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 := by
  have hc0 := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
  cases key with
  | none =>
    dsimp only [v1ChainAfterKey] at hAfter
    injection hAfter with hEq
    subst hEq
    omega
  | some es =>
    dsimp only [v1ChainAfterKey] at hAfter
    have hadd := Chain.addEpoch_raw_le (spqrHkdfWith F) chain0 es hAfter
    omega

private theorem v1ChainAfterKey_optChainAddEpochEnv (F : ShaCompress)
    (selfPtr esPtr : BitVec 64) (G0 : ChainGhost) (kw0 kw1 : BitVec 64)
    {chain0 chain1 : Chain} {key : Option EpochSecret}
    (hAfter : v1ChainAfterKey (spqrHkdfWith F) chain0 key = .ok chain1) :
    OptChainAddEpochEnv F key
      (mkV1ChainAddEpochGhost selfPtr esPtr G0 kw0 kw1 chain0 key)
      (v1ChainAfterKeyEvents selfPtr esPtr G0 kw0 kw1 chain0 key) := by
  cases key with
  | none => rfl
  | some es =>
    dsimp only [v1ChainAfterKey] at hAfter
    unfold OptChainAddEpochEnv mkV1ChainAddEpochGhost v1ChainAfterKeyEvents ChainAddEpochEnv
    dsimp only
    rw [hAfter]

theorem spqrRecvTightLinkedEnv_nil_exists
    (F : ShaCompress) (K : MlKem)
    (DecodeStateEnv' : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv' : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes) :
    ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] := by
  obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K stBytes defaultMessage
  exact ⟨default, default, default, defaultStates F, defaultMessage, defaultV1Recv F,
    defaultInitInnerGhost, defaultChainNewGhost, xAdd, xRk, defaultStatesIntoPbGhost F,
    defaultChainIntoPbCall,
    spqrRecvTightEnv_nil F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv'
      stBytes default default default (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall,
    hLink⟩

theorem spqrRecvC07C09aTightLinkedEnv_nil_exists
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes) :
    ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      SpqrRecvC07C09aTightLinkedEnv F K
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] := by
  obtain ⟨xAdd, xRk, hNil⟩ := spqrRecvC07TightLinkedEnv_nil_exists F K StatesRecvProtoEnv
    stBytes default default default (defaultStates F) defaultMessage (defaultV1Recv F)
    defaultInitInnerGhost defaultChainNewGhost (defaultStatesIntoPbGhost F)
    defaultChainIntoPbCall
  exact ⟨default, default, default, defaultStates F, defaultMessage, defaultV1Recv F,
    defaultInitInnerGhost, defaultChainNewGhost, xAdd, xRk, defaultStatesIntoPbGhost F,
    defaultChainIntoPbCall, hNil⟩

/-! ## Discharging `SpqrRecvBranchHyps` for `SpqrRecvTightLinkedEnv` -/

/-- Discharges all branch budget (`FitsEnv`) and envelope-closure obligations of `SpqrRecvBranchHyps` for any `Env` closed under `SpqrRecvTightLinkedEnv`.
-/
theorem spqrRecvBranchHyps_tightLinked {MC : AllocCostModel}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {DecodeStateEnv' : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv' : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    (st msg : VecArg) (s0 : State) (st_cost : MC.σ)
    (hDecPre : ∀ evs, DecodePreEnv ⟨st, s0.sp - 3056#64⟩ evs → DecodeStateEnv' st.bytes evs)
    (hDecPost : ∀ evs, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs → DecodeStateEnv' st.bytes evs)
    (hFromPb : ∀ pb evs, FromPbEnv pb evs → StatesFromPbEnv' pb evs)
    (hRecv : ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi) evs,
      RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs →
      StatesRecvEnv' st0 sckaMsg evs)
    (hIntoPb : ∀ (st1 : States spqrPolyApi (spqrAuthApi F)) evs,
      IntoPbEnv ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs →
      StatesIntoPbEnv' ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩ evs)
    (hfit : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      FitsEnv MC lim st_cost
        (SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
          StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto))
    (hEnv : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs,
      SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
        StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs →
      Env evs) :
    SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv (InitInnerEnv F)
      FromPbEnv RecvEnv IntoPbEnv Env st msg s0 st_cost where
  env_nil := by
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    exact hEnv default default default (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall []
      ⟨spqrRecvTightEnv_nil F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv'
        st.bytes default default default (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall, hLink⟩
  fit_dec := by
    intro _pre _hpre
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine FitsEnv.mono ?_
      (hfit default default default (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall)
    intro evs_dec hpre_dec
    exact ⟨Or.inr (seqEnv_assoc (hDecPre evs_dec hpre_dec) (Or.inl FreeOnlyEvs.nil)), hLink⟩
  env_dec_free := by
    intro _pre evs_dec evs_d _hpre hdec hd
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    exact hEnv default default default (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall (evs_dec ++ evs_d)
      ⟨Or.inr (SeqEnv.append (hDecPost evs_dec hdec) (Or.inl hd)), hLink⟩
  gt_fit_cf := by
    intro _pre pre_pb vn pb evs_dec _hpre hdec hvn hinner _hmin _hgt hpost_dec
    obtain ⟨xAdd, xRk, hLink, hRkRaw, hRkNil⟩ :=
      exists_greater_link_and_cap F K defaultMessage hdec
    refine fitsEnv_step_of_prefix
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_cf hcf_alloc
    have hcf : V0ChainInitEnv pre_pb vn defaultChainNewGhost evs_cf :=
      Or.inr (Or.inr (chainFromAllocEnv_imp_chainFromEnv hcf_alloc))
    refine ⟨Or.inr (SeqEnv.append (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)), hLink⟩
    exact seqEnv_assoc hcf (seqEnv_assoc hRkNil (Or.inl FreeOnlyEvs.nil))
  gt_fit_rk := by
    intro pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 _hpre hdec hvn hinner _hmin _hgt
      hpost_dec hcf_env hcf
    let xAdd := mkDefaultChainAddEpochGhost chain0
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
    have hcf_opt : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 :=
      by rwa [hvn]
    have hLink : SpqrRecvGhostLink F K st.bytes defaultMessage xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf_opt rfl rfl
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 :=
      chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
    refine fitsEnv_step_of_prefix
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_rk hrk_env
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)
    exact SeqEnv.append (Or.inr (Or.inr hcf_env)) (seqEnv_assoc hrk_env (Or.inl FreeOnlyEvs.nil))
  gt_fit_into := by
    intro pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain
      _hpre hdec hvn hinner _hmin _hgt hpost_dec hcf_env hcf hrk
    let xAdd := mkDefaultChainAddEpochGhost chain0
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩
    let stOut : PqRatchetState :=
      { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }
    have hcf_opt : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 :=
      by rwa [hvn]
    have hLink : SpqrRecvGhostLink F K st.bytes defaultMessage xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf_opt rfl rfl
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 :=
      chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
    refine fitsEnv_step_of_extend
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) xCInto) ?_
    intro evs_into hinto_alloc
    refine ⟨pqRatchetStateEncodeToVecEvents stOut, Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)
    refine seqEnv_assoc (Or.inr (Or.inr hcf_env)) ?_
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    exact SeqEnv.append (chainIntoPbAllocEnv_imp_chainIntoPbEnv hinto_alloc)
      (seqEnv_assoc (pqRatchetStateEncodeToVecEnv_events stOut) FreeOnlyEvs.nil)
  gt_fit_enc := by
    intro pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain evs_into
      _hpre hdec hvn hinner _hmin _hgt hpost_dec hcf_env hcf hrk hinto_env
    let xAdd := mkDefaultChainAddEpochGhost chain0
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩
    have hcf_opt : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 :=
      by rwa [hvn]
    have hLink : SpqrRecvGhostLink F K st.bytes defaultMessage xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf_opt rfl rfl
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 :=
      chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
    refine fitsEnv_step_of_prefix
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) xCInto) ?_
    intro evs_enc henc_env
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)
    refine seqEnv_assoc (Or.inr (Or.inr hcf_env)) ?_
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    exact SeqEnv.append hinto_env (seqEnv_assoc henc_env FreeOnlyEvs.nil)
  gt_env_rk_err := by
    intro pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 _e evs_d
      _hpre hdec hvn hinner _hmin _hgt hpost_dec hcf_env hcf _hrk_err hd
    let xAdd := mkDefaultChainAddEpochGhost chain0
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
    have hcf_opt : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 :=
      by rwa [hvn]
    have hLink : SpqrRecvGhostLink F K st.bytes defaultMessage xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf_opt rfl rfl
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 :=
      chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
    refine hEnv pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall _ ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)
    refine seqEnv_assoc (Or.inr (Or.inr hcf_env)) ?_
    exact SeqEnv.append (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inl hd)
  gt_env_rk_ok := by
    intro pre pre_pb vn pb evs_dec evs_cf chain0 G_c0 chain1 rawKey gChain
      evs_into evs_enc evs_d _hpre hdec hvn hinner _hmin _hgt hpost_dec hcf_env hcf hrk
      hinto_env henc_env hd
    let xAdd := mkDefaultChainAddEpochGhost chain0
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩
    have hcf_opt : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0 :=
      by rwa [hvn]
    have hLink : SpqrRecvGhostLink F K st.bytes defaultMessage xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf_opt rfl rfl
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 :=
      chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
    refine hEnv pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) xCInto _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec)
      (Or.inr ⟨hdec, Or.inr (Or.inl ⟨hvn, hinner, Or.inr ⟨hRkRaw, ?_⟩⟩)⟩)
    refine seqEnv_assoc (Or.inr (Or.inr hcf_env)) ?_
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    exact seqEnv_assoc hinto_env (SeqEnv.append henc_env hd)
  lt_fit_init := by
    intro _pre pre_pb vn pb w1 dir evs_dec _hpre hdec hvn _hinner _hmin _hlt hpost_dec _hdir
    let xInit : InitInnerGhost := ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    obtain ⟨evs_cf, hcf_env⟩ := exists_chainFromEnv pre_pb.chain (some vn)
    refine fitsEnv_step_of_extend
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        xInit defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_init hinit_env
    refine ⟨evs_cf, Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inl ⟨hvn, rfl, Or.inr ?_⟩⟩)
    exact SeqEnv.append hinit_env (seqEnv_assoc hcf_env (Or.inl FreeOnlyEvs.nil))
  lt_fit_cf := by
    intro _pre pre_pb vn pb w1 dir evs_dec evs_init _hpre hdec hvn _hinner _hmin _hlt
      hpost_dec _hdir hinit_env
    let xInit : InitInnerGhost := ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine fitsEnv_step_of_prefix
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        xInit defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_cf hcf_alloc
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inl ⟨hvn, rfl, Or.inr ?_⟩⟩)
    exact SeqEnv.append hinit_env
      (seqEnv_assoc (chainFromAllocEnv_imp_chainFromEnv hcf_alloc) (Or.inl FreeOnlyEvs.nil))
  lt_fit_into := by
    intro _pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf ch G
      _hpre hdec hvn _hinner _hmin _hlt hpost_dec _hdir hinit_env hcf_env hcf
    let xInit : InitInnerGhost := ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine fitsEnv_step_of_prefix
      (hfit pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
        xInit defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) xCInto) ?_
    intro evs_into hinto_alloc
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inl ⟨hvn, rfl, Or.inr ?_⟩⟩)
    refine seqEnv_assoc hinit_env ?_
    exact SeqEnv.append hcf_env (Or.inr ⟨hcf,
      seqEnv_assoc (chainIntoPbAllocEnv_imp_chainIntoPbEnv hinto_alloc) FreeOnlyEvs.nil⟩)
  lt_env_err := by
    intro _pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf evs_d
      _hpre hdec hvn _hinner _hmin _hlt hpost_dec _hdir hinit_env hcf_env hd
    let xInit : InitInnerGhost := ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine hEnv pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
      xInit defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) defaultChainIntoPbCall _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inl ⟨hvn, rfl, Or.inr ?_⟩⟩)
    exact seqEnv_assoc hinit_env (SeqEnv.append hcf_env (Or.inl hd))
  lt_env_ok := by
    intro _pre pre_pb vn pb w1 dir evs_dec evs_init evs_cf ch G evs_into evs_d
      _hpre hdec hvn _hinner _hmin _hlt hpost_dec _hdir hinit_env hcf_env hcf hinto_env hd
    let xInit : InitInnerGhost := ⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine hEnv pre_pb vn pb (defaultStates F) defaultMessage (defaultV1Recv F)
      xInit defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F) xCInto _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inl ⟨hvn, rfl, Or.inr ?_⟩⟩)
    refine seqEnv_assoc hinit_env ?_
    exact seqEnv_assoc hcf_env (Or.inr ⟨hcf, SeqEnv.append hinto_env hd⟩)
  v1_fit_fpb := by
    intro _pre pre_pb pb evs_dec evs_md _hpre hdec hinner _heq _hmin hpost_dec hmd
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb (defaultStates F) defaultMessage (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_fpb hfpb
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    exact SeqEnv.append hmd (Or.inr (seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inl FreeOnlyEvs.nil)))
  v1_env_fpb_err := by
    intro _pre pre_pb pb evs_dec evs_md evs_fpb evs_d
      _hpre hdec hinner _heq _hmin hpost_dec hmd hfpb hd
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes defaultMessage
    refine hEnv pre_pb default pb (defaultStates F) defaultMessage (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall _ ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    exact seqEnv_assoc hmd (Or.inr (SeqEnv.append (hFromPb pb evs_fpb hfpb) (Or.inl hd)))
  v1_fit_rcv := by
    intro _pre pre_pb pb sckaMsg st0 evs_dec evs_md evs_fpb
      _hpre hdec hinner _heq _hmin _hmsg hfrom hpost_dec hmd hfpb
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes sckaMsg
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb st0 sckaMsg (defaultV1Recv F)
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
        defaultChainIntoPbCall) ?_
    intro evs_rcv hrcv
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    exact SeqEnv.append (hFromPb pb evs_fpb hfpb)
      (Or.inr ⟨hfrom, seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inl FreeOnlyEvs.nil)⟩)
  v1_env_rcv_err := by
    intro _pre pre_pb pb sckaMsg st0 evs_dec evs_md evs_fpb evs_rcv evs_d
      _hpre hdec hinner _heq _hmin _hmsg hfrom hpost_dec hmd hfpb hrcv hd
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes sckaMsg
    refine hEnv pre_pb default pb st0 sckaMsg (defaultV1Recv F)
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk (defaultStatesIntoPbGhost F)
      defaultChainIntoPbCall _ ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    exact seqEnv_assoc (hFromPb pb evs_fpb hfpb)
      (Or.inr ⟨hfrom, SeqEnv.append (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inl hd)⟩)
  v1_fit_cf := by
    intro _pre pre_pb pb sckaMsg st0 v evs_dec evs_md evs_fpb evs_rcv
      _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv hpost_dec hmd hfpb hrcv
    obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K st.bytes sckaMsg
    let xSInto : StatesIntoPbGhost F := ⟨0#64, 0#64, v.state⟩
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto defaultChainIntoPbCall) ?_
    intro evs_cf hcf_alloc
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    exact SeqEnv.append (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl,
      seqEnv_assoc (chainFromAllocEnv_imp_chainFromEnv hcf_alloc) (Or.inl FreeOnlyEvs.nil)⟩)
  v1_env_cf_err := by
    intro _pre pre_pb pb sckaMsg st0 v _err evs_dec evs_md evs_fpb evs_rcv evs_cf evs_d
      _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv hcf_err hpost_dec hmd hfpb hrcv hcf_env hd
    let xAdd := mkDefaultChainAddEpochGhost default
    let xRk := mkDefaultChainRecvKeyGhost default
    let xSInto : StatesIntoPbGhost F := ⟨0#64, 0#64, v.state⟩
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_chainFrom_error hdec hcf_err
    refine hEnv pre_pb default pb st0 sckaMsg v
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto defaultChainIntoPbCall _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    exact seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv)
      (Or.inr ⟨hrecv, rfl, SeqEnv.append hcf_env (Or.inl hd)⟩)
  v1_fit_add := by
    intro _pre pre_pb pb sckaMsg st0 v kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
      chain0 G0 es _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hv_key
    let xAdd : ChainAddEpochGhost :=
      ⟨s0.sp - 232#64, s0.sp - 3056#64, G0, ⟨kw0, kw1⟩, chain0, es⟩
    let xRk := mkDefaultChainRecvKeyGhost chain0
    let xSInto : StatesIntoPbGhost F := ⟨0#64, 0#64, v.state⟩
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_chain0 hdec hcf rfl rfl
    have hc0_raw := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRk_raw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 := by
      change rawChain chain0.intoPb ≤ optRaw rawChain pre_pb.chain + 1058
      omega
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto defaultChainIntoPbCall) ?_
    intro evs_add hadd_env
    have hopt_add : OptChainAddEpochEnv F v.key xAdd evs_add := by
      rw [hv_key]
      exact hadd_env
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    exact SeqEnv.append hcf_env
      (Or.inr ⟨hc0_raw, hRk_raw, seqEnv_assoc hopt_add (Or.inl FreeOnlyEvs.nil)⟩)
  v1_fit_rk := by
    intro pre pre_pb pb sckaMsg st0 v kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
      chain0 chain1 G0 G1 _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨0#64, 0#64, v.state⟩
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto defaultChainIntoPbCall) ?_
    intro evs_rk hrk_env
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    exact SeqEnv.append hOptAdd (Or.inr (seqEnv_assoc hrk_env (Or.inl FreeOnlyEvs.nil)))
  v1_env_rk_err := by
    intro pre pre_pb pb sckaMsg st0 v kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
      chain0 chain1 G0 G1 _err evs_d _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter _hrk_err hd
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨0#64, 0#64, v.state⟩
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 v.key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    refine hEnv pre_pb default pb st0 sckaMsg v
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto defaultChainIntoPbCall _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    exact seqEnv_assoc hOptAdd
      (Or.inr (SeqEnv.append (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inl hd)))
  v1_fit_sip := by
    intro pre pre_pb pb sckaMsg st0 st1 key kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf
      chain0 chain1 chain2 G0 G1 rawKey _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter hrk
    let v : V1Recv spqrPolyApi (spqrAuthApi F) := ⟨key, st1⟩
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 232#64, G1, chain2⟩
    let stOut : PqRatchetState :=
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    obtain ⟨evs_cip, hcip_env⟩ := exists_chainIntoPbEnv xCInto
    refine fitsEnv_step_of_extend
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto xCInto) ?_
    intro evs_sip hsip
    refine ⟨evs_cip ++ pqRatchetStateEncodeToVecEvents stOut, Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    refine seqEnv_assoc hOptAdd (Or.inr ?_)
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    exact seqEnv_assoc (hIntoPb st1 evs_sip hsip)
      (SeqEnv.append hcip_env (seqEnv_assoc (pqRatchetStateEncodeToVecEnv_events stOut) FreeOnlyEvs.nil))
  v1_fit_cip := by
    intro pre pre_pb pb sckaMsg st0 st1 key kw0 kw1 evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip
      chain0 chain1 chain2 G0 G1 G2 rawKey _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter hrk hsip
    let v : V1Recv spqrPolyApi (spqrAuthApi F) := ⟨key, st1⟩
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩
    let stOut : PqRatchetState :=
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    refine fitsEnv_step_of_extend
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto xCInto) ?_
    intro evs_cip hcip_alloc
    refine ⟨pqRatchetStateEncodeToVecEvents stOut, Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    refine seqEnv_assoc hOptAdd (Or.inr ?_)
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    refine seqEnv_assoc (hIntoPb st1 evs_sip hsip) ?_
    exact SeqEnv.append (chainIntoPbAllocEnv_imp_chainIntoPbEnv hcip_alloc)
      (seqEnv_assoc (pqRatchetStateEncodeToVecEnv_events stOut) FreeOnlyEvs.nil)
  v1_fit_enc := by
    intro pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
      evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip
      chain0 chain1 chain2 G0 G1 G2 rawKey _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter hrk hsip hcip
    let v : V1Recv spqrPolyApi (spqrAuthApi F) := ⟨key, st1⟩
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    refine fitsEnv_step_of_prefix
      (hfit pre_pb default pb st0 sckaMsg v
        defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto xCInto) ?_
    intro evs_enc henc
    refine ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    refine seqEnv_assoc hOptAdd (Or.inr ?_)
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    refine seqEnv_assoc (hIntoPb st1 evs_sip hsip) ?_
    exact SeqEnv.append hcip (seqEnv_assoc henc FreeOnlyEvs.nil)
  v1_env_ok := by
    intro pre pre_pb pb sckaMsg st0 st1 key kw0 kw1
      evs_dec evs_md evs_fpb evs_rcv evs_cf evs_sip evs_cip evs_enc evs_d
      chain0 chain1 chain2 G0 G1 G2 rawKey _hpre hdec hinner _heq _hmin _hmsg hfrom hrecv
      hpost_dec hmd hfpb hrcv hcf_env hcf hAfter hrk hsip hcip henc hd
    let v : V1Recv spqrPolyApi (spqrAuthApi F) := ⟨key, st1⟩
    let xAdd := mkV1ChainAddEpochGhost (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    let xRk : ChainRecvKeyGhost :=
      ⟨s0.sp - 3056#64, s0.sp - 232#64, pre.epoch - 1#64, pre.index, G1, chain1⟩
    let xSInto : StatesIntoPbGhost F := ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    let xCInto : ChainIntoPbCall := ⟨s0.sp - 3008#64, s0.sp - 232#64, G2, chain2⟩
    have hAddSelf : xAdd.self = chain0 :=
      mkV1ChainAddEpochGhost_self (s0.sp - 232#64) (s0.sp - 3056#64) G0 kw0 kw1 chain0 key
    have hLink : SpqrRecvGhostLink F K st.bytes sckaMsg xAdd xRk :=
      spqrRecvGhostLink_of_v1ChainAfterKey hdec hcf hinner hfrom hrecv hAddSelf hAfter
    have hAddRaw : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 := by
      rw [hAddSelf]
      exact chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation hcf
    have hRkRaw : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 :=
      v1ChainAfterKey_rawChain_le_1058 F hcf hAfter
    have hOptAdd := v1ChainAfterKey_optChainAddEpochEnv F (s0.sp - 232#64) (s0.sp - 3056#64)
      G0 kw0 kw1 hAfter
    refine hEnv pre_pb default pb st0 sckaMsg v
      defaultInitInnerGhost defaultChainNewGhost xAdd xRk xSInto xCInto _
      ⟨Or.inr ?_, hLink⟩
    refine seqEnv_assoc (hDecPost evs_dec hpost_dec) (Or.inr ⟨hdec, Or.inr (Or.inr ⟨hinner, ?_⟩)⟩)
    refine seqEnv_assoc hmd (Or.inr ?_)
    refine seqEnv_assoc (hFromPb pb evs_fpb hfpb) (Or.inr ⟨hfrom, ?_⟩)
    refine seqEnv_assoc (hRecv st0 sckaMsg evs_rcv hrcv) (Or.inr ⟨hrecv, rfl, ?_⟩)
    refine seqEnv_assoc hcf_env (Or.inr ⟨hAddRaw, hRkRaw, ?_⟩)
    refine seqEnv_assoc hOptAdd (Or.inr ?_)
    refine seqEnv_assoc (rfl : ChainRecvKeyEnv (spqrHkdfWith F) xRk _) (Or.inr ⟨⟨rawKey, hrk⟩, ?_⟩)
    refine seqEnv_assoc (hIntoPb st1 evs_sip hsip) ?_
    exact seqEnv_assoc hcip (SeqEnv.append henc hd)

theorem spqrRecvBranchHyps_c07TightLinked {MC : AllocCostModel}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {Env : List AllocEvent → Prop}
    (st msg : VecArg) (s0 : State) (st_cost : MC.σ)
    (hfit : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      FitsEnv MC lim st_cost
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto))
    (hEnv : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs,
      SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs →
      Env evs) :
    SpqrRecvBranchHyps lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      Env st msg s0 st_cost :=
  spqrRecvBranchHyps_tightLinked st msg s0 st_cost
    (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
    hfit hEnv

theorem spqrRecvBranchHyps_c07c09aTightLinked {MC : AllocCostModel}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {Env : List AllocEvent → Prop}
    (st msg : VecArg) (s0 : State) (st_cost : MC.σ)
    (hfit : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      FitsEnv MC lim st_cost
        (SpqrRecvC07C09aTightLinkedEnv F K
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto))
    (hEnv : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs,
      SpqrRecvC07C09aTightLinkedEnv F K
        st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs →
      Env evs) :
    SpqrRecvBranchHyps lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      Env st msg s0 st_cost :=
  spqrRecvBranchHyps_c07TightLinked st msg s0 st_cost hfit hEnv

theorem spqrRecvBranchHyps_c07c09aRawTightLinked {MC : AllocCostModel}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {Env : List AllocEvent → Prop}
    (st msg : VecArg) (s0 : State) (st_cost : MC.σ)
    (hfit : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      FitsEnv MC lim st_cost
        (SpqrRecvC07TightLinkedEnv F K
          LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec.StatesRecvEnv
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto))
    (hEnv : ∀ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs,
      SpqrRecvC07TightLinkedEnv F K
        LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec.StatesRecvEnv
        st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs →
      Env evs) :
    SpqrRecvBranchHyps lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec.StatesRecvEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv)
      Env st msg s0 st_cost :=
  spqrRecvBranchHyps_c07TightLinked st msg s0 st_cost hfit hEnv

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
