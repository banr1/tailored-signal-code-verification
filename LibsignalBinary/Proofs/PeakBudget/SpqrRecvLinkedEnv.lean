/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet4

@[expose] public section

set_option autoImplicit false

/-!
# Pure Ghost Link and Linked Tight Envelopes for `spqr::recv`

Defines the quantifier-free ghost relation `SpqrRecvGhostLink` tying the `spqr::recv` chain-call
ghosts `(xAdd.self, xRk.self)` to `spqrDecodeState stBytes`, `chainFrom`, and `v1ChainAfterKey`,
along with the linked envelopes `SpqrRecvTightLinkedEnv`, `SpqrRecvC07TightLinkedEnv`, and
`SpqrRecvC07C09aTightLinkedEnv`. Discharges `SpqrRecvTightDomain` directly from `TopStateTight` and
`SpqrRecvGhostLink` (`spqrRecvTightDomain_of_topStateTight_and_link`).
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainParamsPB Direction EpochSecret Message MlKem PqRatchetState States V1Recv
   V1State VersionNegotiationPB chainFrom spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost VecPin)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv (v1ChainAfterKey)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (SpqrRecvC07C09aTightEnv spqrRecvC07TightEnv_proto_eq spqrRecvTightEnv_proto_eq)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvTightDomain SpqrRecvTightEnv spqrRecvC07TightEnv_nil
   spqrRecvTightEnv_nil)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvEnv StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_decode_props topStateTight_length_le topStateTight_to_tightValid640)

/-! ## `SpqrRecvGhostLink` and Linked Envelopes -/

/-- Links `(xAdd.self, xRk.self)` to `spqrDecodeState stBytes`, `chainFrom`, and (on the V1 ratchet
path) `v1ChainAfterKey`. Under `TopStateTight F K stBytes`, both `spqrDecodeState` and `chainFrom`
succeed, while on malformed inputs the `SpqrRecvTightEnv` conjunct in the linked envelope still
bounds `evs`. -/
def SpqrRecvGhostLink (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes) (sckaMsg : Message spqrPolyApi)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost) : Prop :=
  match spqrDecodeState stBytes with
  | .error _ => True
  | .ok pre_pb =>
    match chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation with
    | .error _ => True
    | .ok ch0 =>
      xAdd.self = ch0 ∧
      (xRk.self = ch0 ∨
        match pre_pb.inner with
        | some (.v1 pb) =>
          match States.from_pb spqrPolyApi (spqrAuthApi F) pb with
          | .ok st0 =>
            match States.recv K st0 sckaMsg with
            | .ok v => v1ChainAfterKey (spqrHkdfWith F) ch0 v.key = .ok xRk.self
            | .error _ => False
          | .error _ => False
        | _ => False)

/-- Linked counterpart of `SpqrRecvTightEnv` conjoined with `SpqrRecvGhostLink`. -/
def SpqrRecvTightLinkedEnv (F : ShaCompress) (K : MlKem)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv'
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs ∧
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk

/-- Codec-instantiated linked envelope (`SpqrRecvC07TightEnv` conjoined with `SpqrRecvGhostLink`).
-/
def SpqrRecvC07TightLinkedEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvC07TightEnv F K StatesRecvEnv'
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs ∧
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk

/-- Closed linked envelope specialized to `StatesRecvProtoEnv`. -/
def SpqrRecvC07C09aTightLinkedEnv (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-! ## `StatesRecvProtoEnv = StatesRecvEnv` Bridges and Constructors -/

theorem spqrRecvTightLinkedEnv_proto_eq
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
    SpqrRecvTightLinkedEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =
    SpqrRecvTightLinkedEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto := by
  funext evs
  unfold SpqrRecvTightLinkedEnv
  rw [spqrRecvTightEnv_proto_eq]

theorem spqrRecvC07TightLinkedEnv_proto_eq
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =
    SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto := by
  funext evs
  unfold SpqrRecvC07TightLinkedEnv
  rw [spqrRecvC07TightEnv_proto_eq]

theorem spqrRecvGhostLink_of_decode_error
    {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {sckaMsg : Message spqrPolyApi}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {err : CryptoVerification.LibsignalSpqrV1.Error}
    (hdec : spqrDecodeState stBytes = .error err) :
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk := by
  unfold SpqrRecvGhostLink
  rw [hdec]
  trivial

theorem spqrRecvGhostLink_of_chainFrom_error
    {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pre_pb : PqRatchetState} {sckaMsg : Message spqrPolyApi}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {err : CryptoVerification.LibsignalSpqrV1.Error}
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error err) :
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk := by
  unfold SpqrRecvGhostLink
  rw [hdec]; dsimp only
  rw [hcf]
  trivial

/-- Constructs `SpqrRecvGhostLink` when `chainFrom = .ok ch0` and `xAdd.self = xRk.self = ch0`. -/
theorem spqrRecvGhostLink_of_chain0
    {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pre_pb : PqRatchetState} {ch0 : Chain} {sckaMsg : Message spqrPolyApi}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok ch0)
    (hAdd : xAdd.self = ch0)
    (hRk : xRk.self = ch0) :
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk := by
  unfold SpqrRecvGhostLink
  rw [hdec]; dsimp only
  rw [hcf]
  exact ⟨hAdd, Or.inl hRk⟩

/-- Constructs `SpqrRecvGhostLink` on the `Ordering::Equal` V1 ratchet path after `States.recv` and `v1ChainAfterKey`.
-/
theorem spqrRecvGhostLink_of_v1ChainAfterKey
    {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {ch0 : Chain}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok ch0)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v)
    (hAdd : xAdd.self = ch0)
    (hAfter : v1ChainAfterKey (spqrHkdfWith F) ch0 v.key = .ok xRk.self) :
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk := by
  unfold SpqrRecvGhostLink
  rw [hdec]; dsimp only
  rw [hcf]; dsimp only
  rw [hinner]; dsimp only
  rw [hfrom]; dsimp only
  rw [hrecv]
  exact ⟨hAdd, Or.inr hAfter⟩

def mkDefaultChainAddEpochGhost (c : Chain) : ChainAddEpochGhost :=
  { selfPtr := 0#64
    esPtr := 0#64
    G :=
      { linksCap := 0#64
        linksPtr := 1#64
        linksHead := 0#64
        epochs := []
        nextRoot := { cap := 0#64, ptr := 1#64 } }
    esPin := { cap := 0#64, ptr := 1#64 }
    self := c
    epochSecret := default }

def mkDefaultChainRecvKeyGhost (c : Chain) : ChainRecvKeyGhost :=
  { out := 0#64
    selfPtr := 0#64
    epoch := 0#64
    index := 0#32
    G :=
      { linksCap := 0#64
        linksPtr := 1#64
        linksHead := 0#64
        epochs := []
        nextRoot := { cap := 0#64, ptr := 1#64 } }
    self := c }

/-- Every `(F, K, stBytes, sckaMsg)` admits default chain ghosts `(xAdd, xRk)` satisfying `SpqrRecvGhostLink`.
-/
theorem exists_ghosts_spqrRecvGhostLink
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes) (sckaMsg : Message spqrPolyApi) :
    ∃ (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost),
      SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk := by
  cases hdec : spqrDecodeState stBytes with
  | error err =>
    exact ⟨mkDefaultChainAddEpochGhost default, mkDefaultChainRecvKeyGhost default,
      spqrRecvGhostLink_of_decode_error hdec⟩
  | ok pre_pb =>
    cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation with
    | error err =>
      exact ⟨mkDefaultChainAddEpochGhost default, mkDefaultChainRecvKeyGhost default,
        spqrRecvGhostLink_of_chainFrom_error hdec hcf⟩
    | ok ch0 =>
      exact ⟨mkDefaultChainAddEpochGhost ch0, mkDefaultChainRecvKeyGhost ch0,
        spqrRecvGhostLink_of_chain0 hdec hcf rfl rfl⟩

theorem spqrRecvC07TightLinkedEnv_nil_exists
    (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    ∃ (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost),
      SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] := by
  obtain ⟨xAdd, xRk, hLink⟩ := exists_ghosts_spqrRecvGhostLink F K stBytes sckaMsg
  exact ⟨xAdd, xRk, spqrRecvC07TightEnv_nil F K StatesRecvEnv'
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto, hLink⟩

/-! ## Discharging `SpqrRecvTightDomain` from `TopStateTight` and `SpqrRecvGhostLink` -/

/-- Derives `SpqrRecvTightDomain F K stBytes xAdd xRk` from `TopStateTight` and `SpqrRecvGhostLink`.
-/
theorem spqrRecvTightDomain_of_topStateTight_and_link
    {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {sckaMsg : Message spqrPolyApi}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    (hTop : TopStateTight F K stBytes)
    (hLink : SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk) :
    SpqrRecvTightDomain F K stBytes xAdd xRk := by
  obtain ⟨hPts, hChainParams, _⟩ := topStateTight_to_tightValid640 hTop
  refine SpqrRecvTightDomain.ofRawOutCaps (topStateTight_length_le hTop) hPts hChainParams ?_
  intro pre_pb hdec
  obtain ⟨hvn, hcLinks, hv1Pre, ch0, hcf, hch0_links, hch0_small, hch0_cp, hch0_rc, hv1Post⟩ :=
    topStateTight_decode_props hTop hdec
  have hLinkDec :
      xAdd.self = ch0 ∧
      (xRk.self = ch0 ∨
        match pre_pb.inner with
        | some (.v1 pb) =>
          match States.from_pb spqrPolyApi (spqrAuthApi F) pb with
          | .ok st0 =>
            match States.recv K st0 sckaMsg with
            | .ok v => v1ChainAfterKey (spqrHkdfWith F) ch0 v.key = .ok xRk.self
            | .error _ => False
          | .error _ => False
        | _ => False) := by
    unfold SpqrRecvGhostLink at hLink
    rw [hdec] at hLink; dsimp only at hLink
    rw [hcf] at hLink
    exact hLink
  obtain ⟨hAddEq, hRkCases⟩ := hLinkDec
  have hAddLinks4 : xAdd.self.links.length ≤ 4 := by
    rw [hAddEq]
    exact Nat.le_trans hch0_links (by decide)
  have hcLinks4 : ∀ c, pre_pb.chain = some c → c.links.length ≤ 4 :=
    fun c hc => Nat.le_trans (hcLinks c hc) (by decide)
  have hv1PreRaw : ∀ pb, pre_pb.inner = some (.v1 pb) →
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State pb ≤ 46880 :=
    fun pb hpb => (hv1Pre pb hpb).1
  have hv1PostRaw : ∀ (pb : V1State) (st0 : States spqrPolyApi (spqrAuthApi F))
      (sckaMsg' : Message spqrPolyApi) (v : V1Recv spqrPolyApi (spqrAuthApi F)),
      pre_pb.inner = some (.v1 pb) →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg' = .ok v →
      CryptoVerification.SpqrV1.Top.StateSize.rawV1State v.state.into_pb ≤ 46880 :=
    fun pb st0 sckaMsg' v hi hfrom hrecv => (hv1Post pb st0 sckaMsg' v hi hfrom hrecv).1
  have ⟨hRkLinks4, hRkSmall, hRkCp, hRkRc⟩ :
      xRk.self.links.length ≤ 4 ∧
      CryptoVerification.SpqrV1Sync.SendTotal.RecvSmallTight xRk.self ∧
      LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps.ValidChainParamsPB xRk.self.params ∧
      (∀ c : Chain,
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
        CryptoVerification.SpqrV1.Top.StateSize.rawChain c.intoPb ≤ 238532) := by
    rcases hRkCases with hRk0 | hRkV1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hRk0]; exact Nat.le_trans hch0_links (by decide)
      · rw [hRk0]; exact hch0_small
      · rw [hRk0]; exact hch0_cp
      · rintro c ⟨rawKey, hrk⟩
        rw [hRk0] at hrk
        exact hch0_rc c xRk.epoch xRk.index rawKey hrk
    · cases hinner : pre_pb.inner with
      | none => rw [hinner] at hRkV1; dsimp only at hRkV1
      | some innerVal =>
        cases innerVal with
        | v1 pb0 =>
          rw [hinner] at hRkV1; dsimp only at hRkV1
          cases hfrom0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb0 with
          | error _ => rw [hfrom0] at hRkV1; dsimp only at hRkV1
          | ok st0 =>
            rw [hfrom0] at hRkV1; dsimp only at hRkV1
            cases hrecv0 : States.recv K st0 sckaMsg with
            | error _ => rw [hrecv0] at hRkV1; dsimp only at hRkV1
            | ok v0 =>
              rw [hrecv0] at hRkV1; dsimp only at hRkV1
              obtain ⟨_, ch1, hch1_eq, hch1_links, hch1_small, hch1_cp, hch1_rc⟩ :=
                hv1Post pb0 st0 sckaMsg v0 hinner hfrom0 hrecv0
              have hAfterEq : v1ChainAfterKey (spqrHkdfWith F) ch0 v0.key = .ok ch1 := hch1_eq
              rw [hAfterEq] at hRkV1
              have hRkCh1 : xRk.self = ch1 := (Except.ok.inj hRkV1).symm
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [hRkCh1]; exact Nat.le_trans hch1_links (by decide)
              · rw [hRkCh1]; exact hch1_small
              · rw [hRkCh1]; exact hch1_cp
              · rintro c ⟨rawKey, hrk⟩
                rw [hRkCh1] at hrk
                exact hch1_rc c xRk.epoch xRk.index rawKey hrk
  exact ⟨hvn, hcLinks4, hv1PreRaw, hAddLinks4, hRkLinks4, hRkSmall, hRkCp, hRkRc, hv1PostRaw⟩

theorem spqrRecvTightDomain_of_topStateTight_and_tightLinkedEnv
    {F : ShaCompress} {K : MlKem}
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {stBytes : Bytes}
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (hTop : TopStateTight F K stBytes)
    (hevs : SpqrRecvTightLinkedEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      StatesRecvEnv' stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvTightDomain F K stBytes xAdd xRk :=
  spqrRecvTightDomain_of_topStateTight_and_link hTop hevs.2

theorem spqrRecvTightDomain_of_topStateTight_and_linkedEnv
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {stBytes : Bytes}
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (hTop : TopStateTight F K stBytes)
    (hevs : SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvTightDomain F K stBytes xAdd xRk :=
  spqrRecvTightDomain_of_topStateTight_and_link hTop hevs.2

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
