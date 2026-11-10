/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# Peak Live-Heap Specification for SPQR `spqr::recv`

`PhaseCreditSpec M` and affine `fineCredit M` bounds for `spqr::recv` (`Block 329`) in binary call
order across decode, version dispatch (`Ordering::Less`, `Ordering::Greater`, `Ordering::Equal`),
symmetric-chain advance, and protobuf state re-encoding.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainEpoch ChainEpochPB Epoch EpochSecret Message MlKem PqRatchetState States
   V1Recv V1State VersionNegotiationPB chainFrom spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize
  (chainFrom_raw_le optRaw rawChain rawChainEpoch rawEpochDir rawPqInner rawPqState rawVN
   rawV1State spqrDecodeState_rawPqState_le)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (ChainAddEpochEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (ChainNewEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (ChainRecvKeyEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget (SpqrRecvEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrLowInterceptHyps initInner_phaseCreditSpec pqRatchetStateEncodeToVec_raw_phaseCreditSpec
   spqrBoundedEvs_phaseCreditSpec statesIntoPb_raw_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
  (chainFrom_phaseCreditSpec chainIntoPb_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
  (chainAddEpoch_phaseCreditSpec chainNew_phaseCreditSpec chainRecvKey_phaseCreditSpec
   nextKeyInternalReq recvKeyCapMax recvKey_raw_le_of_maxOoo vecDequeGrowMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw (states_recv_raw_le_2976)

/-! ## Abstract `PhaseCreditSpec` Combinators -/

private theorem nat_max_le_max {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨le_trans h1 (Nat.le_max_left c d), le_trans h2 (Nat.le_max_right c d)⟩

private theorem phaseCreditSpec_of_false {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} (c l p r : Nat) (hf : ∀ evs, ¬ Env evs) :
    PhaseCreditSpec M Env c l p r :=
  (PhaseCreditSpec.of_eq_nil (M := M) fun evs h => False.elim (hf evs h)).mono
    (Nat.zero_le c) (Nat.zero_le l) (Nat.zero_le p) (Nat.zero_le r)

private theorem phaseCreditSpec_or_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (fun evs => FreeOnlyEvs evs ∨ E evs) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).or h).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem phaseCreditSpec_seq_freeOnly_left {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv FreeOnlyEvs E) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).seq h).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem phaseCreditSpec_seq_freeOnly_right {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l r : Nat}
    (h : PhaseCreditSpec M E c l l r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l l r :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem phaseCreditSpec_seq_flat {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ l₁ r₁) (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) (l₁ + l₂) (l₁ + p₂) (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

private theorem phaseCreditSpec_seq_add_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hlp : l₁ ≤ p₁)
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁) (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) (l₁ + l₂) (p₁ + p₂) (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

private theorem phaseCreditSpec_seq_sum_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁) (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) (l₁ + l₂) (l₁ + p₁ + p₂) (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

/-! ## Structural `rawPqState`, `rawChain`, and `rawV1State` Bounds -/

theorem chain_links_mul_200_le_rawChain (c : Chain) :
    200 * c.links.length ≤ rawChain c.intoPb := by
  have hsum : ∀ (ls : List ChainEpoch),
      200 * ls.length ≤
        ((ls.map fun link =>
          ({ send := some link.send.intoPb, recv := some link.recv.intoPb } : ChainEpochPB)).map
          (fun e => rawChainEpoch e + 200)).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons l tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have h := hsum c.links
  unfold Chain.intoPb rawChain
  dsimp only
  omega

theorem chain_links_mul_112_le_rawChain (c : Chain) :
    c.links.length * 112 ≤ rawChain c.intoPb := by
  have h := chain_links_mul_200_le_rawChain c
  omega

theorem chain_links_len_le_rawChain (c : Chain) :
    c.links.length ≤ rawChain c.intoPb := by
  have h := chain_links_mul_200_le_rawChain c
  omega

theorem prev_data_len_le_rawChain (c : Chain) :
    ∀ link ∈ c.links, link.recv.prev.data.length ≤ rawChain c.intoPb := by
  have hmem : ∀ (ls : List ChainEpoch) (link : ChainEpoch),
      link ∈ ls →
      link.recv.prev.data.length ≤
        ((ls.map fun l =>
          ({ send := some l.send.intoPb, recv := some l.recv.intoPb } : ChainEpochPB)).map
          (fun e => rawChainEpoch e + 200)).sum := by
    intro ls link hm
    induction ls with
    | nil => nomatch hm
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with rfl | htl
      · simp only [rawChainEpoch, optRaw, CryptoVerification.LibsignalSpqrV1.ChainEpochDirection.intoPb,
          rawEpochDir]
        omega
      · have h := ih htl
        omega
  intro link hm
  have h := hmem c.links link hm
  unfold Chain.intoPb rawChain
  dsimp only
  omega

theorem vn_authKey_len_le_rawPqState {pre_pb : PqRatchetState} {vn : VersionNegotiationPB}
    (hvn : pre_pb.versionNegotiation = some vn) :
    vn.authKey.length ≤ rawPqState pre_pb := by
  unfold rawPqState
  rw [hvn]
  simp only [optRaw, rawVN]
  omega

theorem optRaw_chain_le_rawPqState (pre_pb : PqRatchetState) :
    optRaw rawChain pre_pb.chain ≤ rawPqState pre_pb := by
  unfold rawPqState
  omega

theorem rawV1State_le_rawPqState {pre_pb : PqRatchetState} {pb : V1State}
    (hinner : pre_pb.inner = some (.v1 pb)) :
    rawV1State pb ≤ rawPqState pre_pb := by
  unfold rawPqState
  rw [hinner]
  simp only [optRaw, rawPqInner]
  omega

/-! ## `DecodeStateBoundedEnv` and `StatesFromPbBoundedEnv` Specs -/

export LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateBoundedEnv decodeStateDeltaCum decodeStateDeltaLive decodeStateDeltaPeak)
export LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (decodeStateMaxReq decodeState_phaseCreditSpec StatesFromPbBoundedEnv statesFromPbDeltaCum)
export LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (statesFromPbDeltaLive statesFromPbDeltaPeak statesFromPbMaxReq statesFromPb_phaseCreditSpec)

/-! ## `Ordering::Less` Branch (`InitInnerTail`) -/

/-- `Ordering::Less` branch envelope for call ghosts `(xInit, xInto)` tied to `vn.authKey` and `chainFrom`.
-/
def SpqrRecvLessCallEnv (F : ShaCompress) (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
    (xInit : InitInnerGhost) (xInto : ChainIntoPbCall) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (InitInnerEnv F xInit)
      (SeqEnv (ChainFromEnv pre_pb.chain (some vn))
        (fun evsTail =>
          FreeOnlyEvs evsTail ∨
            (chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain ∧
              SeqEnv (ChainIntoPbEnv xInto) FreeOnlyEvs evsTail))) evs

def lessDeltaCum (rawPre : Nat) : Nat :=
  96 * (2 * (2 * rawPre + 2048) + 9539) + 58610 + (2 * (rawPre + 296) + 9539)

def lessDeltaLive (rawPre : Nat) : Nat :=
  96 * ((2 * rawPre + 2048) + 8195) + 49858 + ((rawPre + 296) + 8195)

def lessMaxReq (rawPre : Nat) : Nat :=
  2 * rawPre + 2048

theorem spqrRecvOrderingLess_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB}
    {xInit : InitInnerGhost} {xInto : ChainIntoPbCall} {rawPre : Nat}
    (hraw : rawPqState pre_pb ≤ rawPre)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hauth : xInit.authKey = vn.authKey) :
    PhaseCreditSpec M (SpqrRecvLessCallEnv F pre_pb vn xInit xInto)
      (lessDeltaCum rawPre) (lessDeltaLive rawPre) (lessDeltaLive rawPre) (lessMaxReq rawPre) := by
  have hauth_le : xInit.authKey.length ≤ rawPre := by
    rw [hauth]
    exact le_trans (vn_authKey_len_le_rawPqState hvn) hraw
  have hInit := (initInner_phaseCreditSpec hM F xInit).mono
    (c₂ := 96 * (2 * (2 * rawPre + 2048) + 9539))
    (l₂ := 96 * ((2 * rawPre + 2048) + 8195))
    (p₂ := 96 * ((2 * rawPre + 2048) + 8195))
    (r₂ := 2 * rawPre + 2048)
    (by omega) (by omega) (by omega) (by omega)
  have hCf := chainFrom_phaseCreditSpec hM pre_pb.chain (some vn)
  have hTailOk : PhaseCreditSpec M
      (fun evsTail =>
        chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain ∧
          SeqEnv (ChainIntoPbEnv xInto) FreeOnlyEvs evsTail)
      (2 * (rawPre + 296) + 9539) ((rawPre + 296) + 8195) ((rawPre + 296) + 8195) (rawPre + 296) := by
    by_cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain
    · have hch_raw := chainFrom_raw_le (spqrHkdfWith F) pre_pb.chain (some vn) hcf
      have hopt_le := optRaw_chain_le_rawPqState pre_pb
      have hlinks_le : xInto.chain.links.length * 112 ≤ rawPre + 296 := by
        have h112 := chain_links_mul_112_le_rawChain xInto.chain
        omega
      have hInto := (phaseCreditSpec_seq_freeOnly_right hM
        (chainIntoPb_phaseCreditSpec hM xInto)).mono
        (c₂ := 2 * (rawPre + 296) + 9539)
        (l₂ := (rawPre + 296) + 8195)
        (p₂ := (rawPre + 296) + 8195)
        (r₂ := rawPre + 296)
        (by omega) (by omega) (by omega) hlinks_le
      exact hInto.of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hcf
  have hTail := phaseCreditSpec_or_freeOnly hM hTailOk
  have hActive := phaseCreditSpec_seq_flat hInit (phaseCreditSpec_seq_flat hCf hTail)
  have hOr := phaseCreditSpec_or_freeOnly hM hActive
  unfold SpqrRecvLessCallEnv lessDeltaCum lessDeltaLive lessMaxReq
  exact hOr.mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by omega)

/-! ## `Ordering::Greater` Branch (`V0ChainTail`) -/

/-- Chain initialization envelope in `Ordering::Greater` (`ChainNewEnv`, `ChainFromEnv`, or `FreeOnlyEvs`).
-/
def V0ChainInitEnv (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (_xNew : ChainNewGhost)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ ChainNewEnv evs ∨ ChainFromEnv pre_pb.chain (some vn) evs

/-- `Ordering::Greater` branch envelope for call ghosts `(xNew, xRk, xInto)`. -/
def SpqrRecvGreaterCallEnv (F : ShaCompress)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (xNew : ChainNewGhost) (xRk : ChainRecvKeyGhost) (xInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    (rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      SeqEnv (V0ChainInitEnv pre_pb vn xNew)
        (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
          (fun evsTail =>
            FreeOnlyEvs evsTail ∨
              ((∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
                  .ok (xInto.chain, rawKey)) ∧
                SeqEnv (ChainIntoPbEnv xInto)
                  (SeqEnv
                    (PqRatchetStateEncodeToVecEnv
                      { versionNegotiation := some vn
                        chain := some xInto.chain.intoPb
                        inner := some (.v1 pb) })
                    FreeOnlyEvs) evsTail))) evs)

def greaterRecvKeyCum (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxJumpCap maxOooCap d : Nat) : Nat :=
  (maxJumpCap + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
    HasFineReallocCredit.smallAllocCost M 32 +
    d * (2 * recvKeyCapMax (rawPre + 296) maxOooCap + 9539)

def greaterRecvKeyLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  if HasFineReallocCredit.smallMaxReq M < recvKeyCapMax (rawPre + 296) maxOooCap then
    recvKeyCapMax (rawPre + 296) maxOooCap + 8195
  else 0

def greaterIntoBound (rawPre maxOooCap : Nat) : Nat :=
  rawPre + 328 + 36 * maxOooCap

def greaterEncodeBound (rawPre maxOooCap : Nat) : Nat :=
  greaterIntoBound rawPre maxOooCap + 752

def greaterDeltaCum (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxJumpCap maxOooCap d : Nat) : Nat :=
  58610 + greaterRecvKeyCum M rawPre maxJumpCap maxOooCap d +
    (2 * greaterIntoBound rawPre maxOooCap + 9539) +
    (2 * greaterEncodeBound rawPre maxOooCap + 9539)

def greaterDeltaLive (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  49858 + greaterRecvKeyLarge M rawPre maxOooCap +
    (greaterIntoBound rawPre maxOooCap + 8195) +
    (greaterEncodeBound rawPre maxOooCap + 8195)

def greaterDeltaPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  49858 + 2 * greaterRecvKeyLarge M rawPre maxOooCap +
    (greaterIntoBound rawPre maxOooCap + 8195) +
    (greaterEncodeBound rawPre maxOooCap + 8195)

def greaterMaxReq (rawPre maxOooCap : Nat) : Nat :=
  max 448 (max (recvKeyCapMax (rawPre + 296) maxOooCap) (greaterEncodeBound rawPre maxOooCap))

theorem spqrRecvOrderingGreater_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmall448 : 448 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {xNew : ChainNewGhost} {xRk : ChainRecvKeyGhost} {xInto : ChainIntoPbCall}
    {rawPre maxJumpCap maxOooCap d : Nat}
    (hraw : rawPqState pre_pb ≤ rawPre)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (rawPre + 296) + 36 * maxOooCap < 2 ^ d) :
    PhaseCreditSpec M (SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xInto)
      (greaterDeltaCum M rawPre maxJumpCap maxOooCap d)
      (greaterDeltaLive M rawPre maxOooCap)
      (greaterDeltaPeak M rawPre maxOooCap)
      (greaterMaxReq rawPre maxOooCap) := by
  have hInit : PhaseCreditSpec M (V0ChainInitEnv pre_pb vn xNew) 58610 49858 49858 448 := by
    have hn : PhaseCreditSpec M ChainNewEnv 58610 0 0 448 :=
      chainNew_phaseCreditSpec hM hSmall448
    have hcf := chainFrom_phaseCreditSpec hM pre_pb.chain (some vn)
    unfold V0ChainInitEnv
    exact phaseCreditSpec_or_freeOnly hM
      ((hn.or hcf).mono (c₂ := 58610) (l₂ := 49858) (p₂ := 49858) (r₂ := 448)
        (by decide) (by decide) (by decide) (by decide))
  have hReqLe72 : max 32 nextKeyInternalReq ≤ 72 := by decide
  have hSmallRk : max 32 nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans hReqLe72 (le_trans (by decide : 72 ≤ 448) hSmall448)
  set bInto := greaterIntoBound rawPre maxOooCap
  set rEnc := greaterEncodeBound rawPre maxOooCap
  by_cases hrc0 : rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296
  · have hopt_le := optRaw_chain_le_rawPqState pre_pb
    have hrc0' : rawChain xRk.self.intoPb ≤ rawPre + 296 := by omega
    have hPrev : ∀ link ∈ xRk.self.links, link.recv.prev.data.length ≤ rawPre + 296 :=
      fun link hm => le_trans (prev_data_len_le_rawChain xRk.self link hm) hrc0'
    have hRk : PhaseCreditSpec M (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
        (greaterRecvKeyCum M rawPre maxJumpCap maxOooCap d)
        (greaterRecvKeyLarge M rawPre maxOooCap)
        (2 * greaterRecvKeyLarge M rawPre maxOooCap)
        (max (max 32 nextKeyInternalReq) (recvKeyCapMax (rawPre + 296) maxOooCap)) :=
      chainRecvKey_phaseCreditSpec hM hSmallRk (spqrHkdfWith F) xRk hJump hOoo hPrev hd
    have hTailOk : PhaseCreditSpec M
        (fun evsTail =>
          (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
              .ok (xInto.chain, rawKey)) ∧
            SeqEnv (ChainIntoPbEnv xInto)
              (SeqEnv
                (PqRatchetStateEncodeToVecEnv
                  { versionNegotiation := some vn
                    chain := some xInto.chain.intoPb
                    inner := some (.v1 pb) })
                FreeOnlyEvs) evsTail)
        ((2 * bInto + 9539) + (2 * rEnc + 9539))
        ((bInto + 8195) + (rEnc + 8195))
        ((bInto + 8195) + (rEnc + 8195))
        (max bInto rEnc) := by
      by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
          .ok (xInto.chain, rawKey)
      · obtain ⟨rawKey, hrk⟩ := hrk_ok
        have hrc1 := recvKey_raw_le_of_maxOoo (spqrHkdfWith F) xRk.self xRk.epoch xRk.index hOoo hrk
        have hlinks_le : xInto.chain.links.length * 112 ≤ bInto := by
          have h112 := chain_links_mul_112_le_rawChain xInto.chain
          dsimp only [bInto]; unfold greaterIntoBound; omega
        have hpre_eq : rawPqState pre_pb = rawVN vn + optRaw rawChain pre_pb.chain + rawV1State pb := by
          unfold rawPqState; rw [hvn, hinner]; rfl
        set stOut : PqRatchetState :=
          { versionNegotiation := some vn, chain := some xInto.chain.intoPb, inner := some (.v1 pb) }
        have hraw_out : rawPqState stOut + 752 ≤ rEnc := by
          have hst_eq : rawPqState stOut = rawVN vn + rawChain xInto.chain.intoPb + rawV1State pb := rfl
          dsimp only [rEnc]; unfold greaterEncodeBound greaterIntoBound; omega
        have hInto := (chainIntoPb_phaseCreditSpec hM xInto).mono
          (c₂ := 2 * bInto + 9539) (l₂ := bInto + 8195) (p₂ := bInto + 8195) (r₂ := bInto)
          (by omega) (by omega) (by omega) hlinks_le
        have hEnc := (phaseCreditSpec_seq_freeOnly_right hM
          (pqRatchetStateEncodeToVec_raw_phaseCreditSpec hM stOut)).mono
          (c₂ := 2 * rEnc + 9539) (l₂ := rEnc + 8195) (p₂ := rEnc + 8195) (r₂ := rEnc)
          (by omega) (by omega) (by omega) hraw_out
        exact (phaseCreditSpec_seq_flat hInto hEnc).of_imp fun _ h => h.2
      · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hrk_ok
    have hTail := phaseCreditSpec_or_freeOnly hM hTailOk
    have hRkTail := phaseCreditSpec_seq_add_peak (Nat.le_mul_of_pos_left _ (by decide)) hRk hTail
    have hSeq := (phaseCreditSpec_seq_flat hInit hRkTail).of_imp
      (E₁ := fun evs => rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        SeqEnv (V0ChainInitEnv pre_pb vn xNew)
          (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk) _) evs)
      fun _ h => h.2
    have hOr := phaseCreditSpec_or_freeOnly hM hSeq
    have hb_le_r : bInto ≤ rEnc := by dsimp only [bInto, rEnc]; unfold greaterEncodeBound; omega
    have h72_le_cap : 72 ≤ recvKeyCapMax (rawPre + 296) maxOooCap := by
      unfold recvKeyCapMax; omega
    unfold SpqrRecvGreaterCallEnv greaterDeltaCum greaterDeltaLive greaterDeltaPeak greaterMaxReq
    exact hOr.mono
      (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
      (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
      (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
      (nat_max_le_max (Nat.le_refl 448)
        (nat_max_le_max (Nat.max_le.mpr ⟨le_trans hReqLe72 h72_le_cap, Nat.le_refl _⟩)
          (Nat.max_le.mpr ⟨hb_le_r, Nat.le_refl _⟩)))
  · exact phaseCreditSpec_or_freeOnly hM
      (phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hrc0)

/-! ## `Ordering::Equal` Branch (`V1RatchetTail`) -/

/-- Affine `PhaseCreditSpec` hypothesis bundle for `<States>::recv`, guarded by `StatesDecPtsNeededBound st0`.
-/
structure StatesRecvCreditSpec (M : AllocCostModel) [HasFineReallocCredit M] (F : ShaCompress)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop) where
  kCum : Nat
  cCum : Nat
  kLive : Nat
  cLive : Nat
  kPeak : Nat
  cPeak : Nat
  kReq : Nat
  cReq : Nat
  spec_of_pts :
    ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      StatesDecPtsNeededBound st0 →
      PhaseCreditSpec M (StatesRecvEnv st0 msg)
        (kCum * rawV1State st0.into_pb + cCum)
        (kLive * rawV1State st0.into_pb + cLive)
        (kPeak * rawV1State st0.into_pb + cPeak)
        (kReq * rawV1State st0.into_pb + cReq)

/-- Optional `<Chain>::add_epoch` envelope (`evs = []` when `esOpt = none`, `ChainAddEpochEnv` when `some`).
-/
def OptChainAddEpochEnv (F : ShaCompress) (esOpt : Option EpochSecret) (xAdd : ChainAddEpochGhost)
    (evs : List AllocEvent) : Prop :=
  match esOpt with
  | none => evs = []
  | some _ => ChainAddEpochEnv (spqrHkdfWith F) xAdd evs

/-- Symmetric-chain and protobuf re-encoding tail (`+1856 .. +2820`) of the `Ordering::Equal` branch.
-/
def V1ChainAndEncodeEnv (F : ShaCompress)
    (pre_pb : PqRatchetState) (esOpt : Option EpochSecret)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (ChainFromEnv pre_pb.chain pre_pb.versionNegotiation)
    (fun evs1 =>
      FreeOnlyEvs evs1 ∨
        (rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
          rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
          SeqEnv (OptChainAddEpochEnv F esOpt xAdd)
            (fun evs2 =>
              FreeOnlyEvs evs2 ∨
                SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
                  (fun evs3 =>
                    FreeOnlyEvs evs3 ∨
                      ((∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
                          .ok (xCInto.chain, rawKey)) ∧
                        SeqEnv (StatesIntoPbEnv xSInto)
                          (SeqEnv (ChainIntoPbEnv xCInto)
                            (SeqEnv
                              (PqRatchetStateEncodeToVecEnv
                                { versionNegotiation := none
                                  chain := some xCInto.chain.intoPb
                                  inner := some (.v1 xSInto.st.into_pb) })
                              FreeOnlyEvs)) evs3)) evs2) evs1)) evs

/-- `Ordering::Equal` (`V1RatchetTail`, `+1532 .. +2820`) allocator trace envelope. -/
def SpqrRecvEqualCallEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SeqEnv FreeOnlyEvs
    (fun evsAfterMd =>
      FreeOnlyEvs evsAfterMd ∨
        SeqEnv (StatesFromPbBoundedEnv pb)
          (fun evsAfterFrom =>
            FreeOnlyEvs evsAfterFrom ∨
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
                SeqEnv (StatesRecvEnv st0 sckaMsg)
                  (fun evsAfterRecv =>
                    FreeOnlyEvs evsAfterRecv ∨
                      (States.recv K st0 sckaMsg = .ok v ∧
                        xSInto.st = v.state ∧
                        V1ChainAndEncodeEnv F pre_pb v.key
                          xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)) evsAfterMd) evs

def equalAddEpochReq (rawPre : Nat) : Nat :=
  vecDequeGrowMaxReq (rawPre + 296)

def equalRecvKeyCum (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxJumpCap maxOooCap d : Nat) : Nat :=
  (maxJumpCap + 1) * HasFineReallocCredit.smallAllocCost M nextKeyInternalReq +
    HasFineReallocCredit.smallAllocCost M 32 +
    d * (2 * recvKeyCapMax (rawPre + 1058) maxOooCap + 9539)

def equalRecvKeyLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  if HasFineReallocCredit.smallMaxReq M < recvKeyCapMax (rawPre + 1058) maxOooCap then
    recvKeyCapMax (rawPre + 1058) maxOooCap + 8195
  else 0

def equalSIntoReq (rawPre : Nat) : Nat :=
  2 * (rawPre + 2976) + 1824

def equalCIntoBound (rawPre maxOooCap : Nat) : Nat :=
  rawPre + 1090 + 36 * maxOooCap

def equalEncodeBound (rawPre maxOooCap : Nat) : Nat :=
  2 * rawPre + 4818 + 36 * maxOooCap

def equalChainTailCum (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxJumpCap maxOooCap d : Nat) : Nat :=
  58610 + (2 * equalAddEpochReq rawPre + 57714) +
    equalRecvKeyCum M rawPre maxJumpCap maxOooCap d +
    64 * (2 * equalSIntoReq rawPre + 9539) +
    (2 * equalCIntoBound rawPre maxOooCap + 9539) +
    (2 * equalEncodeBound rawPre maxOooCap + 9539)

def equalChainTailLive (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  49858 + (equalAddEpochReq rawPre + 8195) + equalRecvKeyLarge M rawPre maxOooCap +
    64 * (equalSIntoReq rawPre + 8195) +
    (equalCIntoBound rawPre maxOooCap + 8195) +
    (equalEncodeBound rawPre maxOooCap + 8195)

def equalChainTailPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) : Nat :=
  49858 + (equalAddEpochReq rawPre + 8195) + 2 * equalRecvKeyLarge M rawPre maxOooCap +
    64 * (equalSIntoReq rawPre + 8195) +
    (equalCIntoBound rawPre maxOooCap + 8195) +
    (equalEncodeBound rawPre maxOooCap + 8195)

def equalChainTailMaxReq (rawPre maxOooCap : Nat) : Nat :=
  max (equalAddEpochReq rawPre)
    (max (recvKeyCapMax (rawPre + 1058) maxOooCap)
      (max (equalSIntoReq rawPre) (equalEncodeBound rawPre maxOooCap)))

theorem v1ChainAndEncode_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {rawPre maxJumpCap maxOooCap d : Nat}
    (hraw : rawPqState pre_pb ≤ rawPre)
    (hSInto : rawV1State xSInto.st.into_pb ≤ rawPre + 2976)
    (hJump : xRk.self.params.maxJumpOrDefault.toNat ≤ maxJumpCap)
    (hOoo : xRk.self.params.maxOooKeysOrDefault.toNat ≤ maxOooCap)
    (hd : (rawPre + 1058) + 36 * maxOooCap < 2 ^ d) :
    PhaseCreditSpec M (V1ChainAndEncodeEnv F pre_pb esOpt xAdd xRk xSInto xCInto)
      (equalChainTailCum M rawPre maxJumpCap maxOooCap d)
      (equalChainTailLive M rawPre maxOooCap)
      (equalChainTailPeak M rawPre maxOooCap)
      (equalChainTailMaxReq rawPre maxOooCap) := by
  have hCf := chainFrom_phaseCreditSpec hM pre_pb.chain pre_pb.versionNegotiation
  have hReqLe72 : max 32 nextKeyInternalReq ≤ 72 := by decide
  have hSmallRk : max 32 nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans hReqLe72 hSmall72
  set rAdd := equalAddEpochReq rawPre
  set rSInto := equalSIntoReq rawPre
  set bCInto := equalCIntoBound rawPre maxOooCap
  set rEnc := equalEncodeBound rawPre maxOooCap
  have h448 : 448 ≤ equalChainTailMaxReq rawPre maxOooCap := by
    have : 448 ≤ equalAddEpochReq rawPre := by
      unfold equalAddEpochReq vecDequeGrowMaxReq CryptoVerification.SpqrV1.ChainProofs.chainEpochSize
      omega
    unfold equalChainTailMaxReq; omega
  have hInnerGuard : PhaseCreditSpec M
      (fun evs1 =>
        rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
          rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
          SeqEnv (OptChainAddEpochEnv F esOpt xAdd)
            (fun evs2 =>
              FreeOnlyEvs evs2 ∨
                SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
                  (fun evs3 =>
                    FreeOnlyEvs evs3 ∨
                      ((∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
                          .ok (xCInto.chain, rawKey)) ∧
                        SeqEnv (StatesIntoPbEnv xSInto)
                          (SeqEnv (ChainIntoPbEnv xCInto)
                            (SeqEnv
                              (PqRatchetStateEncodeToVecEnv
                                { versionNegotiation := none
                                  chain := some xCInto.chain.intoPb
                                  inner := some (.v1 xSInto.st.into_pb) })
                              FreeOnlyEvs)) evs3)) evs2) evs1)
      ((2 * rAdd + 57714) + equalRecvKeyCum M rawPre maxJumpCap maxOooCap d +
        64 * (2 * rSInto + 9539) + (2 * bCInto + 9539) + (2 * rEnc + 9539))
      ((rAdd + 8195) + equalRecvKeyLarge M rawPre maxOooCap +
        64 * (rSInto + 8195) + (bCInto + 8195) + (rEnc + 8195))
      ((rAdd + 8195) + 2 * equalRecvKeyLarge M rawPre maxOooCap +
        64 * (rSInto + 8195) + (bCInto + 8195) + (rEnc + 8195))
      (equalChainTailMaxReq rawPre maxOooCap) := by
    by_cases hrc : rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058
    · obtain ⟨hrcAdd, hrcRk⟩ := hrc
      have hopt_le := optRaw_chain_le_rawPqState pre_pb
      have hAddLen : xAdd.self.links.length ≤ rawPre + 296 := by
        have := chain_links_len_le_rawChain xAdd.self
        omega
      have hAdd : PhaseCreditSpec M (OptChainAddEpochEnv F esOpt xAdd)
          (2 * rAdd + 57714) (rAdd + 8195) (rAdd + 8195) rAdd := by
        unfold OptChainAddEpochEnv
        cases esOpt with
        | none =>
          exact (PhaseCreditSpec.nil M).mono
            (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | some _ =>
          exact chainAddEpoch_phaseCreditSpec hM hSmall72 (spqrHkdfWith F) xAdd hAddLen
      have hPrev : ∀ link ∈ xRk.self.links, link.recv.prev.data.length ≤ rawPre + 1058 := by
        intro link hm
        have := prev_data_len_le_rawChain xRk.self link hm
        omega
      have hRk : PhaseCreditSpec M (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
          (equalRecvKeyCum M rawPre maxJumpCap maxOooCap d)
          (equalRecvKeyLarge M rawPre maxOooCap)
          (2 * equalRecvKeyLarge M rawPre maxOooCap)
          (max (max 32 nextKeyInternalReq) (recvKeyCapMax (rawPre + 1058) maxOooCap)) :=
        chainRecvKey_phaseCreditSpec hM hSmallRk (spqrHkdfWith F) xRk hJump hOoo hPrev hd
      have hEncodeTail : PhaseCreditSpec M
          (fun evs3 =>
            (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
                .ok (xCInto.chain, rawKey)) ∧
              SeqEnv (StatesIntoPbEnv xSInto)
                (SeqEnv (ChainIntoPbEnv xCInto)
                  (SeqEnv
                    (PqRatchetStateEncodeToVecEnv
                      { versionNegotiation := none
                        chain := some xCInto.chain.intoPb
                        inner := some (.v1 xSInto.st.into_pb) })
                    FreeOnlyEvs)) evs3)
          (64 * (2 * rSInto + 9539) + (2 * bCInto + 9539) + (2 * rEnc + 9539))
          (64 * (rSInto + 8195) + (bCInto + 8195) + (rEnc + 8195))
          (64 * (rSInto + 8195) + (bCInto + 8195) + (rEnc + 8195))
          (max rSInto (max bCInto rEnc)) := by
        by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xCInto.chain, rawKey)
        · obtain ⟨rawKey, hrk⟩ := hrk_ok
          have hrc2 := recvKey_raw_le_of_maxOoo (spqrHkdfWith F) xRk.self xRk.epoch xRk.index hOoo hrk
          have hlinks_le : xCInto.chain.links.length * 112 ≤ bCInto := by
            have := chain_links_mul_112_le_rawChain xCInto.chain
            dsimp only [bCInto]; unfold equalCIntoBound; omega
          set stOut : PqRatchetState :=
            { versionNegotiation := none
              chain := some xCInto.chain.intoPb
              inner := some (.v1 xSInto.st.into_pb) }
          have hraw_out : rawPqState stOut + 752 ≤ rEnc := by
            have hst_eq : rawPqState stOut =
                0 + rawChain xCInto.chain.intoPb + rawV1State xSInto.st.into_pb := rfl
            dsimp only [rEnc]; unfold equalEncodeBound; omega
          have hS_r : 2 * rawV1State xSInto.st.into_pb + 1824 ≤ rSInto := by
            dsimp only [rSInto]; unfold equalSIntoReq; omega
          have hS := (statesIntoPb_raw_phaseCreditSpec hM xSInto).mono
            (c₂ := 64 * (2 * rSInto + 9539))
            (l₂ := 64 * (rSInto + 8195))
            (p₂ := 64 * (rSInto + 8195))
            (r₂ := rSInto)
            (by omega) (by omega) (by omega) hS_r
          have hC := (chainIntoPb_phaseCreditSpec hM xCInto).mono
            (c₂ := 2 * bCInto + 9539) (l₂ := bCInto + 8195) (p₂ := bCInto + 8195) (r₂ := bCInto)
            (by omega) (by omega) (by omega) hlinks_le
          have hE := (phaseCreditSpec_seq_freeOnly_right hM
            (pqRatchetStateEncodeToVec_raw_phaseCreditSpec hM stOut)).mono
            (c₂ := 2 * rEnc + 9539) (l₂ := rEnc + 8195) (p₂ := rEnc + 8195) (r₂ := rEnc)
            (by omega) (by omega) (by omega) hraw_out
          exact ((phaseCreditSpec_seq_flat hS (phaseCreditSpec_seq_flat hC hE)).of_imp
            fun _ h => h.2).mono
            (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
            (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
            (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
            (Nat.le_refl _)
        · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hrk_ok
      have hEvs3 := phaseCreditSpec_or_freeOnly hM hEncodeTail
      have hEvs2 := phaseCreditSpec_or_freeOnly hM
        (phaseCreditSpec_seq_add_peak (Nat.le_mul_of_pos_left _ (by decide)) hRk hEvs3)
      have hb_le_r : bCInto ≤ rEnc := by
        dsimp only [bCInto, rEnc]; unfold equalCIntoBound equalEncodeBound; omega
      have h72_le_cap : 72 ≤ recvKeyCapMax (rawPre + 1058) maxOooCap := by
        unfold recvKeyCapMax; omega
      exact ((phaseCreditSpec_seq_flat hAdd hEvs2).mono
        (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
        (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
        (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
        (by unfold equalChainTailMaxReq
            exact nat_max_le_max (Nat.le_refl rAdd)
              (nat_max_le_max (Nat.max_le.mpr ⟨le_trans hReqLe72 h72_le_cap, Nat.le_refl _⟩)
                (nat_max_le_max (Nat.le_refl rSInto)
                  (Nat.max_le.mpr ⟨hb_le_r, Nat.le_refl _⟩))))).of_imp
        fun _ h => h.2.2
    · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrc
  have hSeq := phaseCreditSpec_seq_flat hCf (phaseCreditSpec_or_freeOnly hM hInnerGuard)
  unfold V1ChainAndEncodeEnv equalChainTailCum equalChainTailLive equalChainTailPeak
  exact hSeq.mono
    (by dsimp only [rAdd, rSInto, bCInto, rEnc]; simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by dsimp only [rAdd, rSInto, bCInto, rEnc]; simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by dsimp only [rAdd, rSInto, bCInto, rEnc]; simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.max_le.mpr ⟨h448, Nat.le_refl _⟩)

def equalDeltaCum (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (rawPre maxJumpCap maxOooCap d : Nat) : Nat :=
  (77 * (4 * rawPre + 16384) + 188 * (rawPre + 64) + 9539 * 64) +
    (S.kCum * rawPre + S.cCum) +
    equalChainTailCum M rawPre maxJumpCap maxOooCap d

def equalDeltaLive (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (rawPre maxOooCap : Nat) : Nat :=
  2 * (4 * rawPre + 16384) +
    (S.kLive * rawPre + S.cLive) +
    equalChainTailLive M rawPre maxOooCap

def equalDeltaPeak (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (rawPre maxOooCap : Nat) : Nat :=
  2 * (4 * rawPre + 16384) +
    (S.kLive * rawPre + S.cLive) +
    (S.kPeak * rawPre + S.cPeak) +
    equalChainTailPeak M rawPre maxOooCap

def equalMaxReq {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (rawPre maxOooCap : Nat) : Nat :=
  max (2 * rawPre + 4096)
    (max (S.kReq * rawPre + S.cReq) (equalChainTailMaxReq rawPre maxOooCap))

theorem spqrRecvOrderingEqual_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
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
    PhaseCreditSpec M
      (SpqrRecvEqualCallEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (equalDeltaCum M S rawPre maxJumpCap maxOooCap d)
      (equalDeltaLive M S rawPre maxOooCap)
      (equalDeltaPeak M S rawPre maxOooCap)
      (equalMaxReq S rawPre maxOooCap) := by
  have hpb_le : rawV1State pb ≤ rawPre :=
    le_trans (rawV1State_le_rawPqState hinner) hraw
  have hFromPb := (statesFromPb_phaseCreditSpec hM hLow pb).mono
    (c₂ := 77 * (4 * rawPre + 16384) + 188 * (rawPre + 64) + 9539 * 64)
    (l₂ := 2 * (4 * rawPre + 16384))
    (p₂ := 2 * (4 * rawPre + 16384))
    (r₂ := 2 * rawPre + 4096)
    (by unfold statesFromPbDeltaCum; dsimp only; omega)
    (by unfold statesFromPbDeltaLive; omega)
    (by unfold statesFromPbDeltaPeak; omega)
    (by unfold statesFromPbMaxReq; omega)
  have hAfterFromOk : PhaseCreditSpec M
      (fun evsAfterFrom =>
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
          SeqEnv (StatesRecvEnv st0 sckaMsg)
            (fun evsAfterRecv =>
              FreeOnlyEvs evsAfterRecv ∨
                (States.recv K st0 sckaMsg = .ok v ∧
                  xSInto.st = v.state ∧
                  V1ChainAndEncodeEnv F pre_pb v.key
                    xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)
      ((S.kCum * rawPre + S.cCum) + equalChainTailCum M rawPre maxJumpCap maxOooCap d)
      ((S.kLive * rawPre + S.cLive) + equalChainTailLive M rawPre maxOooCap)
      ((S.kLive * rawPre + S.cLive) + (S.kPeak * rawPre + S.cPeak) +
        equalChainTailPeak M rawPre maxOooCap)
      (max (S.kReq * rawPre + S.cReq) (equalChainTailMaxReq rawPre maxOooCap)) := by
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · have hpts : StatesDecPtsNeededBound st0 := StatesDecPtsNeededBound.of_from_pb hfrom
      have hst0_raw : rawV1State st0.into_pb ≤ rawPre :=
        le_trans (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom).1 hpb_le
      have hRecv := (S.spec_of_pts st0 sckaMsg hpts).mono
        (c₂ := S.kCum * rawPre + S.cCum)
        (l₂ := S.kLive * rawPre + S.cLive)
        (p₂ := S.kPeak * rawPre + S.cPeak)
        (r₂ := S.kReq * rawPre + S.cReq)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ hst0_raw) _)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ hst0_raw) _)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ hst0_raw) _)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ hst0_raw) _)
      have hAfterRecvOk : PhaseCreditSpec M
          (fun evsAfterRecv =>
            States.recv K st0 sckaMsg = .ok v ∧
              xSInto.st = v.state ∧
              V1ChainAndEncodeEnv F pre_pb v.key xAdd xRk xSInto xCInto evsAfterRecv)
          (equalChainTailCum M rawPre maxJumpCap maxOooCap d)
          (equalChainTailLive M rawPre maxOooCap)
          (equalChainTailPeak M rawPre maxOooCap)
          (equalChainTailMaxReq rawPre maxOooCap) := by
        by_cases hrv : States.recv K st0 sckaMsg = .ok v ∧ xSInto.st = v.state
        · obtain ⟨hrecv_ok, hst_eq⟩ := hrv
          have hv_raw : rawV1State xSInto.st.into_pb ≤ rawPre + 2976 := by
            rw [hst_eq]
            have := states_recv_raw_le_2976 hpts.toStatesPtsNeededBound hrecv_ok
            omega
          exact (v1ChainAndEncode_phaseCreditSpec hM hSmall72 F hraw hv_raw hJump hOoo hd).of_imp
            fun _ h => h.2.2
        · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrv
      have hAfterRecv := phaseCreditSpec_or_freeOnly hM hAfterRecvOk
      exact (phaseCreditSpec_seq_sum_peak hRecv hAfterRecv).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hfrom
  have hAfterFrom := phaseCreditSpec_or_freeOnly hM hAfterFromOk
  have hAfterMd := phaseCreditSpec_or_freeOnly hM (phaseCreditSpec_seq_flat hFromPb hAfterFrom)
  have hFull := phaseCreditSpec_seq_freeOnly_left hM hAfterMd
  unfold SpqrRecvEqualCallEnv equalDeltaCum equalDeltaLive equalDeltaPeak equalMaxReq
  exact hFull.mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)

/-! ## Top-Level `spqr::recv` Join (`SpqrRecvPartsEnv`) -/

/-- Full `spqr::recv` allocator trace envelope on input state slice `stBytes`, composing message
preamble validation, `spqr::decode_state`, and the three version-ordering dispatch branches. -/
def SpqrRecvPartsEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (DecodeStateBoundedEnv stBytes.length)
      (fun evsAfterDec =>
        FreeOnlyEvs evsAfterDec ∨
          (spqrDecodeState stBytes = .ok pre_pb ∧
            ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
                SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
              (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
                SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
              (pre_pb.inner = some (.v1 pb) ∧
                SpqrRecvEqualCallEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v
                  xAdd xRk xSInto xCInto evsAfterDec)))) evs

def spqrRecvDeltaCum (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (stLen maxJumpCap maxOooCap d : Nat) : Nat :=
  decodeStateDeltaCum stLen +
    max (lessDeltaCum (201 * stLen))
      (max (greaterDeltaCum M (201 * stLen) maxJumpCap maxOooCap d)
        (equalDeltaCum M S (201 * stLen) maxJumpCap maxOooCap d))

def spqrRecvDeltaLive (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (stLen maxOooCap : Nat) : Nat :=
  decodeStateDeltaLive stLen +
    max (lessDeltaLive (201 * stLen))
      (max (greaterDeltaLive M (201 * stLen) maxOooCap)
        (equalDeltaLive M S (201 * stLen) maxOooCap))

def spqrRecvDeltaPeak (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (stLen maxOooCap : Nat) : Nat :=
  decodeStateDeltaLive stLen + decodeStateDeltaPeak stLen +
    max (lessDeltaLive (201 * stLen))
      (max (greaterDeltaPeak M (201 * stLen) maxOooCap)
        (equalDeltaPeak M S (201 * stLen) maxOooCap))

def spqrRecvMaxReq {M : AllocCostModel} [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
    (stLen maxOooCap : Nat) : Nat :=
  max (decodeStateMaxReq stLen)
    (max (lessMaxReq (201 * stLen))
      (max (greaterMaxReq (201 * stLen) maxOooCap)
        (equalMaxReq S (201 * stLen) maxOooCap)))

/-- `PhaseCreditSpec M` for `SpqrRecvPartsEnv`. -/
theorem spqrRecvParts_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
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
    PhaseCreditSpec M
      (SpqrRecvPartsEnv F K StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v
        xInit xNew xAdd xRk xSInto xCInto)
      (spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d)
      (spqrRecvDeltaLive M S stBytes.length maxOooCap)
      (spqrRecvDeltaPeak M S stBytes.length maxOooCap)
      (spqrRecvMaxReq S stBytes.length maxOooCap) := by
  have hSmall448 : 448 ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans (by decide : 448 ≤ 8195) hLow.hSmallMaxGe
  have hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M :=
    le_trans (by decide : 72 ≤ 448) hSmall448
  set stLen := stBytes.length
  set rawPre := 201 * stLen
  have hDec := decodeState_phaseCreditSpec hM hLow stLen
  have hAfterDecOk : PhaseCreditSpec M
      (fun evsAfterDec =>
        spqrDecodeState stBytes = .ok pre_pb ∧
          ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
              SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
            (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
            (pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvEqualCallEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v
                xAdd xRk xSInto xCInto evsAfterDec)))
      (max (lessDeltaCum rawPre)
        (max (greaterDeltaCum M rawPre maxJumpCap maxOooCap d)
          (equalDeltaCum M S rawPre maxJumpCap maxOooCap d)))
      (max (lessDeltaLive rawPre)
        (max (greaterDeltaLive M rawPre maxOooCap)
          (equalDeltaLive M S rawPre maxOooCap)))
      (max (lessDeltaLive rawPre)
        (max (greaterDeltaPeak M rawPre maxOooCap)
          (equalDeltaPeak M S rawPre maxOooCap)))
      (max (lessMaxReq rawPre)
        (max (greaterMaxReq rawPre maxOooCap)
          (equalMaxReq S rawPre maxOooCap))) := by
    by_cases hdec_ok : spqrDecodeState stBytes = .ok pre_pb
    · have hraw : rawPqState pre_pb ≤ rawPre :=
        spqrDecodeState_rawPqState_le hdec_ok
      have hd_gt : (rawPre + 296) + 36 * maxOooCap < 2 ^ d := by omega
      have hLess : PhaseCreditSpec M
          (fun ev => pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
            SpqrRecvLessCallEnv F pre_pb vn xInit xCInto ev)
          (lessDeltaCum rawPre) (lessDeltaLive rawPre) (lessDeltaLive rawPre) (lessMaxReq rawPre) := by
        by_cases hL : pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey
        · exact (spqrRecvOrderingLess_phaseCreditSpec hM F hraw hL.1 hL.2).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hL
      have hGreater : PhaseCreditSpec M
          (fun ev => pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto ev)
          (greaterDeltaCum M rawPre maxJumpCap maxOooCap d)
          (greaterDeltaLive M rawPre maxOooCap)
          (greaterDeltaPeak M rawPre maxOooCap)
          (greaterMaxReq rawPre maxOooCap) := by
        by_cases hG : pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingGreater_phaseCreditSpec hM hSmall448 F hraw hG.1 hG.2
            hJump hOoo hd_gt).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hG
      have hEqual : PhaseCreditSpec M
          (fun ev => pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvEqualCallEnv F K StatesRecvEnv pre_pb pb st0 sckaMsg v
              xAdd xRk xSInto xCInto ev)
          (equalDeltaCum M S rawPre maxJumpCap maxOooCap d)
          (equalDeltaLive M S rawPre maxOooCap)
          (equalDeltaPeak M S rawPre maxOooCap)
          (equalMaxReq S rawPre maxOooCap) := by
        by_cases hE : pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingEqual_phaseCreditSpec hM hLow hSmall72 F K S hraw hE
            hJump hOoo hd).of_imp fun _ h => h.2
        · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hE
      exact (hLess.or (hGreater.or hEqual)).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false _ _ _ _ fun _ h => absurd h.1 hdec_ok
  exact phaseCreditSpec_or_freeOnly hM
    (phaseCreditSpec_seq_sum_peak hDec (phaseCreditSpec_or_freeOnly hM hAfterDecOk))

/-- Affine fine credit `cumSmall s + max (liveLarge s) (peakLarge s)` upper-bounding `M.footprint s - baseFine`.
-/
def fineCredit (M : AllocCostModel) [HasFineReallocCredit M] (s : M.σ) : Nat :=
  HasFineReallocCredit.cumSmall s +
    max (HasFineReallocCredit.liveLarge s) (HasFineReallocCredit.peakLarge s)

theorem fineCredit_footprint_le {M : AllocCostModel} [HasFineReallocCredit M] (s : M.σ) :
    M.footprint s ≤ HasFineReallocCredit.baseFine (M := M) + fineCredit M s := by
  unfold fineCredit
  have hfp := HasFineReallocCredit.footprint_le (M := M) s
  omega

theorem fineCredit_le_of_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {Δcum Δlive Δpeak maxReq : Nat}
    (h : PhaseCreditSpec M Env Δcum Δlive Δpeak maxReq)
    (hlp : Δlive ≤ Δpeak) (s0 : M.σ) {evs : List AllocEvent} (hevs : Env evs) :
    fineCredit M (M.stepEvents evs s0) ≤ fineCredit M s0 + Δcum + Δpeak := by
  unfold fineCredit
  obtain ⟨hc, hl, hp⟩ := h.credit_le s0 hevs
  omega

private theorem greaterDeltaLive_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) :
    greaterDeltaLive M rawPre maxOooCap ≤ greaterDeltaPeak M rawPre maxOooCap :=
  Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by decide)) _) _) _

private theorem equalChainTailLive_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    (rawPre maxOooCap : Nat) :
    equalChainTailLive M rawPre maxOooCap ≤ equalChainTailPeak M rawPre maxOooCap :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by decide)) _) _) _) _

private theorem equalDeltaLive_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv) (rawPre maxOooCap : Nat) :
    equalDeltaLive M S rawPre maxOooCap ≤ equalDeltaPeak M S rawPre maxOooCap :=
  Nat.add_le_add (Nat.le_add_right _ _) (equalChainTailLive_le_peak M rawPre maxOooCap)

theorem spqrRecvDeltaLive_le_spqrRecvDeltaPeak
    (M : AllocCostModel) [HasFineReallocCredit M] {F : ShaCompress}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv) (stLen maxOooCap : Nat) :
    spqrRecvDeltaLive M S stLen maxOooCap ≤ spqrRecvDeltaPeak M S stLen maxOooCap :=
  Nat.add_le_add (Nat.le_add_right _ _)
    (nat_max_le_max (Nat.le_refl _)
      (nat_max_le_max (greaterDeltaLive_le_peak M (201 * stLen) maxOooCap)
        (equalDeltaLive_le_peak M S (201 * stLen) maxOooCap)))

theorem spqrRecvPartsEnv_nil (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvPartsEnv F K StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v
      xInit xNew xAdd xRk xSInto xCInto [] :=
  Or.inl fun _ h => nomatch h

/-- Affine `fineCredit M` bound for `SpqrRecvPartsEnv`. -/
theorem spqrRecv_fineCredit_le
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
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
    fineCredit M (M.stepEvents evs s0) ≤
      fineCredit M s0 +
        spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d +
        spqrRecvDeltaPeak M S stBytes.length maxOooCap :=
  fineCredit_le_of_phaseCreditSpec
    (spqrRecvParts_phaseCreditSpec hM hLow F K S stBytes pre_pb vn pb st0 sckaMsg v
      xInit xNew xAdd xRk xSInto xCInto hJump hOoo hd)
    (spqrRecvDeltaLive_le_spqrRecvDeltaPeak M S stBytes.length maxOooCap)
    s0 hevs

theorem spqrRecv_evalLog_footprint_le
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    (S : StatesRecvCreditSpec M F StatesRecvEnv)
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
    M.footprint (M.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := M) +
        spqrRecvDeltaCum M S stBytes.length maxJumpCap maxOooCap d +
        spqrRecvDeltaPeak M S stBytes.length maxOooCap :=
  (spqrRecvParts_phaseCreditSpec hM hLow F K S stBytes pre_pb vn pb st0 sckaMsg v
    xInit xNew xAdd xRk xSInto xCInto hJump hOoo hd).evalLog_footprint_le_of_live_le_peak
    (spqrRecvDeltaLive_le_spqrRecvDeltaPeak M S stBytes.length maxOooCap) hevs

/-- `PhaseCreditSpec M` for the coarse `SpqrBoundedEvs 512` `SpqrRecvEnv`. -/
theorem spqrRecvDefaultEnv_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (st msg : VecArg) :
    let R := 4 * st.bytes.length + 4 * msg.bytes.length + 16384
    PhaseCreditSpec M (SpqrRecvEnv st msg)
      (512 * (2 * R + 9539)) (512 * (R + 8195)) (512 * (R + 8195)) R :=
  spqrBoundedEvs_phaseCreditSpec hM 512 (4 * st.bytes.length + 4 * msg.bytes.length + 16384)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
