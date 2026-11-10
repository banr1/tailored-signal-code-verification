/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit

/-!
# Peak Live-Heap & Group Interface for `PreKeySignalMessage::try_from`

Top-level interface for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`, re-exporting:
1. All-inputs CLI `PksmGhost` envelope `PksmTryFromBoundedEnv` and black-box `PhaseCreditSpec` /
   `PhaseGroupSpec` bounds (`pksmTryFrom_phaseCredit`, `pksmTryFrom_phaseGroup`).
2. Canonical `ResponderWire.PreKeyTryFromBaseBudget` `PreKeyTryFromArgs` envelope
   `PreKeyTryFromBoundedEnv` and `PhaseCreditSpec` / `PhaseGroupSpec` bounds
   (`preKeyTryFrom_phaseCredit_of_sig`, `preKeyTryFrom_phaseCredit`, `preKeyTryFrom_phaseGroup`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec

open CryptoGames.LibsignalSessionApi (PreKeySignalMessage ProtoPreKeySignalMessage)
open CryptoVerification.E2E.Pqxdh.ResponderWire (PreKeyTryFromArgs)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto pksmParse)
open LibsignalBinary.Heap (AllocCostModel AllocEvent SeqEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
  (PreKeyLoopEnv PreKeySeg2Env PreKeySeg4Env PreKeyTryFromEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv SigTryFromBoundedEnv SigTryFromErrTailEnv
   TryCloneBytesEnv sigTryFromCapDeltaCum sigTryFromCapDeltaGrpS sigTryFromCapDeltaLive
   sigTryFromCapDeltaPeak sigTryFromCapMaxReq sigTryFromDeltaCum sigTryFromDeltaCum_le_cap
   sigTryFromDeltaGrpS sigTryFromDeltaGrpS_le_cap sigTryFromDeltaLive
   sigTryFromDeltaLive_le_cap sigTryFromDeltaPeak sigTryFromDeltaPeak_le_cap sigTryFromMaxReq
   sigTryFromMaxReq_le_cap)
open LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit
  (ProtoLoop4GroupInv ProtoLoop4StateInv ProtoLoop4StateInvTight)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
  (PksmAfterKyberOkEnv PksmKyberErrAllocEnv PksmLoopTailBoundedEnv PksmPostBoundedEnv
   PksmPostSeg4Env PksmTryFromLoopBoundedEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers (ProtoCaps4)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireLowInterceptHyps fineCostModel_wireLowInterceptHyps wireGrowsFrom wireRemGrows
   wireRemGrows_mono)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

export LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireLowInterceptHyps fineCostModel_wireLowInterceptHyps wireGrowsFrom wireRemGrows
   wireRemGrows_mono)

abbrev WireGroupHyps (M : AllocCostModel) [HasFineGroupCredit M] : Prop :=
  LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers.WireGroupHyps M

theorem fineCostModel_wireGroupHyps :
    WireGroupHyps LibsignalBinary.Heap.Fine.fineCostModel :=
  LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers.fineCostModel_wireGroupHyps

/-! ## Deterministic `decodeProto` / `pksmParse` Field Extractors & Length Bounds -/

abbrev pksmDecodedInnerBytes : List (BitVec 8) → List (BitVec 8) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmDecodedInnerBytes

abbrev pksmDecodedKyberOpt : List (BitVec 8) → Option (List (BitVec 8)) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmDecodedKyberOpt

abbrev pksmInnerGhost (x : PksmGhost) : TryFromGhost :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmInnerGhost x

theorem decodeProto_fields_le {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    (h : decodeProto body = some m) :
    (∀ v, m.baseKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.identityKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.message = some v → v.length ≤ body.length) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ body.length) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.decodeProto_fields_le h

theorem pksmDecodedInnerBytes_length_le (bs : List (BitVec 8)) :
    (pksmDecodedInnerBytes bs).length ≤ bs.length :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmDecodedInnerBytes_length_le bs

theorem pksmDecodedKyberOpt_length_le (bs : List (BitVec 8)) :
    ∀ kp, pksmDecodedKyberOpt bs = some kp → kp.length ≤ bs.length :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmDecodedKyberOpt_length_le bs

theorem pksmParse_inner_eq_decoded {bs : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse bs = some pm) :
    pm.message.serialized = pksmDecodedInnerBytes bs :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmParse_inner_eq_decoded h

theorem pksmParse_kyber_eq_decoded {bs : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse bs = some pm) :
    pm.kyberPayload.map (·.ciphertext) = pksmDecodedKyberOpt bs :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmParse_kyber_eq_decoded h

/-! ## All-Inputs CLI `PksmTryFromBoundedEnv` & Black-Box `PhaseCreditSpec` (`PksmGhost`) -/

abbrev PksmTryFromBoundedEnv (x : PksmGhost) (evs : List AllocEvent) : Prop :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.PksmTryFromBoundedEnv x evs

abbrev pksmTryFromDeltaCum (x : PksmGhost) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaCum x

abbrev pksmTryFromDeltaLive (x : PksmGhost) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaLive x

abbrev pksmTryFromDeltaPeak (x : PksmGhost) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaPeak x

abbrev pksmTryFromMaxReq (x : PksmGhost) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromMaxReq x

abbrev pksmTryFromCapDeltaCum (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaCum N

abbrev pksmTryFromCapDeltaLive (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaLive N

abbrev pksmTryFromCapDeltaPeak (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaPeak N

abbrev pksmTryFromCapMaxReq (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapMaxReq N

theorem pksmTryFromDeltaCum_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaCum x ≤ pksmTryFromCapDeltaCum N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaCum_le_cap h

theorem pksmTryFromDeltaLive_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaLive x ≤ pksmTryFromCapDeltaLive N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaLive_le_cap h

theorem pksmTryFromDeltaPeak_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaPeak x ≤ pksmTryFromCapDeltaPeak N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaPeak_le_cap h

theorem pksmTryFromMaxReq_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromMaxReq x ≤ pksmTryFromCapMaxReq N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromMaxReq_le_cap h

theorem phaseCreditSpec_intoBoxedBounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {bs : List (BitVec 8)} (hLen : bs.length ≤ N) :
    PhaseCreditSpec M (IntoBoxedBoundedEnv bs) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_intoBoxedBounded hM hLen

theorem phaseCreditSpec_intoBoxedOptBounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {opt : Option (List (BitVec 8))}
    (hLen : ∀ bs, opt = some bs → bs.length ≤ N) :
    PhaseCreditSpec M (IntoBoxedOptBoundedEnv opt) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_intoBoxedOptBounded hM hLen

theorem phaseCreditSpec_tryCloneBytes {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {bs : List (BitVec 8)} (hLen : bs.length ≤ N) :
    PhaseCreditSpec M (TryCloneBytesEnv bs) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_tryCloneBytes hM hLen

theorem phaseCreditSpec_sigTryFromErrTail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M SigTryFromErrTailEnv 19478 16590 16590 128 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_sigTryFromErrTail hM

theorem phaseCreditSpec_pksmLoopTail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M PksmLoopTailBoundedEnv 29273 24913 24913 128 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_pksmLoopTail hM

theorem phaseCreditSpec_pksmKyberErrAlloc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M PksmKyberErrAllocEnv 9675 8263 8263 68 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_pksmKyberErrAlloc hM

theorem phaseCreditSpec_pksmPost_blackbox {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (hKyberLen : ∀ kp, kyberOpt = some kp → kp.length ≤ bs.length) :
    PhaseCreditSpec M (PksmPostBoundedEnv bs kyberOpt innerG)
      (4 * min bs.length 135167 + 19078 + sigTryFromDeltaCum innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG + sigTryFromDeltaPeak innerG)
      (max 68 (max bs.length (sigTryFromMaxReq innerG))) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_pksmPost_blackbox
    hM hLow bs kyberOpt innerG hKyberLen

theorem phaseCreditSpec_pksmFull_blackbox {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PksmGhost)
    (LoopEnv : List AllocEvent → Prop)
    (hLoop : ∀ evs, LoopEnv evs →
      ProtoLoop4StateInvTight M 29273 0 0 128 x.bytes.length ProtoCaps4.zero evs)
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (hKyberLen : ∀ kp, kyberOpt = some kp → kp.length ≤ x.bytes.length)
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨ SeqEnv LoopEnv (PksmPostBoundedEnv x.bytes kyberOpt innerG) evs) :
    let N := x.bytes.length
    PhaseCreditSpec M Env
      (94 * N + 16 * min (max 8 (2 * N)) 135167 + 38156 * wireRemGrows N 0 +
        4 * min N 135167 + 48351 + sigTryFromDeltaCum innerG)
      (4 * N + 49170 + sigTryFromDeltaLive innerG)
      (4 * N + 49170 + sigTryFromDeltaLive innerG + sigTryFromDeltaPeak innerG)
      (max (max 128 (2 * N)) (sigTryFromMaxReq innerG)) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_pksmFull_blackbox
    hM hLow x LoopEnv hLoop kyberOpt innerG hKyberLen Env hEnv

theorem pksmTryFrom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PksmGhost) :
    PhaseCreditSpec M (PksmTryFromBoundedEnv x)
      (pksmTryFromDeltaCum x)
      (pksmTryFromDeltaLive x)
      (pksmTryFromDeltaPeak x)
      (pksmTryFromMaxReq x) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFrom_phaseCredit hM hLow x

/-! ## Canonical `ResponderWire` `PreKeyTryFromBoundedEnv` & `PhaseCreditSpec` (`PreKeyTryFromArgs`) -/

abbrev PreKeyTryFromBoundedEnv (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  PreKeyTryFromEnv (fun bs => SigTryFromBoundedEnv ⟨0#64, bs, 0#64⟩) x

def preKeyTryFromCapDeltaCum (M_cap B_cap : Nat) : Nat :=
  2 * min M_cap 135167 + 2 * min (max 8 (2 * M_cap)) 135167 +
    2 * min B_cap 135167 + 108386 + sigTryFromCapDeltaCum M_cap

def preKeyTryFromCapDeltaLive (M_cap B_cap : Nat) : Nat :=
  2 * M_cap + B_cap + 16390 + sigTryFromCapDeltaLive M_cap

def preKeyTryFromCapDeltaPeak (M_cap B_cap : Nat) : Nat :=
  3 * M_cap + B_cap + 16390 + sigTryFromCapDeltaLive M_cap + sigTryFromCapDeltaPeak M_cap

def preKeyTryFromCapMaxReq (M_cap B_cap : Nat) : Nat :=
  max (max 3138 (max (2 * M_cap) B_cap)) (sigTryFromCapMaxReq M_cap)

def preKeyTryFromDeltaCum (x : PreKeyTryFromArgs) : Nat :=
  2 * min x.inner.length 135167 + 2 * min (max 8 (2 * x.inner.length)) 135167 +
    2 * min x.bytes.length 135167 + 108386 + sigTryFromDeltaCum ⟨0#64, x.inner, 0#64⟩

def preKeyTryFromDeltaLive (x : PreKeyTryFromArgs) : Nat :=
  2 * x.inner.length + x.bytes.length + 16390 + sigTryFromDeltaLive ⟨0#64, x.inner, 0#64⟩

def preKeyTryFromDeltaPeak (x : PreKeyTryFromArgs) : Nat :=
  3 * x.inner.length + x.bytes.length + 16390 +
    sigTryFromDeltaLive ⟨0#64, x.inner, 0#64⟩ + sigTryFromDeltaPeak ⟨0#64, x.inner, 0#64⟩

def preKeyTryFromMaxReq (x : PreKeyTryFromArgs) : Nat :=
  max (max 3138 (max (2 * x.inner.length) x.bytes.length)) (sigTryFromMaxReq ⟨0#64, x.inner, 0#64⟩)

private theorem min_right_mono {a b S : Nat} (h : a ≤ b) : min a S ≤ min b S := by
  omega

private theorem max8_two_mul_mono {a b : Nat} (h : a ≤ b) : max 8 (2 * a) ≤ max 8 (2 * b) := by
  omega

theorem preKeyTryFromDeltaCum_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromDeltaCum x ≤ preKeyTryFromCapDeltaCum M_cap B_cap := by
  unfold preKeyTryFromDeltaCum preKeyTryFromCapDeltaCum
  refine Nat.add_le_add ?_ (sigTryFromDeltaCum_le_cap hM)
  refine Nat.add_le_add ?_ (Nat.le_refl 108386)
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left 2 (min_right_mono hB))
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 (min_right_mono hM))
    (Nat.mul_le_mul_left 2 (min_right_mono (max8_two_mul_mono hM)))

theorem preKeyTryFromDeltaLive_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromDeltaLive x ≤ preKeyTryFromCapDeltaLive M_cap B_cap := by
  unfold preKeyTryFromDeltaLive preKeyTryFromCapDeltaLive
  refine Nat.add_le_add ?_ (sigTryFromDeltaLive_le_cap hM)
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hM) hB) (Nat.le_refl 16390)

theorem preKeyTryFromDeltaPeak_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromDeltaPeak x ≤ preKeyTryFromCapDeltaPeak M_cap B_cap := by
  unfold preKeyTryFromDeltaPeak preKeyTryFromCapDeltaPeak
  refine Nat.add_le_add ?_ (sigTryFromDeltaPeak_le_cap hM)
  refine Nat.add_le_add ?_ (sigTryFromDeltaLive_le_cap hM)
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 3 hM) hB) (Nat.le_refl 16390)

theorem preKeyTryFromMaxReq_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromMaxReq x ≤ preKeyTryFromCapMaxReq M_cap B_cap := by
  unfold preKeyTryFromMaxReq preKeyTryFromCapMaxReq
  exact max_le_max
    (max_le_max (Nat.le_refl 3138) (max_le_max (Nat.mul_le_mul_left 2 hM) hB))
    (sigTryFromMaxReq_le_cap hM)

theorem phaseCreditSpec_bytesMergeZeroCap_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wt : WireType) (bs : List (BitVec 8)) (L : Nat)
    (hLen : ∀ v rest, CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs = some (v, rest) →
      v.length ≤ L) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt 0#64 bs)
      (6 * L + 19094) (2 * L + 8267) (3 * L + 16398) (max 72 (2 * L)) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_bytesMergeZeroCap_le
    hM wt bs L hLen

theorem phaseCreditSpec_preKeyLoop {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyLoopEnv x)
      (2 * min x.inner.length 135167 + 2 * min (max 8 (2 * x.inner.length)) 135167 + 86170)
      (2 * x.inner.length + 8195)
      (3 * x.inner.length + 16390)
      (max 3138 (2 * x.inner.length)) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_preKeyLoop hM hLow x

theorem phaseCreditSpec_preKeySeg2 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeySeg2Env x) 12677 0 0 1569 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_preKeySeg2 hM hLow x

theorem phaseCreditSpec_preKeySeg4 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeySeg4Env x)
      (2 * min x.bytes.length 135167 + 9539)
      (x.bytes.length + 8195)
      (x.bytes.length + 8195)
      x.bytes.length :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseCreditSpec_preKeySeg4 hM hLow x

theorem preKeyTryFrom_phaseCredit_of_sig {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {sigEnv : List (BitVec 8) → List AllocEvent → Prop}
    (x : PreKeyTryFromArgs) {sc sl sp sr : Nat}
    (hSig : PhaseCreditSpec M (sigEnv x.inner) sc sl sp sr) :
    PhaseCreditSpec M (PreKeyTryFromEnv sigEnv x)
      (2 * min x.inner.length 135167 + 2 * min (max 8 (2 * x.inner.length)) 135167 +
        2 * min x.bytes.length 135167 + 108386 + sc)
      (2 * x.inner.length + x.bytes.length + 16390 + sl)
      (3 * x.inner.length + x.bytes.length + 16390 + sl + sp)
      (max (max 3138 (max (2 * x.inner.length) x.bytes.length)) sr) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFrom_phaseCredit_of_sig
    hM hLow x hSig

theorem preKeyTryFrom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyTryFromBoundedEnv x)
      (preKeyTryFromDeltaCum x)
      (preKeyTryFromDeltaLive x)
      (preKeyTryFromDeltaPeak x)
      (preKeyTryFromMaxReq x) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFrom_phaseCredit hM hLow x

/-! ## Small-Allocation Group Bounds (`PhaseGroupSpec`) -/

abbrev pksmTryFromLoopDeltaGrpS (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromLoopDeltaGrpS N

abbrev pksmTryFromCapDeltaGrpS (N : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaGrpS N

abbrev pksmTryFromDeltaGrpS (x : PksmGhost) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaGrpS x

theorem pksmTryFromLoopDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    pksmTryFromLoopDeltaGrpS N₁ ≤ pksmTryFromLoopDeltaGrpS N₂ :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromLoopDeltaGrpS_mono h

theorem pksmTryFromCapDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    pksmTryFromCapDeltaGrpS N₁ ≤ pksmTryFromCapDeltaGrpS N₂ :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaGrpS_mono h

theorem pksmTryFromDeltaGrpS_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaGrpS x ≤ pksmTryFromCapDeltaGrpS N :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaGrpS_le_cap h

theorem phaseGroupSpec_intoBoxed {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (IntoBoxedBoundedEnv bs) 140011 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_intoBoxed hGrp bs

theorem phaseGroupSpec_intoBoxedOpt {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (opt : Option (List (BitVec 8))) :
    PhaseGroupSpec M (IntoBoxedOptBoundedEnv opt) 140011 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_intoBoxedOpt hGrp opt

theorem phaseGroupSpec_tryClone {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (TryCloneBytesEnv bs) 140011 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_tryClone hGrp bs

theorem phaseGroupSpec_sigTryFromErrTail {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M SigTryFromErrTailEnv 183475 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_sigTryFromErrTail hGrp

theorem phaseGroupSpec_pksmLoopTail {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M PksmLoopTailBoundedEnv 323486 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_pksmLoopTail hGrp

theorem phaseGroupSpec_pksmKyberErrAlloc {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M PksmKyberErrAllocEnv 43464 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_pksmKyberErrAlloc hGrp

theorem pksmTryFromLoop_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (N : Nat) :
    PhaseGroupSpec M (PksmTryFromLoopBoundedEnv N ProtoCaps4.zero)
      (pksmTryFromLoopDeltaGrpS N) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromLoop_phaseGroup hGrp N

theorem phaseGroupSpec_pksmPost_blackbox {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost) :
    PhaseGroupSpec M (PksmPostBoundedEnv bs kyberOpt innerG)
      (280022 + sigTryFromDeltaGrpS innerG) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_pksmPost_blackbox
    hGrp bs kyberOpt innerG

theorem phaseGroupSpec_pksmFull_blackbox {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PksmGhost)
    (LoopEnv : List AllocEvent → Prop)
    (hLoop : ∀ evs, LoopEnv evs →
      ProtoLoop4GroupInv M 323486 x.bytes.length ProtoCaps4.zero evs)
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨ SeqEnv LoopEnv (PksmPostBoundedEnv x.bytes kyberOpt innerG) evs) :
    let N := x.bytes.length
    PhaseGroupSpec M Env
      (2369 * N + 560044 * wireRemGrows N 0 + 603508 + sigTryFromDeltaGrpS innerG) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_pksmFull_blackbox
    hGrp x LoopEnv hLoop kyberOpt innerG Env hEnv

theorem pksmTryFrom_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PksmGhost) :
    PhaseGroupSpec M (PksmTryFromBoundedEnv x) (pksmTryFromDeltaGrpS x) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFrom_phaseGroup hGrp x

abbrev preKeyTryFromCapDeltaGrpS (M_cap B_cap : Nat) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFromCapDeltaGrpS M_cap B_cap

abbrev preKeyTryFromDeltaGrpS (x : PreKeyTryFromArgs) : Nat :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFromDeltaGrpS x

theorem preKeyTryFromDeltaGrpS_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromDeltaGrpS x ≤ preKeyTryFromCapDeltaGrpS M_cap B_cap :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFromDeltaGrpS_le_cap hM hB

theorem phaseGroupSpec_preKeyLoop {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeyLoopEnv x) 1120088 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_preKeyLoop hGrp x

theorem phaseGroupSpec_preKeySeg2 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeySeg2Env x) 140011 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_preKeySeg2 hGrp x

theorem phaseGroupSpec_preKeySeg4 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeySeg4Env x) 140011 :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.phaseGroupSpec_preKeySeg4 hGrp x

theorem preKeyTryFrom_phaseGroup_of_sig {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M)
    {sigEnv : List (BitVec 8) → List AllocEvent → Prop}
    (x : PreKeyTryFromArgs) {sg : Nat}
    (hSig : PhaseGroupSpec M (sigEnv x.inner) sg) :
    PhaseGroupSpec M (PreKeyTryFromEnv sigEnv x) (1400110 + sg) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFrom_phaseGroup_of_sig
    hGrp x hSig

theorem preKeyTryFrom_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeyTryFromBoundedEnv x) (preKeyTryFromDeltaGrpS x) :=
  LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.preKeyTryFrom_phaseGroup hGrp x

end LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
