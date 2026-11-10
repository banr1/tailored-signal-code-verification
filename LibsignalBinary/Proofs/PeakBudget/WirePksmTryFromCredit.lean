/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# End-to-End `PhaseCreditSpec` & `PhaseGroupSpec` Combinators for `PreKeySignalMessage::try_from`

Connects `WirePksmTryFromHelpers` and `WirePksmLoopCredit` to `WireFieldDomainCaps`,
`WireMsgPeakSpec`, and `ResponderWire.PreKeyTryFromBaseBudget`:
1. Post-loop, error-tail, and Kyber validation error bridges (`IntoBoxedBoundedEnv`,
   `IntoBoxedOptBoundedEnv`, `TryCloneBytesEnv`, `PksmLoopTailBoundedEnv`, `PksmKyberErrAllocEnv`).
2. `decodeProto` and `pksmParse` deterministic field extractors and byte-length bounds.
3. All-inputs `PksmTryFromBoundedEnv` (`PksmGhost`) black-box `PhaseCreditSpec` and `PhaseGroupSpec`
   theorems.
4. Canonical `ResponderWire.PreKeyTryFromBaseBudget` (`PreKeyTryFromArgs`) `PhaseCreditSpec` and
   `PhaseGroupSpec` theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit

open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi
  (KyberPayload PreKeySignalMessage ProtoPreKeySignalMessage)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (PreKeyTryFromArgs psmRem2 psmRem3 psmRem4 psmRem8)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeKey decodeVarint decodeVarintAux decodeVarint_encodeVarint encodeVarint
   mergeBytes mergeUint32 protoSignalCodec skipBytes skipField skipGroup skipScalar)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost reserveCap)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm
  (decodeProto decodeProtoLoop emptyProto kyberOk kyberPayloadOf mergeProtoField pksmParse)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
  (FromSeg2Env FromSeg3Env PreKeyLoopEnv PreKeyPostEnv PreKeySeg2Env PreKeySeg4Env
   PreKeySeg4OkEnv PreKeyTryFromEnv preKeyLoopEvents)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (FreeOnlyAlign16Evs ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
  (pksmParse_lengths_le signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (DecodeErrorPushBoundedEnv IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv
   SigTryFromBoundedEnv SigTryFromErrTailEnv TryCloneBytesEnv WireGroupHyps WireLowInterceptHyps
   intoBoxedCapEvents sigTryFromCapDeltaCum sigTryFromCapDeltaGrpS sigTryFromCapDeltaGrpS_mono
   sigTryFromCapDeltaLive sigTryFromCapDeltaPeak sigTryFromCapMaxReq sigTryFromDeltaCum
   sigTryFromDeltaCum_le_cap sigTryFromDeltaGrpS sigTryFromDeltaGrpS_le_cap sigTryFromDeltaLive
   sigTryFromDeltaLive_le_cap sigTryFromDeltaPeak sigTryFromDeltaPeak_le_cap
   sigTryFromMaxReq sigTryFromMaxReq_le_cap sigTryFrom_phaseCredit sigTryFrom_phaseGroup
   wireRemGrows wireRemGrows_mono)
open LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit
  (ProtoLoop4BoundedEnv ProtoLoop4GroupInv ProtoLoop4StateInv ProtoLoop4StateInvS
   ProtoLoop4StateInvTight phaseCreditSpec_errTail1_aff phaseCreditSpec_errTail2_S
   phaseCreditSpec_errTail2_aff phaseCreditSpec_intoBoxedBounded_S
   phaseCreditSpec_intoBoxedBounded_le phaseCreditSpec_intoBoxedSmall_S
   phaseCreditSpec_protoLoop4_S phaseCreditSpec_protoLoop4_aff
   phaseCreditSpec_tryCloneBounded_S phaseCreditSpec_tryCloneBounded_le
   phaseGroupSpec_errTail1 phaseGroupSpec_errTail2 phaseGroupSpec_intoBoxedBounded
   phaseGroupSpec_protoLoop4 phaseGroupSpec_tryCloneBounded)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (ProtoCaps4 ProtoField4 bytesMergeOkPeakDelta bytesMergeOkSmallDelta
   mergeBytes_length_sum req_align_doReserveClearEvents
   reserveCap_zero_le_max reserveClearLargeDelta reserveClearSmallDelta
   stepEvents_bytesMergeOk_cancel vecLargeCredit vecLargeCredit_eq_bytesLargeLive
   vecLargeCredit_le_aff vecLargeCredit_zero)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers (bytesLargeLive)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (bytesLargeLive_le_two_mul_of_le_max phaseGroupSpec_bytesMergeZeroCap
   phaseGroupSpec_intoBoxedSlice phaseGroupSpec_rustAlloc_le108 phaseGroupSpec_tryCloneBytes)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (TryCloneFromRefEnv intoBoxedSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## Nominal Post-Loop, Loop Error-Tail, & Kyber Error Bridges -/

theorem intoBoxedCapEvents_eq_intoBoxedSliceEvents (cap : BitVec 64) (bs : List (BitVec 8)) :
    intoBoxedCapEvents cap bs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩ :=
  rfl

/-- Affine `PhaseCreditSpec` for `WireMsgPeakSpec.IntoBoxedBoundedEnv bs` with `bs.length ≤ N`. -/
theorem phaseCreditSpec_intoBoxedBounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {bs : List (BitVec 8)} (hLen : bs.length ≤ N) :
    PhaseCreditSpec M (IntoBoxedBoundedEnv bs) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  phaseCreditSpec_intoBoxedBounded_le hM N (IntoBoxedBoundedEnv bs) fun _ hE => by
    obtain ⟨cap, _, _, rfl⟩ := hE
    exact Or.inr ⟨bs, cap, hLen, rfl⟩

/-- Affine `PhaseCreditSpec` for `WireMsgPeakSpec.IntoBoxedOptBoundedEnv opt` (e.g. Kyber
`Option` ciphertext) when any present slice has length `≤ N`. -/
theorem phaseCreditSpec_intoBoxedOptBounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {opt : Option (List (BitVec 8))}
    (hLen : ∀ bs, opt = some bs → bs.length ≤ N) :
    PhaseCreditSpec M (IntoBoxedOptBoundedEnv opt) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  phaseCreditSpec_intoBoxedBounded_le hM N (IntoBoxedOptBoundedEnv opt) fun _ hE => by
    cases opt with
    | none => exact Or.inl hE
    | some bs =>
      obtain ⟨cap, _, _, rfl⟩ := hE
      exact Or.inr ⟨bs, cap, hLen bs rfl, rfl⟩

/-- Affine `PhaseCreditSpec` for `WireMsgPeakSpec.TryCloneBytesEnv bs` with `bs.length ≤ N`. -/
theorem phaseCreditSpec_tryCloneBytes {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {N : Nat} {bs : List (BitVec 8)} (hLen : bs.length ≤ N) :
    PhaseCreditSpec M (TryCloneBytesEnv bs) (2 * N + 9539) (N + 8195) (N + 8195) N :=
  phaseCreditSpec_tryCloneBounded_le hM N (TryCloneBytesEnv bs) fun _ hE =>
    Or.inr ⟨bs, hLen, hE⟩

/-- Affine `PhaseCreditSpec` for `WireMsgPeakSpec.SigTryFromErrTailEnv`. -/
theorem phaseCreditSpec_sigTryFromErrTail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M SigTryFromErrTailEnv 19478 16590 16590 128 :=
  phaseCreditSpec_errTail1_aff hM SigTryFromErrTailEnv fun _ hE => by
    have hNilFree : FreeOnlyEvs [] := FreeOnlyAlign16Evs.nil.toFreeOnlyEvs
    cases hE with
    | nil => exact ⟨[], [], rfl, hNilFree, Or.inl rfl⟩
    | fromOnly => exact ⟨rustAllocEvents 72 8, [], by simp, hNilFree, Or.inr (Or.inl rfl)⟩
    | @fromPush evs_p hp =>
      refine ⟨rustAllocEvents 72 8 ++ evs_p, [], by simp, hNilFree, Or.inr (Or.inr ⟨evs_p, rfl, ?_⟩)⟩
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega

/-- Bounded protobuf decode loop exit/error-tail envelope for `PreKeySignalMessage::try_from`,
covering normal exit (`[]` / `FreeOnlyEvs`), 1-push decode errors (`merge_uint32` / `bytes::merge` /
`skip_field`), and 2-push nested group errors (`skip_group` inside `skip_field` + `merge_field`). -/
inductive PksmLoopTailBoundedEnv : List AllocEvent → Prop where
  | freeOnly {evs : List AllocEvent} :
      FreeOnlyEvs evs →
      PksmLoopTailBoundedEnv evs
  | err1 {evs_p evs_free : List AllocEvent} :
      DecodeErrorPushBoundedEnv 0 evs_p →
      FreeOnlyEvs evs_free →
      PksmLoopTailBoundedEnv (rustAllocEvents 72 8 ++ evs_p ++ evs_free)
  | err2 {evs_p0 evs_p1 evs_free : List AllocEvent} :
      DecodeErrorPushBoundedEnv 0 evs_p0 →
      DecodeErrorPushBoundedEnv 1 evs_p1 →
      FreeOnlyEvs evs_free →
      PksmLoopTailBoundedEnv (rustAllocEvents 72 8 ++ evs_p0 ++ evs_p1 ++ evs_free)

theorem PksmLoopTailBoundedEnv.of_sigTryFromErrTail {evs : List AllocEvent}
    (h : SigTryFromErrTailEnv evs) : PksmLoopTailBoundedEnv evs := by
  have hNilFree : FreeOnlyEvs [] := FreeOnlyAlign16Evs.nil.toFreeOnlyEvs
  cases h with
  | nil => exact .freeOnly hNilFree
  | fromOnly =>
    simpa using PksmLoopTailBoundedEnv.err1 (evs_p := []) (evs_free := []) (Or.inl rfl) hNilFree
  | @fromPush evs_p hp =>
    simpa using PksmLoopTailBoundedEnv.err1 (evs_p := evs_p) (evs_free := []) hp hNilFree

/-- Affine `PhaseCreditSpec` for `PksmLoopTailBoundedEnv` (up to 2 `<DecodeError>::push` frames +
`FreeOnlyEvs`). -/
theorem phaseCreditSpec_pksmLoopTail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M PksmLoopTailBoundedEnv 29273 24913 24913 128 :=
  phaseCreditSpec_errTail2_aff hM PksmLoopTailBoundedEnv fun evs hE => by
    cases hE with
    | freeOnly hf =>
      exact ⟨[], [], [], evs, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, hf⟩
    | @err1 evs_p evs_free hp hf =>
      have hp0 : evs_p = [] ∨ evs_p = rustAllocEvents 128 8 := by
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      exact ⟨rustAllocEvents 72 8, evs_p, [], evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0, Or.inl rfl, hf⟩
    | @err2 evs_p0 evs_p1 evs_free hp0 hp1 hf =>
      have hp0' : evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8 := by
        rcases hp0 with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      have hp1' : evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8 := by
        rcases hp1 with rfl | ⟨hZ, _⟩ | ⟨_, rfl⟩
        · exact Or.inl rfl
        · omega
        · exact Or.inr rfl
      exact ⟨rustAllocEvents 72 8, evs_p0, evs_p1, evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0', hp1', hf⟩

/-- Kyber 3-way validation error allocation in Block 111 (`+0x684 → +0xa24`):
allocates a 68-byte (`kyber_half_err`) or 54-byte (`kyber_neither_v4_err`) error `String`. -/
def PksmKyberErrAllocEnv (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents 68 1 ∨ evs = rustAllocEvents 54 1

/-- Affine `PhaseCreditSpec` for `PksmKyberErrAllocEnv` (`maxReq = 68`). -/
theorem phaseCreditSpec_pksmKyberErrAlloc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M PksmKyberErrAllocEnv 9675 8263 8263 68 := by
  have h68 := PhaseCreditSpec.rustAlloc_aff hM (req := 68) (al := 1) (by decide)
  have h54 := PhaseCreditSpec.rustAlloc_aff hM (req := 54) (al := 1) (by decide)
  exact ((h68.or h54).of_imp (fun _ h => h)).mono (by decide) (by decide) (by decide) (by decide)

theorem phaseCreditSpec_intoBoxedOptBounded_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S N : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    {opt : Option (List (BitVec 8))}
    (hLen : ∀ bs, opt = some bs → bs.length ≤ N) :
    PhaseCreditSpec M (IntoBoxedOptBoundedEnv opt) (2 * min N S + 9539) (N + 8195) (N + 8195) N :=
  phaseCreditSpec_intoBoxedBounded_S hM hSm N (IntoBoxedOptBoundedEnv opt) fun _ hE => by
    cases opt with
    | none => exact Or.inl hE
    | some bs =>
      obtain ⟨cap, _, _, rfl⟩ := hE
      exact Or.inr ⟨bs, cap, hLen bs rfl, rfl⟩

theorem phaseCreditSpec_tryCloneBytes_S_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S N : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    {bs : List (BitVec 8)} (hLen : bs.length ≤ N) :
    PhaseCreditSpec M (TryCloneBytesEnv bs) (2 * min N S + 9539) (N + 8195) (N + 8195) N :=
  phaseCreditSpec_tryCloneBounded_S hM hSm N (TryCloneBytesEnv bs) fun _ hE =>
    Or.inr ⟨bs, hLen, hE⟩

theorem phaseCreditSpec_pksmLoopTail_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S) :
    PhaseCreditSpec M PksmLoopTailBoundedEnv 29273 0 0 128 :=
  phaseCreditSpec_errTail2_S hM hSm hS128 PksmLoopTailBoundedEnv fun evs hE => by
    cases hE with
    | freeOnly hf =>
      exact ⟨[], [], [], evs, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, hf⟩
    | @err1 evs_p evs_free hp hf =>
      have hp0 : evs_p = [] ∨ evs_p = rustAllocEvents 128 8 := by
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      exact ⟨rustAllocEvents 72 8, evs_p, [], evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0, Or.inl rfl, hf⟩
    | @err2 evs_p0 evs_p1 evs_free hp0 hp1 hf =>
      have hp0' : evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8 := by
        rcases hp0 with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      have hp1' : evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8 := by
        rcases hp1 with rfl | ⟨hZ, _⟩ | ⟨_, rfl⟩
        · exact Or.inl rfl
        · omega
        · exact Or.inr rfl
      exact ⟨rustAllocEvents 72 8, evs_p0, evs_p1, evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0', hp1', hf⟩

theorem phaseCreditSpec_pksmKyberErrAlloc_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS68 : 68 ≤ S) :
    PhaseCreditSpec M PksmKyberErrAllocEnv 9675 0 0 68 := by
  have h68Sm : 68 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h54Sm : 54 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h68 := (PhaseCreditSpec.rustAlloc_small M (req := 68) (al := 1) (by decide) (by decide) h68Sm).mono
    (hM.smallAlloc_le h68Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 68)
  have h54 := (PhaseCreditSpec.rustAlloc_small M (req := 54) (al := 1) (by decide) (by decide) h54Sm).mono
    (hM.smallAlloc_le h54Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 54)
  exact ((h68.or h54).of_imp (fun _ h => h)).mono (by decide) (by decide) (by decide) (by decide)

/-! ## `decodeProto` & `pksmParse` Deterministic Field Extractors & Length Bounds -/

private theorem decodeVarintAux_rest_le :
    ∀ (bs : List (BitVec 8)) (i : Nat) (acc v : BitVec 64) (rest : List (BitVec 8)),
      decodeVarintAux i acc bs = some (v, rest) → rest.length ≤ bs.length
  | [], _, _, _, _, h => by simp [decodeVarintAux] at h
  | b :: tl, i, acc, v, rest, h => by
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · simp at h
      · injection h with hEq
        injection hEq with _ hRest
        subst hRest
        exact Nat.le_succ _
    · split at h
      · simp at h
      · exact Nat.le_trans (decodeVarintAux_rest_le tl (i + 1) _ v rest h) (Nat.le_succ _)

private theorem decodeKey_rest_le {bs rest : List (BitVec 8)} {tw : Nat × WireType}
    (h : decodeKey bs = some (tw, rest)) : rest.length ≤ bs.length := by
  unfold decodeKey at h
  rcases hd : decodeVarint bs with _ | ⟨key, r⟩ <;> rw [hd] at h
  · cases h
  · dsimp only at h
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · simp only [hk, ↓reduceIte] at h; cases h
    · simp only [hk, ↓reduceIte] at h
      rcases hw : WireType.ofNat? (key.toNat % 8) with _ | wt <;> rw [hw] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with h'
        obtain ⟨_, rfl⟩ := Prod.mk.inj h'
        exact decodeVarintAux_rest_le _ 0 0 key _ hd

private theorem skipBytes_rest_le {n : Nat} {bs r : List (BitVec 8)}
    (h : skipBytes n bs = some r) : r.length ≤ bs.length := by
  unfold skipBytes at h
  split_ifs at h
  injection h with hr
  rw [← hr, List.length_drop]
  omega

private theorem skipScalar_rest_le {wt : WireType} {bs r : List (BitVec 8)}
    (h : skipScalar wt bs = some r) : r.length ≤ bs.length := by
  cases wt with
  | varint =>
    unfold skipScalar at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨v, rest⟩, hd, rfl⟩ := h
    exact decodeVarintAux_rest_le bs 0 0 v rest hd
  | thirtyTwoBit => exact skipBytes_rest_le h
  | sixtyFourBit => exact skipBytes_rest_le h
  | lengthDelimited =>
    unfold skipScalar at h
    rcases hd : decodeVarint bs with _ | ⟨len, rest⟩ <;> rw [hd] at h
    · cases h
    · exact Nat.le_trans (skipBytes_rest_le h) (decodeVarintAux_rest_le bs 0 0 len rest hd)
  | startGroup => cases h
  | endGroup => cases h

private theorem skipField_skipGroup_rest_le :
    ∀ fuel : Nat,
      (∀ depth tag wt bs r, skipField fuel depth tag wt bs = some r → r.length ≤ bs.length) ∧
      (∀ depth tag bs r, skipGroup fuel depth tag bs = some r → r.length ≤ bs.length)
  | 0 => ⟨(fun _ _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩
  | fuel + 1 => by
    obtain ⟨ihF, ihG⟩ := skipField_skipGroup_rest_le fuel
    refine ⟨?_, ?_⟩
    · intro depth tag wt bs r h
      unfold skipField at h
      split at h
      · simp at h
      · cases wt with
        | endGroup => cases h
        | startGroup => exact ihG depth tag bs r h
        | varint => exact skipScalar_rest_le h
        | sixtyFourBit => exact skipScalar_rest_le h
        | lengthDelimited => exact skipScalar_rest_le h
        | thirtyTwoBit => exact skipScalar_rest_le h
    · intro depth tag bs r h
      unfold skipGroup at h
      rcases hk : decodeKey bs with _ | ⟨⟨itag, iwt⟩, rest⟩ <;> rw [hk] at h
      · cases h
      · have hrest := decodeKey_rest_le hk
        cases iwt <;> dsimp only at h
        case endGroup =>
          split at h
          · injection h with hr
            rwa [← hr]
          · simp at h
        all_goals
          rcases hs : skipField fuel (depth - 1) itag _ rest with _ | rest' <;> rw [hs] at h
          · cases h
          · exact Nat.le_trans (ihG depth tag rest' r h)
              (Nat.le_trans (ihF _ _ _ rest rest' hs) hrest)

private theorem mergeUint32_rest_le {wt : WireType} {bs r : List (BitVec 8)} {v : BitVec 32}
    (h : mergeUint32 wt bs = some (v, r)) : r.length ≤ bs.length := by
  unfold mergeUint32 at h
  split_ifs at h
  rcases hd : decodeVarint bs with _ | ⟨val, rest⟩ <;> rw [hd] at h
  · cases h
  · injection h with h'
    obtain ⟨_, rfl⟩ := Prod.mk.inj h'
    exact decodeVarintAux_rest_le _ 0 0 val _ hd

private def protoPksmAllBounded (N : Nat) (m : ProtoPreKeySignalMessage) : Prop :=
  (∀ v, m.baseKey = some v → v.length ≤ N) ∧
  (∀ v, m.identityKey = some v → v.length ≤ N) ∧
  (∀ v, m.message = some v → v.length ≤ N) ∧
  (∀ v, m.kyberCiphertext = some v → v.length ≤ N)

private theorem decodeProtoLoop_all_le (N : Nat) :
    ∀ (fuel : Nat) (m m' : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ N →
      protoPksmAllBounded N m →
      decodeProtoLoop fuel m bs = some m' →
      protoPksmAllBounded N m'
  | _, m, m', [], _, hm, h => by
    unfold decodeProtoLoop at h
    injection h with hm'
    rwa [← hm']
  | 0, _, _, _ :: _, _, _, h => by cases h
  | fuel + 1, m, m', b :: tl, hbs, hm, h => by
    unfold decodeProtoLoop at h
    rcases hk : decodeKey (b :: tl) with _ | ⟨⟨tag, wt⟩, rest⟩ <;> rw [hk] at h
    · cases h
    · have hrest : rest.length ≤ N := Nat.le_trans (decodeKey_rest_le hk) hbs
      dsimp only at h
      rcases hmF : mergeProtoField m tag wt rest with _ | ⟨m1, rest1⟩ <;> rw [hmF] at h
      · cases h
      · have hstep : rest1.length ≤ N ∧ protoPksmAllBounded N m1 := by
          unfold mergeProtoField at hmF
          split at hmF <;> simp only [Option.map_eq_some_iff] at hmF
          · obtain ⟨⟨_, r⟩, hmu, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_rest_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have hsum := mergeBytes_length_sum hmb
            refine ⟨by omega, ?_, hm.2.1, hm.2.2⟩
            intro w hw; injection hw with hw'; subst hw'; omega
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have hsum := mergeBytes_length_sum hmb
            refine ⟨by omega, hm.1, ?_, hm.2.2⟩
            intro w hw; injection hw with hw'; subst hw'; omega
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have hsum := mergeBytes_length_sum hmb
            refine ⟨by omega, hm.1, hm.2.1, ?_, hm.2.2.2⟩
            intro w hw; injection hw with hw'; subst hw'; omega
          · obtain ⟨⟨_, r⟩, hmu, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_rest_le hmu) hrest, hm⟩
          · obtain ⟨⟨_, r⟩, hmu, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_rest_le hmu) hrest, hm⟩
          · obtain ⟨⟨_, r⟩, hmu, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans (mergeUint32_rest_le hmu) hrest, hm⟩
          · obtain ⟨⟨v, r⟩, hmb, hmr⟩ := hmF
            dsimp only at hmr
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            have hsum := mergeBytes_length_sum hmb
            refine ⟨by omega, hm.1, hm.2.1, hm.2.2.1, ?_⟩
            intro w hw; injection hw with hw'; subst hw'; omega
          · obtain ⟨r, hsk, hmr⟩ := hmF
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmr
            exact ⟨Nat.le_trans ((skipField_skipGroup_rest_le _).1 _ _ _ _ _ hsk) hrest, hm⟩
        exact decodeProtoLoop_all_le N fuel m1 m' rest1 hstep.1 hstep.2 h

/-- Every decoded `ProtoPreKeySignalMessage` from `decodeProto body = some m` has all four
`Vec<u8>` fields (`baseKey`, `identityKey`, `message`, `kyberCiphertext`) bounded by `body.length`. -/
theorem decodeProto_fields_le {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    (h : decodeProto body = some m) :
    (∀ v, m.baseKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.identityKey = some v → v.length ≤ body.length) ∧
    (∀ v, m.message = some v → v.length ≤ body.length) ∧
    (∀ v, m.kyberCiphertext = some v → v.length ≤ body.length) :=
  decodeProtoLoop_all_le body.length body.length emptyProto m body (Nat.le_refl _)
    ⟨(fun _ hv => by cases hv), (fun _ hv => by cases hv),
     (fun _ hv => by cases hv), (fun _ hv => by cases hv)⟩ h

/-- Deterministic inner `SignalMessage` slice extracted from `decodeProto (bs.drop 1)`. -/
def pksmDecodedInnerBytes : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | _ :: body =>
    match decodeProto body with
    | some m => m.message.getD []
    | none => []

/-- Deterministic optional Kyber ciphertext slice extracted from `decodeProto (bs.drop 1)`. -/
def pksmDecodedKyberOpt : List (BitVec 8) → Option (List (BitVec 8))
  | [] => none
  | _ :: body =>
    match decodeProto body with
    | some m => m.kyberCiphertext
    | none => none

/-- Deterministic `TryFromGhost` argument passed to `SignalMessage::try_from`. -/
def pksmInnerGhost (x : PksmGhost) : TryFromGhost :=
  ⟨0#64, pksmDecodedInnerBytes x.bytes, 0#64⟩

theorem pksmDecodedInnerBytes_length_le (bs : List (BitVec 8)) :
    (pksmDecodedInnerBytes bs).length ≤ bs.length := by
  cases bs with
  | nil => simp [pksmDecodedInnerBytes]
  | cons vb body =>
    dsimp only [pksmDecodedInnerBytes]
    rcases hd : decodeProto body with _ | m
    · simp
    · dsimp only
      rcases hm : m.message with _ | msg
      · simp
      · have hle := (decodeProto_fields_le hd).2.2.1 msg hm
        simp only [Option.getD_some, List.length_cons]
        omega

theorem pksmDecodedKyberOpt_length_le (bs : List (BitVec 8)) :
    ∀ kp, pksmDecodedKyberOpt bs = some kp → kp.length ≤ bs.length := by
  intro kp hkp
  cases bs with
  | nil => simp [pksmDecodedKyberOpt] at hkp
  | cons vb body =>
    dsimp only [pksmDecodedKyberOpt] at hkp
    rcases hd : decodeProto body with _ | m <;> rw [hd] at hkp
    · cases hkp
    · have hle := (decodeProto_fields_le hd).2.2.2 kp hkp
      simp only [List.length_cons]
      omega

theorem pksmParse_inner_eq_decoded {bs : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse bs = some pm) :
    pm.message.serialized = pksmDecodedInnerBytes bs := by
  have _ := pksmParse_lengths_le h
  rcases bs with _ | ⟨vb, body⟩
  · cases h
  · unfold pksmParse at h
    dsimp only [pksmDecodedInnerBytes] at h ⊢
    split_ifs at h
    rcases hd : decodeProto body with _ | m <;> rw [hd] at h
    · cases h
    · dsimp only at h ⊢
      rcases hbk : m.baseKey with _ | bk <;> rw [hbk] at h
      · cases h
      · rcases hik : m.identityKey with _ | ik <;> rw [hik] at h
        · cases h
        · rcases hmsg : m.message with _ | msg <;> rw [hmsg] at h
          · cases h
          · rcases hsid : m.signedPreKeyId with _ | sid <;> rw [hsid] at h
            · cases h
            · dsimp only at h
              split_ifs at h
              rcases hpk1 : PublicKey.deserialize bk with _ | bKey <;> rw [hpk1] at h
              · cases h
              · rcases hpk2 : PublicKey.deserialize ik with _ | iKey <;> rw [hpk2] at h
                · cases h
                · rcases hsm : SignalMessage.tryFrom protoSignalCodec msg with _ | inner <;>
                    rw [hsm] at h
                  · cases h
                  · injection h with hpm
                    rw [← hpm]
                    have hInnerSer := (signalMessage_tryFrom_lengths_le hsm).1
                    simpa [Option.getD] using hInnerSer

theorem pksmParse_kyber_eq_decoded {bs : List (BitVec 8)} {pm : PreKeySignalMessage}
    (h : pksmParse bs = some pm) :
    pm.kyberPayload.map (·.ciphertext) = pksmDecodedKyberOpt bs := by
  rcases bs with _ | ⟨vb, body⟩
  · cases h
  · unfold pksmParse at h
    dsimp only [pksmDecodedKyberOpt] at h ⊢
    split_ifs at h
    rcases hd : decodeProto body with _ | m <;> rw [hd] at h
    · cases h
    · dsimp only at h ⊢
      rcases hbk : m.baseKey with _ | bk <;> rw [hbk] at h
      · cases h
      · rcases hik : m.identityKey with _ | ik <;> rw [hik] at h
        · cases h
        · rcases hmsg : m.message with _ | msg <;> rw [hmsg] at h
          · cases h
          · rcases hsid : m.signedPreKeyId with _ | sid <;> rw [hsid] at h
            · cases h
            · dsimp only at h
              by_cases hky : kyberOk (vb >>> 4) m = true
              · simp only [hky, ↓reduceIte] at h
                rcases hpk1 : PublicKey.deserialize bk with _ | bKey <;> rw [hpk1] at h
                · cases h
                · rcases hpk2 : PublicKey.deserialize ik with _ | iKey <;> rw [hpk2] at h
                  · cases h
                  · rcases hsm : SignalMessage.tryFrom protoSignalCodec msg with _ | inner <;>
                      rw [hsm] at h
                    · cases h
                    · injection h with hpm
                      rw [← hpm]
                      unfold kyberOk at hky
                      rcases hkpid : m.kyberPreKeyId with _ | kpid <;>
                        rcases hkpct : m.kyberCiphertext with _ | kpct <;>
                        simp [hkpid, hkpct, kyberPayloadOf] at hky ⊢
              · simp [hky] at h

/-! ## All-Inputs `PreKeySignalMessage::try_from` Envelopes & Black-Box `PhaseCreditSpec` -/

/-- Canonical 4-field slice-budgeted protobuf decode loop envelope for `PreKeySignalMessage::try_from`. -/
abbrev PksmTryFromLoopBoundedEnv : Nat → ProtoCaps4 → List AllocEvent → Prop :=
  ProtoLoop4BoundedEnv PksmLoopTailBoundedEnv

/-- Segment 4 post-inner-`SignalMessage::try_from` envelope (`.error` `FreeOnlyEvs` cleanup, or `.ok`
`TryCloneBytesEnv bs` + `FreeOnlyEvs`). -/
def PksmPostSeg4Env (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (TryCloneBytesEnv bs) FreeOnlyEvs evs

/-- Post-Kyber-validation envelope (`IdentityKey::try_from` `.error` `FreeOnlyEvs`, or `.ok`
followed by `SigTryFromBoundedEnv innerG` and `PksmPostSeg4Env bs`). -/
def PksmAfterKyberOkEnv (bs : List (BitVec 8)) (innerG : TryFromGhost)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (SigTryFromBoundedEnv innerG) (SeqEnv (PksmPostSeg4Env bs) FreeOnlyEvs) evs

/-- Complete post-loop envelope of Block 111 (`PreKeySignalMessage::try_from`) in exact binary call
order:
1. Missing mandatory field or `base_key` `PublicKey::deserialize` error (`FreeOnlyEvs`);
2. Kyber half-present (`68` B) or v4-neither (`54` B) error `String` alloc + `FreeOnlyEvs`;
3. Kyber valid (`IntoBoxedOptBoundedEnv kyberOpt`) → `PksmAfterKyberOkEnv bs innerG`. -/
def PksmPostBoundedEnv (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv PksmKyberErrAllocEnv FreeOnlyEvs evs ∨
  SeqEnv FreeOnlyEvs
    (SeqEnv (IntoBoxedOptBoundedEnv kyberOpt) (PksmAfterKyberOkEnv bs innerG)) evs

/-- Full all-inputs allocator envelope for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`
(Block `111`, `PksmTryFromPlacedBudget`). -/
def PksmTryFromBoundedEnv (x : PksmGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  SeqEnv (PksmTryFromLoopBoundedEnv x.bytes.length ProtoCaps4.zero)
    (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)) evs

def pksmTryFromCapDeltaCum (N : Nat) : Nat :=
  94 * N + 16 * min (max 8 (2 * N)) 135167 + 38156 * wireRemGrows N 0 +
    4 * min N 135167 + 48351 + sigTryFromCapDeltaCum N

def pksmTryFromCapDeltaLive (N : Nat) : Nat :=
  4 * N + 49170 + sigTryFromCapDeltaLive N

def pksmTryFromCapDeltaPeak (N : Nat) : Nat :=
  4 * N + 49170 + sigTryFromCapDeltaLive N + sigTryFromCapDeltaPeak N

def pksmTryFromCapMaxReq (N : Nat) : Nat :=
  max (max 128 (2 * N)) (sigTryFromCapMaxReq N)

def pksmTryFromDeltaCum (x : PksmGhost) : Nat :=
  94 * x.bytes.length + 16 * min (max 8 (2 * x.bytes.length)) 135167 +
    38156 * wireRemGrows x.bytes.length 0 + 4 * min x.bytes.length 135167 + 48351 +
    sigTryFromDeltaCum (pksmInnerGhost x)

def pksmTryFromDeltaLive (x : PksmGhost) : Nat :=
  4 * x.bytes.length + 49170 + sigTryFromDeltaLive (pksmInnerGhost x)

def pksmTryFromDeltaPeak (x : PksmGhost) : Nat :=
  4 * x.bytes.length + 49170 +
    sigTryFromDeltaLive (pksmInnerGhost x) + sigTryFromDeltaPeak (pksmInnerGhost x)

def pksmTryFromMaxReq (x : PksmGhost) : Nat :=
  max (max 128 (2 * x.bytes.length)) (sigTryFromMaxReq (pksmInnerGhost x))

private theorem min_right_mono {a b S : Nat} (h : a ≤ b) : min a S ≤ min b S := by
  omega

private theorem max8_two_mul_mono {a b : Nat} (h : a ≤ b) : max 8 (2 * a) ≤ max 8 (2 * b) := by
  omega

theorem pksmTryFromDeltaCum_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaCum x ≤ pksmTryFromCapDeltaCum N := by
  have hInner : (pksmInnerGhost x).bytes.length ≤ N :=
    Nat.le_trans (pksmDecodedInnerBytes_length_le x.bytes) h
  unfold pksmTryFromDeltaCum pksmTryFromCapDeltaCum
  refine Nat.add_le_add ?_ (sigTryFromDeltaCum_le_cap hInner)
  refine Nat.add_le_add ?_ (Nat.le_refl 48351)
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left 4 (min_right_mono h))
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left 38156 (wireRemGrows_mono 0 h))
  exact Nat.add_le_add (Nat.mul_le_mul_left 94 h)
    (Nat.mul_le_mul_left 16 (min_right_mono (max8_two_mul_mono h)))

theorem pksmTryFromDeltaLive_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaLive x ≤ pksmTryFromCapDeltaLive N := by
  have hInner : (pksmInnerGhost x).bytes.length ≤ N :=
    Nat.le_trans (pksmDecodedInnerBytes_length_le x.bytes) h
  unfold pksmTryFromDeltaLive pksmTryFromCapDeltaLive
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 4 h) (Nat.le_refl 49170))
    (sigTryFromDeltaLive_le_cap hInner)

theorem pksmTryFromDeltaPeak_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaPeak x ≤ pksmTryFromCapDeltaPeak N := by
  have hInner : (pksmInnerGhost x).bytes.length ≤ N :=
    Nat.le_trans (pksmDecodedInnerBytes_length_le x.bytes) h
  unfold pksmTryFromDeltaPeak pksmTryFromCapDeltaPeak
  refine Nat.add_le_add ?_ (sigTryFromDeltaPeak_le_cap hInner)
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 4 h) (Nat.le_refl 49170))
    (sigTryFromDeltaLive_le_cap hInner)

theorem pksmTryFromMaxReq_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromMaxReq x ≤ pksmTryFromCapMaxReq N := by
  have hInner : (pksmInnerGhost x).bytes.length ≤ N :=
    Nat.le_trans (pksmDecodedInnerBytes_length_le x.bytes) h
  have hs := sigTryFromMaxReq_le_cap hInner
  unfold pksmTryFromMaxReq pksmTryFromCapMaxReq
  exact max_le_max (max_le_max (Nat.le_refl 128) (Nat.mul_le_mul_left 2 h)) hs

private theorem freeOrSeqFree_cum {A : Nat} : max 0 (A + 0) ≤ A := by omega
private theorem freeOrSeqFree_live {A : Nat} : max 0 (A + 0) ≤ A := by omega
private theorem freeOrSeqFree_peak {A P : Nat} (h : A ≤ P) : max 0 (max P (A + 0)) ≤ P := by omega
private theorem freeOrSeqFree_req {R : Nat} : max 0 (max R 0) ≤ R := by omega

private theorem pksmAfterKyber_cum {A SC : Nat} : max 0 (SC + (A + 0)) ≤ A + SC := by omega
private theorem pksmAfterKyber_live {L SL : Nat} : max 0 (SL + (L + 0)) ≤ L + SL := by omega
private theorem pksmAfterKyber_peak {L SL SP : Nat} :
    max 0 (max SP (SL + max L (L + 0))) ≤ L + SL + SP := by omega
private theorem pksmAfterKyber_req {N SR : Nat} :
    max 0 (max SR (max N 0)) ≤ max N SR := by omega

private theorem pksmPost_cum {MB SC kErr k₁ k₂ k : Nat} (h1 : kErr ≤ k) (h2 : k₁ + k₂ ≤ k) :
    max 0 (max kErr (0 + ((2 * MB + k₁) + (2 * MB + k₂ + SC)))) ≤ 4 * MB + k + SC := by omega
private theorem pksmPost_live {N k₀ k SL : Nat} (hk : k₀ + k₀ ≤ k) :
    max 0 (max 0 (0 + ((N + k₀) + (N + k₀ + SL)))) ≤ 2 * N + k + SL := by omega
private theorem pksmPost_peak {N k₀ k SL SP : Nat} (hk : k₀ + k₀ ≤ k) :
    max 0 (max 0 (max 0 (0 + max (N + k₀) ((N + k₀) + (N + k₀ + SL + SP))))) ≤
      2 * N + k + SL + SP := by omega
private theorem pksmPost_req {N SR : Nat} :
    max 0 (max 68 (max 0 (max N (max N SR)))) ≤ max 68 (max N SR) := by omega

private theorem phaseCreditSpec_pksmPost_blackbox_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS68 : 68 ≤ S)
    (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (hKyberLen : ∀ kp, kyberOpt = some kp → kp.length ≤ bs.length) :
    PhaseCreditSpec M (PksmPostBoundedEnv bs kyberOpt innerG)
      (4 * min bs.length S + 19078 + sigTryFromDeltaCum innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG + sigTryFromDeltaPeak innerG)
      (max 68 (max bs.length (sigTryFromMaxReq innerG))) := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  have hKyberErr : PhaseCreditSpec M (SeqEnv PksmKyberErrAllocEnv FreeOnlyEvs) 9675 0 0 68 :=
    ((phaseCreditSpec_pksmKyberErrAlloc_S hM hSm hS68).seq hFree).mono
      (by decide) (by decide) (by decide) (by decide)
  have hKyberOk := phaseCreditSpec_intoBoxedOptBounded_S hM hSm hKyberLen
  have hSig := sigTryFrom_phaseCredit hM hLow innerG
  have hClone := phaseCreditSpec_tryCloneBytes_S_le hM hSm (Nat.le_refl bs.length)
  have hSeg4 : PhaseCreditSpec M (PksmPostSeg4Env bs)
      (2 * min bs.length S + 9539) (bs.length + 8195) (bs.length + 8195) bs.length :=
    (hFree.or (hClone.seq hFree)).mono
      freeOrSeqFree_cum freeOrSeqFree_live (freeOrSeqFree_peak (Nat.le_refl _)) freeOrSeqFree_req
  have hAfterKyber : PhaseCreditSpec M (PksmAfterKyberOkEnv bs innerG)
      (2 * min bs.length S + 9539 + sigTryFromDeltaCum innerG)
      (bs.length + 8195 + sigTryFromDeltaLive innerG)
      (bs.length + 8195 + sigTryFromDeltaLive innerG + sigTryFromDeltaPeak innerG)
      (max bs.length (sigTryFromMaxReq innerG)) :=
    (hFree.or (hSig.seq (hSeg4.seq hFree))).mono
      pksmAfterKyber_cum pksmAfterKyber_live pksmAfterKyber_peak pksmAfterKyber_req
  have hOkBranch := hFree.seq (hKyberOk.seq hAfterKyber)
  exact ((hFree.or (hKyberErr.or hOkBranch)).of_imp (fun _ h => h)).mono
    (pksmPost_cum (by decide) (by decide))
    (pksmPost_live (by decide))
    (pksmPost_peak (by decide))
    pksmPost_req

/-- Composes all post-loop phases of `PreKeySignalMessage::try_from` in exact binary call order,
treating `WireMsgPeakSpec.sigTryFrom_phaseCredit` as an opaque black box. -/
theorem phaseCreditSpec_pksmPost_blackbox {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost)
    (hKyberLen : ∀ kp, kyberOpt = some kp → kp.length ≤ bs.length) :
    PhaseCreditSpec M (PksmPostBoundedEnv bs kyberOpt innerG)
      (4 * min bs.length 135167 + 19078 + sigTryFromDeltaCum innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG)
      (2 * bs.length + 16390 + sigTryFromDeltaLive innerG + sigTryFromDeltaPeak innerG)
      (max 68 (max bs.length (sigTryFromMaxReq innerG))) :=
  phaseCreditSpec_pksmPost_blackbox_S hM hLow hLow.hSmallMaxEq (by decide) bs kyberOpt innerG hKyberLen

private theorem pksm_join_cum {A B SC c₁ c₂ c : Nat} (hc : c₁ + c₂ ≤ c) :
    max 0 ((A + c₁) + (B + c₂ + SC)) ≤ A + B + c + SC := by
  omega

private theorem pksm_join_live {N c₁ c₂ c SL : Nat} (hc : c₁ + c₂ ≤ c) :
    max 0 ((2 * N + c₁ + 0) + (2 * N + c₂ + SL)) ≤ 4 * N + c + SL := by
  omega

private theorem pksm_join_peak {N c₀ c₁ c₂ c SL SP : Nat}
    (hc0 : c₀ ≤ c) (hc12 : c₁ + c₂ ≤ c) :
    max 0 (max (max (3 * N + c₀) (2 * N + c₁ + 0))
      ((2 * N + c₁ + 0) + (2 * N + c₂ + SL + SP))) ≤
    4 * N + c + SL + SP := by
  omega

private theorem pksm_join_req {N SR : Nat} :
    max 0 (max (max 128 (max 128 (2 * N))) (max 68 (max N SR))) ≤
    max (max 128 (2 * N)) SR := by
  omega

/-- Parametric black-box composition of any 4-field `ProtoLoop4StateInvTight`-backed protobuf decode
loop (`tc = 29273, tl = 0, tp = 0, tr = 128`) followed in exact call order by
`PksmPostBoundedEnv`. -/
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
      (max (max 128 (2 * N)) (sigTryFromMaxReq innerG)) := by
  dsimp only
  have hLoopSpec := ProtoLoop4StateInvS.to_phaseCreditSpec hLoop
  have hPostSpec := phaseCreditSpec_pksmPost_blackbox hM hLow x.bytes kyberOpt innerG hKyberLen
  have hNil := PhaseCreditSpec.nil M
  exact ((hNil.or (hLoopSpec.seq hPostSpec)).of_imp hEnv).mono
    (pksm_join_cum (by decide))
    (pksm_join_live (by decide))
    (pksm_join_peak (by decide) (by decide))
    pksm_join_req

/-- Black-box `PhaseCreditSpec` for `PksmTryFromBoundedEnv x`. -/
theorem pksmTryFrom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PksmGhost) :
    PhaseCreditSpec M (PksmTryFromBoundedEnv x)
      (pksmTryFromDeltaCum x)
      (pksmTryFromDeltaLive x)
      (pksmTryFromDeltaPeak x)
      (pksmTryFromMaxReq x) := by
  have hLoopSpec :=
    phaseCreditSpec_protoLoop4_S hM hLow hLow.hSmallMaxEq (by decide) x.bytes.length
      (phaseCreditSpec_pksmLoopTail_S hM hLow.hSmallMaxEq (by decide))
  have hPostSpec :=
    phaseCreditSpec_pksmPost_blackbox hM hLow x.bytes
      (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)
      (pksmDecodedKyberOpt_length_le x.bytes)
  have hNil := PhaseCreditSpec.nil M
  unfold pksmTryFromDeltaCum pksmTryFromDeltaLive pksmTryFromDeltaPeak pksmTryFromMaxReq
  exact ((hNil.or (hLoopSpec.seq hPostSpec)).of_imp (fun _ h => h)).mono
    (pksm_join_cum (by decide))
    (pksm_join_live (by decide))
    (pksm_join_peak (by decide) (by decide))
    pksm_join_req

/-! ## Canonical `ResponderWire.PreKeyTryFromBaseBudget` `PhaseCreditSpec` (`PreKeyTryFromArgs`) -/

private theorem mergeBytes_encodeVarint_vlen_le (val : BitVec 64) (tail v rest : List (BitVec 8))
    (h : mergeBytes .lengthDelimited (encodeVarint val ++ tail) = some (v, rest)) :
    v.length ≤ val.toNat := by
  simp only [mergeBytes, decodeVarint_encodeVarint] at h
  split_ifs at h
  injection h with h'
  obtain ⟨rfl, _⟩ := Prod.mk.inj h'
  rw [List.length_take]
  omega

/-- Legacy `ModelHyps`-only `PhaseCreditSpec` for a `valCap = 0` `bytesMergeEventsCore` call. -/
theorem phaseCreditSpec_bytesMergeZeroCap_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wt : WireType) (bs : List (BitVec 8)) (L : Nat)
    (hLen : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ L) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt 0#64 bs)
      (6 * L + 19094) (2 * L + 8267) (3 * L + 16398) (max 72 (2 * L)) := by
  unfold bytesMergeEventsCore
  rcases hm : mergeBytes wt bs with _ | ⟨v, rest⟩
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 8) (by decide)).mono
      (by omega) (by omega) (by omega) (by omega)
  · dsimp only
    have hvL : v.length ≤ L := hLen v rest hm
    by_cases hZ : v.length = 0
    · simp only [hZ, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    · simp only [hZ, ↓reduceIte]
      have hPos : 0 < v.length := by omega
      refine { req_align := ?_, credit_le := ?_ }
      · rintro _ rfl ev hMem
        rcases List.mem_append.mp hMem with hMem12 | hMem3
        · rcases List.mem_append.mp hMem12 with hMem1 | hMem2
          · unfold rustAllocEvents at hMem1
            split at hMem1 <;> rw [List.mem_singleton] at hMem1 <;> subst hMem1 <;>
              simp only [eventStepReq, eventStepAlign] <;> omega
          · obtain ⟨hReq, hAl⟩ := req_align_doReserveClearEvents hPos hMem2
            exact ⟨by omega, hAl⟩
        · unfold rustDeallocEvents at hMem3
          rw [List.mem_singleton] at hMem3
          subst hMem3
          simp only [eventStepReq, eventStepAlign]
          omega
      · rintro st0 _ rfl
        have hLive0 :
            HasFineReallocCredit.liveLarge st0 ≤
              HasFineReallocCredit.liveLarge st0 + vecLargeCredit M 0 := by
          simp
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_bytesMergeOk_cancel M st0 (len := v.length) hLive0
        simp only [hZ, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
          vecLargeCredit_zero, Nat.add_zero] at hCum hLv hPk ⊢
        have hRcMax : reserveCap 0 0 v.length ≤ max (2 * v.length) 8 :=
          reserveCap_zero_le_max hPos
        have hVecL :
            vecLargeCredit M (if v.length ≤ 0 then 0 else reserveCap 0 0 v.length) ≤
              2 * L + 8267 := by
          have hNotLe0 : ¬ v.length ≤ 0 := by omega
          simp only [hNotLe0, ↓reduceIte]
          have hAff := vecLargeCredit_le_aff hM (reserveCap 0 0 v.length)
          omega
        have hSmBound : bytesMergeOkSmallDelta M 0 v.length ≤ 6 * L + 19094 := by
          unfold bytesMergeOkSmallDelta reserveClearSmallDelta
          have hNotLe0 : ¬ v.length ≤ 0 := by omega
          simp only [hZ, hNotLe0, ↓reduceIte]
          have hTmp :
              (if v.length ≤ HasFineReallocCredit.smallMaxReq M then
                HasFineReallocCredit.smallAllocCost M v.length
              else HasFineReallocCredit.largeMetaCost M) ≤ 2 * v.length + 9539 := by
            split_ifs with hSm
            · exact hM.smallAlloc_le hSm
            · have hm := hM.meta_le; omega
          have hRes :
              (if reserveCap 0 0 v.length ≤ HasFineReallocCredit.smallMaxReq M then
                HasFineReallocCredit.smallAllocCost M (reserveCap 0 0 v.length)
              else HasFineReallocCredit.largeMetaCost M) ≤
                2 * reserveCap 0 0 v.length + 9539 := by
            split_ifs with hSm
            · exact hM.smallAlloc_le hSm
            · have hm := hM.meta_le; omega
          omega
        have hPkBound : bytesMergeOkPeakDelta M 0 v.length ≤ 3 * L + 16398 := by
          unfold bytesMergeOkPeakDelta reserveClearLargeDelta
          have hNotLe0 : ¬ v.length ≤ 0 := by omega
          simp only [hZ, hNotLe0, ↓reduceIte]
          have hTmpL :
              (if v.length ≤ HasFineReallocCredit.smallMaxReq M then 0
              else HasFineReallocCredit.largeCost M v.length) ≤ v.length + 8195 := by
            split_ifs with hSm
            · omega
            · exact hM.largeCost_le (by omega)
          have hResL :
              (if reserveCap 0 0 v.length ≤ HasFineReallocCredit.smallMaxReq M then 0
              else HasFineReallocCredit.largeCost M (reserveCap 0 0 v.length)) ≤
                reserveCap 0 0 v.length + 8195 := by
            split_ifs with hSm
            · omega
            · exact hM.largeCost_le (by omega)
          omega
        exact ⟨by omega, by omega, by omega⟩

private theorem add_two_bounded {a b A B c₀ c : Nat}
    (ha : a ≤ A + c₀) (hb : b ≤ B + c₀) (hc : c₀ + c₀ ≤ c) :
    a + b ≤ A + B + c := by
  omega

/-- Tight `S`-capped `PhaseCreditSpec` for a `valCap = 0` `bytesMergeEventsCore` call with
`v.length ≤ L`. -/
theorem phaseCreditSpec_bytesMergeZeroCap_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS72 : 72 ≤ S)
    (wt : WireType) (bs : List (BitVec 8)) (L : Nat)
    (hLen : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ L) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt 0#64 bs)
      (2 * min L S + 2 * min (max 8 (2 * L)) S + 19078)
      (2 * L + 8195)
      (3 * L + 16390)
      (max 72 (2 * L)) := by
  have hS8 : 8 ≤ S := by omega
  unfold bytesMergeEventsCore
  rcases hm : mergeBytes wt bs with _ | ⟨v, rest⟩
  · have h72Sm : 72 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have h72 := (PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 8) (by decide) (by decide) h72Sm).mono
      (hM.smallAlloc_le h72Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
    exact h72.mono
      (Nat.le_trans (by decide : 2 * 72 + 9539 ≤ 19078) (Nat.le_add_left _ _))
      (Nat.zero_le _) (Nat.zero_le _) (Nat.le_max_left 72 _)
  · dsimp only
    have hvL : v.length ≤ L := hLen v rest hm
    by_cases hZ : v.length = 0
    · simp only [hZ, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [hZ, ↓reduceIte]
      have hPos : 0 < v.length := by omega
      refine { req_align := ?_, credit_le := ?_ }
      · rintro _ rfl ev hMem
        rcases List.mem_append.mp hMem with hMem12 | hMem3
        · rcases List.mem_append.mp hMem12 with hMem1 | hMem2
          · unfold rustAllocEvents at hMem1
            split at hMem1 <;> rw [List.mem_singleton] at hMem1 <;> subst hMem1 <;>
              simp only [eventStepReq, eventStepAlign] <;> omega
          · obtain ⟨hReq, hAl⟩ := req_align_doReserveClearEvents hPos hMem2
            exact ⟨by omega, hAl⟩
        · unfold rustDeallocEvents at hMem3
          rw [List.mem_singleton] at hMem3
          subst hMem3
          simp only [eventStepReq, eventStepAlign]
          omega
      · rintro st0 _ rfl
        have hLive0 :
            HasFineReallocCredit.liveLarge st0 ≤
              HasFineReallocCredit.liveLarge st0 + vecLargeCredit M 0 := by
          simp
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_bytesMergeOk_cancel M st0 (len := v.length) hLive0
        simp only [hZ, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
          vecLargeCredit_zero, Nat.add_zero] at hCum hLv hPk ⊢
        have hRcMax : reserveCap 0 0 v.length ≤ max (2 * L) 8 :=
          Nat.le_trans (reserveCap_zero_le_max hPos) (by omega)
        have hNotLe0 : ¬ v.length ≤ 0 := by omega
        have hVecL :
            vecLargeCredit M (if v.length ≤ 0 then 0 else reserveCap 0 0 v.length) ≤
              2 * L + 8195 := by
          simp only [hNotLe0, ↓reduceIte, vecLargeCredit_eq_bytesLargeLive]
          exact bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 hRcMax
        have hSmBound :
            bytesMergeOkSmallDelta M 0 v.length ≤
              2 * min L S + 2 * min (max 8 (2 * L)) S + 19078 := by
          unfold bytesMergeOkSmallDelta reserveClearSmallDelta
          simp only [hZ, hNotLe0, ↓reduceIte]
          have hTmp :
              (if v.length ≤ HasFineReallocCredit.smallMaxReq M then
                HasFineReallocCredit.smallAllocCost M v.length
              else HasFineReallocCredit.largeMetaCost M) ≤ 2 * min L S + 9539 := by
            split_ifs with hSmV
            · exact Nat.le_trans (hM.smallAlloc_le hSmV)
                (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_min.mpr ⟨hvL, by omega⟩)) 9539)
            · exact Nat.le_trans hM.meta_le
                (Nat.le_trans (by decide : 122 ≤ 9539) (Nat.le_add_left 9539 _))
          have hRes :
              (if reserveCap 0 0 v.length ≤ HasFineReallocCredit.smallMaxReq M then
                HasFineReallocCredit.smallAllocCost M (reserveCap 0 0 v.length)
              else HasFineReallocCredit.largeMetaCost M) ≤
                2 * min (max 8 (2 * L)) S + 9539 := by
            split_ifs with hSmR
            · have hRcLe : reserveCap 0 0 v.length ≤ min (max 8 (2 * L)) S := by omega
              exact Nat.le_trans (hM.smallAlloc_le hSmR)
                (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hRcLe) 9539)
            · exact Nat.le_trans hM.meta_le
                (Nat.le_trans (by decide : 122 ≤ 9539) (Nat.le_add_left 9539 _))
          exact add_two_bounded hTmp hRes (by decide)
        have hPkBound : bytesMergeOkPeakDelta M 0 v.length ≤ 3 * L + 16390 := by
          unfold bytesMergeOkPeakDelta reserveClearLargeDelta
          simp only [hZ, hNotLe0, ↓reduceIte]
          have hTmpL :
              (if v.length ≤ HasFineReallocCredit.smallMaxReq M then 0
              else HasFineReallocCredit.largeCost M v.length) ≤ L + 8195 := by
            split_ifs with hSmV
            · exact Nat.zero_le _
            · exact Nat.le_trans (hM.largeCost_le (by omega)) (Nat.add_le_add_right hvL 8195)
          have hResL :
              (if reserveCap 0 0 v.length ≤ HasFineReallocCredit.smallMaxReq M then 0
              else HasFineReallocCredit.largeCost M (reserveCap 0 0 v.length)) ≤
                2 * L + 8195 := by
            have hEq := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 hRcMax
            unfold bytesLargeLive at hEq
            exact hEq
          have hSum := add_two_bounded hTmpL hResL (by decide : 8195 + 8195 ≤ 16390)
          exact Nat.le_trans hSum (Nat.add_le_add_right (by omega : L + 2 * L ≤ 3 * L) 16390)
        exact ⟨Nat.le_trans hCum (Nat.add_le_add_left hSmBound _),
          Nat.le_trans hLv (Nat.add_le_add_left hVecL _),
          Nat.le_trans hPk (max_le_max (Nat.le_refl _) (Nat.add_le_add_left hPkBound _))⟩

/-- Small-field specialization (`max 72 (max 8 (2 * L)) ≤ S`) of `bytesMergeEventsCore wt 0#64 bs`:
zero `liveLarge` and `peakLarge` delta. -/
theorem phaseCreditSpec_bytesMergeZeroCap_small_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (wt : WireType) (bs : List (BitVec 8)) (L : Nat)
    (hSmallL : max 72 (max 8 (2 * L)) ≤ S)
    (hLen : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ L) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt 0#64 bs)
      (2 * L + 2 * max 8 (2 * L) + 19078) 0 0 (max 72 (2 * L)) := by
  unfold bytesMergeEventsCore
  rcases hm : mergeBytes wt bs with _ | ⟨v, rest⟩
  · have h72Sm : 72 ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have h72 := (PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 8) (by decide) (by decide) h72Sm).mono
      (hM.smallAlloc_le h72Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
    exact h72.mono
      (Nat.le_trans (by decide : 2 * 72 + 9539 ≤ 19078) (Nat.le_add_left _ _))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_max_left 72 _)
  · dsimp only
    have hvL : v.length ≤ L := hLen v rest hm
    by_cases hZ : v.length = 0
    · simp only [hZ, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · simp only [hZ, ↓reduceIte]
      have hPos : 0 < v.length := by omega
      refine { req_align := ?_, credit_le := ?_ }
      · rintro _ rfl ev hMem
        rcases List.mem_append.mp hMem with hMem12 | hMem3
        · rcases List.mem_append.mp hMem12 with hMem1 | hMem2
          · unfold rustAllocEvents at hMem1
            split at hMem1 <;> rw [List.mem_singleton] at hMem1 <;> subst hMem1 <;>
              simp only [eventStepReq, eventStepAlign] <;> omega
          · obtain ⟨hReq, hAl⟩ := req_align_doReserveClearEvents hPos hMem2
            exact ⟨by omega, hAl⟩
        · unfold rustDeallocEvents at hMem3
          rw [List.mem_singleton] at hMem3
          subst hMem3
          simp only [eventStepReq, eventStepAlign]
          omega
      · rintro st0 _ rfl
        have hLive0 :
            HasFineReallocCredit.liveLarge st0 ≤
              HasFineReallocCredit.liveLarge st0 + vecLargeCredit M 0 := by
          simp
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_bytesMergeOk_cancel M st0 (len := v.length) hLive0
        simp only [hZ, ↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mod,
          vecLargeCredit_zero, Nat.add_zero] at hCum hLv hPk ⊢
        have hRcMax : reserveCap 0 0 v.length ≤ max 8 (2 * L) :=
          Nat.le_trans (reserveCap_zero_le_max hPos) (by omega)
        have hvSm : v.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have hRcSm : reserveCap 0 0 v.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
        have hNotLe0 : ¬ v.length ≤ 0 := by omega
        have hVecL : vecLargeCredit M (if v.length ≤ 0 then 0 else reserveCap 0 0 v.length) = 0 := by
          simp only [hNotLe0, ↓reduceIte, vecLargeCredit, hRcSm]
        have hPk0 : bytesMergeOkPeakDelta M 0 v.length = 0 := by
          simp only [bytesMergeOkPeakDelta, reserveClearLargeDelta, hZ, hNotLe0, hvSm, hRcSm,
            ↓reduceIte]
        have hSmBound : bytesMergeOkSmallDelta M 0 v.length ≤ 2 * L + 2 * max 8 (2 * L) + 19078 := by
          unfold bytesMergeOkSmallDelta reserveClearSmallDelta
          simp only [hZ, hNotLe0, hvSm, hRcSm, ↓reduceIte]
          have ha1 : HasFineReallocCredit.smallAllocCost M v.length ≤ 2 * L + 9539 :=
            Nat.le_trans (hM.smallAlloc_le hvSm) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hvL) 9539)
          have ha2 :
              HasFineReallocCredit.smallAllocCost M (reserveCap 0 0 v.length) ≤
                2 * max 8 (2 * L) + 9539 :=
            Nat.le_trans (hM.smallAlloc_le hRcSm)
              (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hRcMax) 9539)
          exact add_two_bounded ha1 ha2 (by decide)
        rw [hVecL, Nat.add_zero] at hLv
        rw [hPk0, Nat.add_zero] at hPk
        exact ⟨Nat.le_trans hCum (Nat.add_le_add_left hSmBound _), hLv, hPk⟩

private theorem preKeyLoop_join_cum {A B c₁ c₂ c₃ c₄ c : Nat} (hc : c₁ + c₂ + c₃ + c₄ ≤ c) :
    ((c₁ + c₂) + (2 * A + 2 * B + c₃)) + c₄ ≤ 2 * A + 2 * B + c := by
  omega

private theorem preKeyLoop_join_live {L c₀ : Nat} :
    ((0 + 0) + (L + c₀)) + 0 ≤ L + c₀ := by
  omega

private theorem preKeyLoop_join_peak {L P c₀ c₁ : Nat} (hLP : L + c₀ ≤ P + c₁) :
    max (max (max 0 (0 + 0)) ((0 + 0) + (P + c₁))) (((0 + 0) + (L + c₀)) + 0) ≤ P + c₁ := by
  omega

private theorem preKeyLoop_join_req {IL : Nat} :
    max (max (max 72 72) (max 72 (2 * IL))) 3138 ≤ max 3138 (2 * IL) := by
  omega

private theorem phaseCreditSpec_preKeyLoop_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS : 3138 ≤ S)
    (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyLoopEnv x)
      (2 * min x.inner.length S + 2 * min (max 8 (2 * x.inner.length)) S + 86170)
      (2 * x.inner.length + 8195)
      (3 * x.inner.length + 16390)
      (max 3138 (2 * x.inner.length)) := by
  have h1 := (phaseCreditSpec_bytesMergeZeroCap_small_S hM hSm .lengthDelimited
    (encodeVarint 33#64 ++ x.bkBytes ++ psmRem2 x) 33 (by omega) fun v rest hm => by
      rw [List.append_assoc] at hm
      exact mergeBytes_encodeVarint_vlen_le 33#64 _ v rest hm).mono
    (by decide : 2 * 33 + 2 * max 8 (2 * 33) + 19078 ≤ 19292)
    (Nat.le_refl 0) (Nat.le_refl 0) (by decide : max 72 (2 * 33) ≤ 72)
  have h2 := (phaseCreditSpec_bytesMergeZeroCap_small_S hM hSm .lengthDelimited
    (encodeVarint 33#64 ++ x.ikBytes ++ psmRem3 x) 33 (by omega) fun v rest hm => by
      rw [List.append_assoc] at hm
      exact mergeBytes_encodeVarint_vlen_le 33#64 _ v rest hm).mono
    (by decide : 2 * 33 + 2 * max 8 (2 * 33) + 19078 ≤ 19292)
    (Nat.le_refl 0) (Nat.le_refl 0) (by decide : max 72 (2 * 33) ≤ 72)
  have h3 := phaseCreditSpec_bytesMergeZeroCap_S hM hSm (by omega) .lengthDelimited
    (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner ++ psmRem4 x)
    x.inner.length fun v rest hm => by
      rw [List.append_assoc] at hm
      have hv := mergeBytes_encodeVarint_vlen_le (BitVec.ofNat 64 x.inner.length) _ v rest hm
      rw [BitVec.toNat_ofNat] at hv
      exact Nat.le_trans hv (Nat.mod_le _ _)
  have h4 := (phaseCreditSpec_bytesMergeZeroCap_small_S hM hSm .lengthDelimited
    (encodeVarint 1569#64 ++ x.kyberBytes ++ psmRem8 x) 1569 (by omega) fun v rest hm => by
      rw [List.append_assoc] at hm
      exact mergeBytes_encodeVarint_vlen_le 1569#64 _ v rest hm).mono
    (by decide : 2 * 1569 + 2 * max 8 (2 * 1569) + 19078 ≤ 28508)
    (Nat.le_refl 0) (Nat.le_refl 0) (by decide : max 72 (2 * 1569) ≤ 3138)
  refine ((((h1.seq h2).seq h3).seq h4).of_imp (fun evs hE => ?_)).mono
    (preKeyLoop_join_cum (by decide))
    preKeyLoop_join_live
    (preKeyLoop_join_peak (Nat.add_le_add (by omega) (by decide)))
    preKeyLoop_join_req
  rw [hE]
  unfold preKeyLoopEvents
  exact Or.inr ⟨_, _, rfl, Or.inr ⟨_, _, rfl, Or.inr ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩

/-- Tight `PhaseCreditSpec` for `PreKeyTryFromBaseBudget.PreKeyLoopEnv x`. -/
theorem phaseCreditSpec_preKeyLoop {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyLoopEnv x)
      (2 * min x.inner.length 135167 + 2 * min (max 8 (2 * x.inner.length)) 135167 + 86170)
      (2 * x.inner.length + 8195)
      (3 * x.inner.length + 16390)
      (max 3138 (2 * x.inner.length)) :=
  phaseCreditSpec_preKeyLoop_S hM hLow.hSmallMaxEq (by decide) x

/-- Tight `PhaseCreditSpec` for `PreKeyTryFromBaseBudget.PreKeySeg2Env x` (Kyber `1569` B
`into_boxed_slice` is in the small regime `≤ 135167`, so `Δlive = 0, Δpeak = 0`). -/
theorem phaseCreditSpec_preKeySeg2 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeySeg2Env x) 12677 0 0 1569 :=
  (phaseCreditSpec_intoBoxedSmall_S hM hLow.hSmallMaxEq 1569 (by decide) (PreKeySeg2Env x) fun _ hE => by
    obtain ⟨cap, _, _, rfl⟩ := hE
    exact Or.inr ⟨x.kyberBytes, cap, by simp [PreKeyTryFromArgs.kyberBytes], rfl⟩).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem phaseCreditSpec_preKeySeg4_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeySeg4Env x)
      (2 * min x.bytes.length S + 9539)
      (x.bytes.length + 8195)
      (x.bytes.length + 8195)
      x.bytes.length := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  have hClone :=
    phaseCreditSpec_tryCloneBounded_S hM hSm x.bytes.length
      (TryCloneFromRefEnv ⟨x.ptr, x.bytes⟩) fun _ hE => Or.inr ⟨x.bytes, Nat.le_refl _, hE⟩
  exact ((hFree.or (hClone.seq hFree)).of_imp (fun _ h => h)).mono
    freeOrSeqFree_cum freeOrSeqFree_live (freeOrSeqFree_peak (Nat.le_refl _)) freeOrSeqFree_req

/-- Tight `PhaseCreditSpec` for `PreKeyTryFromBaseBudget.PreKeySeg4Env x`. -/
theorem phaseCreditSpec_preKeySeg4 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeySeg4Env x)
      (2 * min x.bytes.length 135167 + 9539)
      (x.bytes.length + 8195)
      (x.bytes.length + 8195)
      x.bytes.length :=
  phaseCreditSpec_preKeySeg4_S hM hLow.hSmallMaxEq x

private theorem preKeyPost_join_cum {B sc c₁ c₂ c : Nat} (hc : c₁ + c₂ ≤ c) :
    0 + (c₁ + (sc + (B + c₂))) ≤ B + c + sc := by
  omega

private theorem preKeyPost_join_live {BL c₀ sl : Nat} :
    0 + (0 + (sl + (BL + c₀))) ≤ BL + c₀ + sl := by
  omega

private theorem preKeyPost_join_peak {BL c₀ sl sp : Nat} :
    max 0 (0 + max 0 (0 + max sp (sl + (BL + c₀)))) ≤ BL + c₀ + sl + sp := by
  omega

private theorem preKeyPost_join_req {BL sr : Nat} :
    max 0 (max 1569 (max sr BL)) ≤ max (max 1569 BL) sr := by
  omega

private theorem preKeyFull_join_cum {A B C sc c₁ c₂ c : Nat} (hc : c₁ + c₂ ≤ c) :
    (A + B + c₁) + (C + c₂ + sc) ≤ A + B + C + c + sc := by
  omega

private theorem preKeyFull_join_live {IL BL c₀ c sl : Nat} (hc : c₀ + c₀ ≤ c) :
    (2 * IL + c₀) + (BL + c₀ + sl) ≤ 2 * IL + BL + c + sl := by
  omega

private theorem preKeyFull_join_peak {IL BL c₀ c sl sp : Nat} (hc : c₀ + c₀ ≤ c) :
    max (3 * IL + c) ((2 * IL + c₀) + (BL + c₀ + sl + sp)) ≤
      3 * IL + BL + c + sl + sp := by
  omega

private theorem preKeyFull_join_req {IL BL sr : Nat} :
    max (max 3138 (2 * IL)) (max (max 1569 BL) sr) ≤
      max (max 3138 (max (2 * IL) BL)) sr := by
  omega

/-- Parametric `PhaseCreditSpec` for `PreKeyTryFromBaseBudget.PreKeyTryFromEnv sigEnv x` given any
inner `SignalMessage::try_from` bound `hSig`. -/
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
      (max (max 3138 (max (2 * x.inner.length) x.bytes.length)) sr) := by
  have hLoop := phaseCreditSpec_preKeyLoop hM hLow x
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  have hSeg2 := phaseCreditSpec_preKeySeg2 hM hLow x
  have hSeg4 := phaseCreditSpec_preKeySeg4 hM hLow x
  have hPost : PhaseCreditSpec M (PreKeyPostEnv sigEnv x)
      (2 * min x.bytes.length 135167 + 22216 + sc)
      (x.bytes.length + 8195 + sl)
      (x.bytes.length + 8195 + sl + sp)
      (max (max 1569 x.bytes.length) sr) :=
    (hFree.seq (hSeg2.seq (hSig.seq hSeg4))).mono
      (preKeyPost_join_cum (by decide))
      preKeyPost_join_live
      preKeyPost_join_peak
      preKeyPost_join_req
  exact (hLoop.seq hPost).mono
    (preKeyFull_join_cum (by decide))
    (preKeyFull_join_live (by decide))
    (preKeyFull_join_peak (by decide))
    preKeyFull_join_req

/-- Black-box `PhaseCreditSpec` for `PreKeyTryFromEnv` specialized to
`WireMsgPeakSpec.SigTryFromBoundedEnv`. -/
theorem preKeyTryFrom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyTryFromEnv (fun bs => SigTryFromBoundedEnv ⟨0#64, bs, 0#64⟩) x)
      (2 * min x.inner.length 135167 + 2 * min (max 8 (2 * x.inner.length)) 135167 +
        2 * min x.bytes.length 135167 + 108386 + sigTryFromDeltaCum ⟨0#64, x.inner, 0#64⟩)
      (2 * x.inner.length + x.bytes.length + 16390 + sigTryFromDeltaLive ⟨0#64, x.inner, 0#64⟩)
      (3 * x.inner.length + x.bytes.length + 16390 +
        sigTryFromDeltaLive ⟨0#64, x.inner, 0#64⟩ + sigTryFromDeltaPeak ⟨0#64, x.inner, 0#64⟩)
      (max (max 3138 (max (2 * x.inner.length) x.bytes.length))
        (sigTryFromMaxReq ⟨0#64, x.inner, 0#64⟩)) :=
  preKeyTryFrom_phaseCredit_of_sig hM hLow x
    (sigTryFrom_phaseCredit hM hLow ⟨0#64, x.inner, 0#64⟩)

/-! ## Small-Allocation Group Bounds (`PhaseGroupSpec`) -/

theorem phaseGroupSpec_intoBoxed {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (IntoBoxedBoundedEnv bs) 140011 :=
  phaseGroupSpec_intoBoxedSlice hGrp bs

theorem phaseGroupSpec_intoBoxedOpt {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (opt : Option (List (BitVec 8))) :
    PhaseGroupSpec M (IntoBoxedOptBoundedEnv opt) 140011 := by
  cases opt with
  | none => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 140011)
  | some bs => exact phaseGroupSpec_intoBoxedSlice hGrp bs

theorem phaseGroupSpec_tryClone {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (TryCloneBytesEnv bs) 140011 :=
  phaseGroupSpec_tryCloneBytes hGrp bs

theorem phaseGroupSpec_sigTryFromErrTail {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M SigTryFromErrTailEnv 183475 :=
  phaseGroupSpec_errTail1 hGrp SigTryFromErrTailEnv fun _ hE => by
    have hNilFree : FreeOnlyEvs [] := FreeOnlyAlign16Evs.nil.toFreeOnlyEvs
    cases hE with
    | nil => exact ⟨[], [], rfl, hNilFree, Or.inl rfl⟩
    | fromOnly => exact ⟨rustAllocEvents 72 8, [], by simp, hNilFree, Or.inr (Or.inl rfl)⟩
    | @fromPush evs_p hp =>
      refine ⟨rustAllocEvents 72 8 ++ evs_p, [], by simp, hNilFree, Or.inr (Or.inr ⟨evs_p, rfl, ?_⟩)⟩
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega

theorem phaseGroupSpec_pksmLoopTail {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M PksmLoopTailBoundedEnv 323486 :=
  phaseGroupSpec_errTail2 hGrp PksmLoopTailBoundedEnv fun evs hE => by
    cases hE with
    | freeOnly hf =>
      exact ⟨[], [], [], evs, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, hf⟩
    | @err1 evs_p evs_free hp hf =>
      have hp0 : evs_p = [] ∨ evs_p = rustAllocEvents 128 8 := by
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      exact ⟨rustAllocEvents 72 8, evs_p, [], evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0, Or.inl rfl, hf⟩
    | @err2 evs_p0 evs_p1 evs_free hp0 hp1 hf =>
      have hp0' : evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8 := by
        rcases hp0 with rfl | ⟨_, rfl⟩ | ⟨hPos, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      have hp1' : evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8 := by
        rcases hp1 with rfl | ⟨hZ, _⟩ | ⟨_, rfl⟩
        · exact Or.inl rfl
        · omega
        · exact Or.inr rfl
      exact ⟨rustAllocEvents 72 8, evs_p0, evs_p1, evs_free, by simp [List.append_assoc],
        Or.inr rfl, hp0', hp1', hf⟩

theorem phaseGroupSpec_pksmKyberErrAlloc {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M PksmKyberErrAllocEnv 43464 := by
  have h68 := phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 68 ≤ 108) (by decide : 1 ≤ 16)
  have h54 := phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 54 ≤ 108) (by decide : 1 ≤ 16)
  exact ((h68.or h54).of_imp (fun _ h => h)).mono (by decide : max 43464 43464 ≤ 43464)

/-- Closed-form `FineScale`-scaled group delta for `PksmTryFromLoopBoundedEnv N ProtoCaps4.zero`:
`2369 * N` (`copy_to_bytes` across `sc = 0..47` and `mmap`) + `560044 * wireRemGrows N 0`
(`4 * 140011` `Vec<u8>` `reserveCap` doublings) + `323486` (`43464 + 2 * 140011` 2-push decode
error tail). -/
def pksmTryFromLoopDeltaGrpS (N : Nat) : Nat :=
  2369 * N + 560044 * wireRemGrows N 0 + 323486

/-- Closed-form `FineScale`-scaled group cap for `PksmTryFromBoundedEnv x` when `x.bytes.length ≤ N`
(`= 4,990,641,776` = `76,152` groups at `N = 1,048,576`). -/
def pksmTryFromCapDeltaGrpS (N : Nat) : Nat :=
  2369 * N + 560044 * wireRemGrows N 0 + 603508 + sigTryFromCapDeltaGrpS N

/-- Exact-ghost `FineScale`-scaled group delta for `PksmTryFromBoundedEnv x`. -/
def pksmTryFromDeltaGrpS (x : PksmGhost) : Nat :=
  2369 * x.bytes.length + 560044 * wireRemGrows x.bytes.length 0 + 603508 +
    sigTryFromDeltaGrpS (pksmInnerGhost x)

theorem pksmTryFromLoopDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    pksmTryFromLoopDeltaGrpS N₁ ≤ pksmTryFromLoopDeltaGrpS N₂ :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 2369 h)
      (Nat.mul_le_mul_left 560044 (wireRemGrows_mono 0 h)))
    (Nat.le_refl 323486)

theorem pksmTryFromCapDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    pksmTryFromCapDeltaGrpS N₁ ≤ pksmTryFromCapDeltaGrpS N₂ :=
  Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 2369 h)
        (Nat.mul_le_mul_left 560044 (wireRemGrows_mono 0 h)))
      (Nat.le_refl 603508))
    (sigTryFromCapDeltaGrpS_mono h)

theorem pksmTryFromDeltaGrpS_le_cap {x : PksmGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    pksmTryFromDeltaGrpS x ≤ pksmTryFromCapDeltaGrpS N := by
  have hInner : (pksmInnerGhost x).bytes.length ≤ N :=
    Nat.le_trans (pksmDecodedInnerBytes_length_le x.bytes) h
  unfold pksmTryFromDeltaGrpS pksmTryFromCapDeltaGrpS
  refine Nat.add_le_add ?_ (sigTryFromDeltaGrpS_le_cap hInner)
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 2369 h)
      (Nat.mul_le_mul_left 560044 (wireRemGrows_mono 0 h)))
    (Nat.le_refl 603508)

/-- Loop-level `PhaseGroupSpec` for `PksmTryFromLoopBoundedEnv N ProtoCaps4.zero`. -/
theorem pksmTryFromLoop_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (N : Nat) :
    PhaseGroupSpec M (PksmTryFromLoopBoundedEnv N ProtoCaps4.zero)
      (pksmTryFromLoopDeltaGrpS N) :=
  phaseGroupSpec_protoLoop4 hGrp N (phaseGroupSpec_pksmLoopTail hGrp)

private theorem pksmAfterKyber_grp {A SG : Nat} :
    max 0 (SG + (A + 0)) ≤ A + SG := by
  omega

private theorem pksmPost_grp {kErr k₀ k SG : Nat}
    (hErr : kErr + 0 ≤ k) (h2 : k₀ + k₀ ≤ k) :
    max 0 (max (kErr + 0) (0 + (k₀ + (k₀ + SG)))) ≤ k + SG := by
  omega

/-- Black-box `PhaseGroupSpec` for `PksmPostBoundedEnv bs kyberOpt innerG`, treating
`sigTryFrom_phaseGroup` as an opaque black box. -/
theorem phaseGroupSpec_pksmPost_blackbox {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8))
    (kyberOpt : Option (List (BitVec 8))) (innerG : TryFromGhost) :
    PhaseGroupSpec M (PksmPostBoundedEnv bs kyberOpt innerG)
      (280022 + sigTryFromDeltaGrpS innerG) := by
  have hFree : PhaseGroupSpec M FreeOnlyEvs 0 := PhaseGroupSpec.freeOnly M
  have hKyberErr : PhaseGroupSpec M (SeqEnv PksmKyberErrAllocEnv FreeOnlyEvs) (43464 + 0) :=
    (phaseGroupSpec_pksmKyberErrAlloc hGrp).seq hFree
  have hKyberOk := phaseGroupSpec_intoBoxedOpt hGrp kyberOpt
  have hSig := sigTryFrom_phaseGroup hGrp innerG
  have hClone := phaseGroupSpec_tryClone hGrp bs
  have hSeg4 : PhaseGroupSpec M (PksmPostSeg4Env bs) 140011 :=
    ((hFree.or (hClone.seq hFree)).of_imp (fun _ h => h)).mono
      (by decide : max 0 (140011 + 0) ≤ 140011)
  have hAfterKyber : PhaseGroupSpec M (PksmAfterKyberOkEnv bs innerG)
      (140011 + sigTryFromDeltaGrpS innerG) :=
    ((hFree.or (hSig.seq (hSeg4.seq hFree))).of_imp (fun _ h => h)).mono pksmAfterKyber_grp
  have hOkBranch := hFree.seq (hKyberOk.seq hAfterKyber)
  exact ((hFree.or (hKyberErr.or hOkBranch)).of_imp (fun _ h => h)).mono
    (pksmPost_grp (by decide) (by decide))

private theorem pksm_join_grp {A t₁ t₂ t SG : Nat} (ht : t₁ + t₂ ≤ t) :
    max 0 ((A + t₁) + (t₂ + SG)) ≤ A + t + SG := by
  omega

/-- Parametric black-box `PhaseGroupSpec` composition of any `ProtoLoop4GroupInv`-backed decode loop
followed by `PksmPostBoundedEnv`. -/
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
      (2369 * N + 560044 * wireRemGrows N 0 + 603508 + sigTryFromDeltaGrpS innerG) := by
  dsimp only
  have hLoopSpec := ProtoLoop4GroupInv.to_phaseGroupSpec hLoop
  have hPostSpec := phaseGroupSpec_pksmPost_blackbox hGrp x.bytes kyberOpt innerG
  have hNil := PhaseGroupSpec.nil M
  exact ((hNil.or (hLoopSpec.seq hPostSpec)).of_imp hEnv).mono
    (pksm_join_grp (by decide))

/-- Black-box `PhaseGroupSpec` for `PksmTryFromBoundedEnv x`. -/
theorem pksmTryFrom_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PksmGhost) :
    PhaseGroupSpec M (PksmTryFromBoundedEnv x) (pksmTryFromDeltaGrpS x) := by
  have hLoopSpec := pksmTryFromLoop_phaseGroup hGrp x.bytes.length
  unfold pksmTryFromLoopDeltaGrpS at hLoopSpec
  have hPostSpec :=
    phaseGroupSpec_pksmPost_blackbox hGrp x.bytes
      (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)
  have hNil := PhaseGroupSpec.nil M
  unfold pksmTryFromDeltaGrpS
  exact ((hNil.or (hLoopSpec.seq hPostSpec)).of_imp (fun _ h => h)).mono
    (pksm_join_grp (by decide))

/-- Closed-form `FineScale`-scaled group cap for `PreKeyTryFromBoundedEnv x` when
`x.inner.length ≤ M_cap` (`= 2,496,720,998` = `38,097` groups at `M_cap = 1,048,576`). -/
def preKeyTryFromCapDeltaGrpS (M_cap _B_cap : Nat) : Nat :=
  1400110 + sigTryFromCapDeltaGrpS M_cap

/-- Exact-ghost `FineScale`-scaled group delta for `PreKeyTryFromBoundedEnv x`. -/
def preKeyTryFromDeltaGrpS (x : PreKeyTryFromArgs) : Nat :=
  1400110 + sigTryFromDeltaGrpS ⟨0#64, x.inner, 0#64⟩

theorem preKeyTryFromDeltaGrpS_le_cap {x : PreKeyTryFromArgs} {M_cap B_cap : Nat}
    (hM : x.inner.length ≤ M_cap) (_hB : x.bytes.length ≤ B_cap) :
    preKeyTryFromDeltaGrpS x ≤ preKeyTryFromCapDeltaGrpS M_cap B_cap :=
  Nat.add_le_add (Nat.le_refl 1400110) (sigTryFromDeltaGrpS_le_cap hM)

private theorem pg_append {M : AllocCostModel} [HasFineGroupCredit M]
    {xs ys : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = xs) g₁) (h₂ : PhaseGroupSpec M (· = ys) g₂) :
    PhaseGroupSpec M (· = xs ++ ys) (g₁ + g₂) where
  groups_le st0 {_} h := by
    subst h
    rw [AllocCostModel.stepEvents_append]
    have b1 := h₁.groups_le st0 rfl
    have b2 := h₂.groups_le (M.stepEvents xs st0) rfl
    omega

/-- `PhaseGroupSpec` for `PreKeyTryFromBaseBudget.PreKeyLoopEnv x` (`4 * 280022 = 1120088`). -/
theorem phaseGroupSpec_preKeyLoop {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeyLoopEnv x) 1120088 := by
  have h1 := phaseGroupSpec_bytesMergeZeroCap hGrp .lengthDelimited
    (encodeVarint 33#64 ++ x.bkBytes ++ psmRem2 x)
  have h2 := phaseGroupSpec_bytesMergeZeroCap hGrp .lengthDelimited
    (encodeVarint 33#64 ++ x.ikBytes ++ psmRem3 x)
  have h3 := phaseGroupSpec_bytesMergeZeroCap hGrp .lengthDelimited
    (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner ++ psmRem4 x)
  have h4 := phaseGroupSpec_bytesMergeZeroCap hGrp .lengthDelimited
    (encodeVarint 1569#64 ++ x.kyberBytes ++ psmRem8 x)
  exact (pg_append (pg_append (pg_append h1 h2) h3) h4).mono
    (by decide : (((280022 + 280022) + 280022) + 280022) ≤ 1120088)

/-- `PhaseGroupSpec` for `PreKeyTryFromBaseBudget.PreKeySeg2Env x`. -/
theorem phaseGroupSpec_preKeySeg2 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeySeg2Env x) 140011 :=
  phaseGroupSpec_intoBoxedBounded hGrp (PreKeySeg2Env x) fun _ hE => by
    obtain ⟨cap, _, _, rfl⟩ := hE
    exact Or.inr ⟨x.kyberBytes, cap, rfl⟩

/-- `PhaseGroupSpec` for `PreKeyTryFromBaseBudget.PreKeySeg4Env x`. -/
theorem phaseGroupSpec_preKeySeg4 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeySeg4Env x) 140011 := by
  have hFree : PhaseGroupSpec M FreeOnlyEvs 0 := PhaseGroupSpec.freeOnly M
  have hClone :=
    phaseGroupSpec_tryCloneBounded hGrp (TryCloneFromRefEnv ⟨x.ptr, x.bytes⟩)
      fun _ hE => Or.inr ⟨x.bytes, hE⟩
  exact ((hFree.or (hClone.seq hFree)).of_imp (fun _ h => h)).mono
    (by decide : max 0 (140011 + 0) ≤ 140011)

private theorem preKeyPost_join_grp {g₀ g sg : Nat} (hg : g₀ + g₀ ≤ g) :
    0 + (g₀ + (sg + g₀)) ≤ g + sg := by
  omega

private theorem preKeyFull_join_grp {g₁ g₂ g sg : Nat} (hg : g₁ + g₂ ≤ g) :
    g₁ + (g₂ + sg) ≤ g + sg := by
  omega

/-- Parametric `PhaseGroupSpec` for `PreKeyTryFromBaseBudget.PreKeyTryFromEnv sigEnv x` given any
inner `SignalMessage::try_from` group bound `hSig`. -/
theorem preKeyTryFrom_phaseGroup_of_sig {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M)
    {sigEnv : List (BitVec 8) → List AllocEvent → Prop}
    (x : PreKeyTryFromArgs) {sg : Nat}
    (hSig : PhaseGroupSpec M (sigEnv x.inner) sg) :
    PhaseGroupSpec M (PreKeyTryFromEnv sigEnv x) (1400110 + sg) := by
  have hLoop := phaseGroupSpec_preKeyLoop hGrp x
  have hFree : PhaseGroupSpec M FreeOnlyEvs 0 := PhaseGroupSpec.freeOnly M
  have hSeg2 := phaseGroupSpec_preKeySeg2 hGrp x
  have hSeg4 := phaseGroupSpec_preKeySeg4 hGrp x
  have hPost : PhaseGroupSpec M (PreKeyPostEnv sigEnv x) (280022 + sg) :=
    (hFree.seq (hSeg2.seq (hSig.seq hSeg4))).mono (preKeyPost_join_grp (by decide))
  exact (hLoop.seq hPost).mono (preKeyFull_join_grp (by decide))

/-- Black-box `PhaseGroupSpec` for `PreKeyTryFromEnv` specialized to
`WireMsgPeakSpec.SigTryFromBoundedEnv`. -/
theorem preKeyTryFrom_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeyTryFromEnv (fun bs => SigTryFromBoundedEnv ⟨0#64, bs, 0#64⟩) x)
      (preKeyTryFromDeltaGrpS x) :=
  preKeyTryFrom_phaseGroup_of_sig hGrp x (sigTryFrom_phaseGroup hGrp ⟨0#64, x.inner, 0#64⟩)

end LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
