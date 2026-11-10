/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFromPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
import LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers

/-!
# Peak Live-Heap & Group Specs for Wire `SignalMessage` & `PreKeySignalMessage`

Allocator event envelopes, `PhaseCreditSpec` bounds, and `PhaseGroupSpec` bounds for
`<SignalMessage>::new`, `<PreKeySignalMessage>::new`, and `<SignalMessage as TryFrom<&[u8]>>::try_from`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec

open CryptoGames.LibsignalSession (SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification.LibsignalProtoCodec (WireType encode mergeBytes protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
  (bytesCumAlloc_le_aff bytesLargeLive bytesLargeLive_le_aff bytesLargeLive_zero
   phaseCredit_signalMessageNew req_align_of_rustAllocEvents req_align_of_rustDeallocEvents
   stepEvents_kyberCopyEvs stepEvents_kyberDeallocEvs stepEvents_rustAlloc_aff
   stepEvents_rustDealloc_any)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireLowInterceptHyps bytesLargeLive_le_two_mul_of_le_max
   bytesMergeEventsCore_groups_step bytesMergeEventsCore_step_tight
   errTail_nil_or_from_or_push_tight
   fineCostModel_wireLowInterceptHyps phaseCredit_intoBoxedSlice_S phaseCredit_tryCloneBytes_S
   phaseGroupSpec_intoBoxedSlice phaseGroupSpec_optBytesAlloc phaseGroupSpec_optBytesDealloc
   phaseGroupSpec_rustAlloc_cap phaseGroupSpec_rustAlloc_le44 phaseGroupSpec_rustAlloc_le108
   phaseGroupSpec_tryCloneBytes tryFrom_ok_field_lengths
   wireGrowsFrom wireRemGrows wireRemGrows_mono)
export LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireLowInterceptHyps fineCostModel_wireLowInterceptHyps wireGrowsFrom wireRemGrows
   wireRemGrows_mono)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (kyberDeallocEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost signalMessageNewEvents)

abbrev WireGroupHyps (M : AllocCostModel) [HasFineGroupCredit M] : Prop :=
  LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers.WireGroupHyps M

theorem fineCostModel_wireGroupHyps :
    WireGroupHyps LibsignalBinary.Heap.Fine.fineCostModel :=
  LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers.fineCostModel_wireGroupHyps

/-! ## 1. `<SignalMessage>::new` (`SignalMessageNewEnv`) -/

def signalMessageNewSerLen (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  (encode (x.protoMsg parse)).length + 9

def signalMessageNewDeltaCum (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  4 * x.ciphertext.length + 4 * x.pqRatchet.length + 2 * signalMessageNewSerLen parse x + 86121

def signalMessageNewDeltaLive (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  x.ciphertext.length + x.pqRatchet.length + signalMessageNewSerLen parse x + 32816

def signalMessageNewDeltaPeak (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  2 * x.ciphertext.length + 2 * x.pqRatchet.length + signalMessageNewSerLen parse x + 65662

def signalMessageNewMaxReq (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  max (max 36 x.ciphertext.length) (max x.pqRatchet.length (signalMessageNewSerLen parse x))

theorem signalMessageNew_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (parse : UuidParser) (x : SignalMessageNewGhost) :
    PhaseCreditSpec M (SignalMessageNewEnv parse x)
      (signalMessageNewDeltaCum parse x)
      (signalMessageNewDeltaLive parse x)
      (signalMessageNewDeltaPeak parse x)
      (signalMessageNewMaxReq parse x) := by
  unfold signalMessageNewDeltaCum signalMessageNewDeltaLive
    signalMessageNewDeltaPeak signalMessageNewMaxReq signalMessageNewSerLen
  exact phaseCredit_signalMessageNew hM parse x

/-! ## 2. `<PreKeySignalMessage>::new` (`PreKeyMsgNewEnv`) -/

def kyberCopyEvs (kp : Option KyberPayload) : List AllocEvent :=
  match kp with
  | none => []
  | some k =>
    if k.ciphertext = [] then []
    else rustAllocEvents k.ciphertext.length 1

def kyberPayloadLen : Option KyberPayload → Nat
  | none => 0
  | some k => k.ciphertext.length

def preKeyMsgNewRawPrologueEvents (kp : Option KyberPayload) (smLen outLen : Nat) :
    List AllocEvent :=
  kyberCopyEvs kp ++
    (rustAllocEvents 33 1 ++ rustAllocEvents 33 1) ++
    rustAllocEvents smLen 1 ++
    rustAllocEvents outLen 1

def preKeyMsgNewRawEvents (kp : Option KyberPayload) (smLen outLen : Nat) : List AllocEvent :=
  preKeyMsgNewRawPrologueEvents kp smLen outLen ++
    kyberDeallocEvs kp ++
    (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    rustDeallocEvents smLen 1

def PreKeyMsgNewRawEnv (kp : Option KyberPayload) (smLen outLen : Nat)
    (evs : List AllocEvent) : Prop :=
  evs = preKeyMsgNewRawEvents kp smLen outLen

def preKeyMsgNewEvents (x : PreKeyMsgNewCall) : List AllocEvent :=
  preKeyMsgNewRawEvents x.kp x.msg.serialized.length x.model.serialized.length

def PreKeyMsgNewEnv (x : PreKeyMsgNewCall) (evs : List AllocEvent) : Prop :=
  PreKeyMsgNewRawEnv x.kp x.msg.serialized.length x.model.serialized.length evs

def preKeyMsgNewRawDeltaCum (kp : Option KyberPayload) (smLen outLen : Nat) : Nat :=
  2 * kyberPayloadLen kp + 2 * smLen + 2 * outLen + 47827

def preKeyMsgNewRawDeltaLive (outLen : Nat) : Nat :=
  outLen + 8195

def preKeyMsgNewRawDeltaPeak (kp : Option KyberPayload) (smLen outLen : Nat) : Nat :=
  kyberPayloadLen kp + smLen + outLen + 41041

def preKeyMsgNewRawMaxReq (kp : Option KyberPayload) (smLen outLen : Nat) : Nat :=
  max (max (kyberPayloadLen kp) 33) (max smLen outLen)

theorem preKeyMsgNewRaw_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (kp : Option KyberPayload) (smLen outLen : Nat) :
    PhaseCreditSpec M (PreKeyMsgNewRawEnv kp smLen outLen)
      (preKeyMsgNewRawDeltaCum kp smLen outLen)
      (preKeyMsgNewRawDeltaLive outLen)
      (preKeyMsgNewRawDeltaPeak kp smLen outLen)
      (preKeyMsgNewRawMaxReq kp smLen outLen) where
  req_align := by
    rintro evs rfl ev hev
    unfold preKeyMsgNewRawEvents preKeyMsgNewRawPrologueEvents at hev
    simp only [List.mem_append] at hev
    have hky : kyberPayloadLen kp ≤ preKeyMsgNewRawMaxReq kp smLen outLen := by
      unfold preKeyMsgNewRawMaxReq; omega
    have h33 : 33 ≤ preKeyMsgNewRawMaxReq kp smLen outLen := by
      unfold preKeyMsgNewRawMaxReq; omega
    have hsm : smLen ≤ preKeyMsgNewRawMaxReq kp smLen outLen := by
      unfold preKeyMsgNewRawMaxReq; omega
    have hout : outLen ≤ preKeyMsgNewRawMaxReq kp smLen outLen := by
      unfold preKeyMsgNewRawMaxReq; omega
    rcases hev with ((((((h1 | (h2 | h3)) | h4) | h5) | h6) | (h7 | h8)) | h9)
    · cases hkp : kp with
      | none => simp [hkp, kyberCopyEvs] at h1
      | some k =>
        simp only [hkp, kyberCopyEvs] at h1
        simp only [hkp, kyberPayloadLen] at hky
        split at h1
        · cases h1
        · exact req_align_of_rustAllocEvents (al := 1) hky (by decide) ev h1
    · exact req_align_of_rustAllocEvents (al := 1) h33 (by decide) ev h2
    · exact req_align_of_rustAllocEvents (al := 1) h33 (by decide) ev h3
    · exact req_align_of_rustAllocEvents (al := 1) hsm (by decide) ev h4
    · exact req_align_of_rustAllocEvents (al := 1) hout (by decide) ev h5
    · cases hkp : kp with
      | none => simp [hkp, kyberDeallocEvs] at h6
      | some k =>
        simp only [hkp, kyberDeallocEvs] at h6
        split at h6
        · cases h6
        · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h6
    · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h7
    · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h8
    · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h9
  credit_le := by
    rintro st0 evs rfl
    have hky_eq : kyberCopyEvs kp = WireSignalHelpers.kyberCopyEvs kp := by
      cases kp <;> rfl
    have hlen_eq : kyberPayloadLen kp = WireSignalHelpers.kyberPayloadLen kp := by
      cases kp <;> rfl
    unfold preKeyMsgNewRawEvents preKeyMsgNewRawPrologueEvents
      preKeyMsgNewRawDeltaCum preKeyMsgNewRawDeltaLive preKeyMsgNewRawDeltaPeak
    rw [hky_eq, hlen_eq]
    simp only [AllocCostModel.stepEvents_append]
    have h1 := stepEvents_kyberCopyEvs M kp st0
    set s1 := M.stepEvents (WireSignalHelpers.kyberCopyEvs kp) st0
    have h2 := stepEvents_rustAlloc_aff hM 33 1 (by decide) s1
    set s2 := M.stepEvents (rustAllocEvents 33 1) s1
    have h3 := stepEvents_rustAlloc_aff hM 33 1 (by decide) s2
    set s3 := M.stepEvents (rustAllocEvents 33 1) s2
    have h4 := stepEvents_rustAlloc_aff hM smLen 1 (by decide) s3
    set s4 := M.stepEvents (rustAllocEvents smLen 1) s3
    have h5 := stepEvents_rustAlloc_aff hM outLen 1 (by decide) s4
    set s5 := M.stepEvents (rustAllocEvents outLen 1) s4
    have h6 := stepEvents_kyberDeallocEvs M kp s5
    set s6 := M.stepEvents (kyberDeallocEvs kp) s5
    have h7 := stepEvents_rustDealloc_any M 33 1 (by decide) s6
    set s7 := M.stepEvents (rustDeallocEvents 33 1) s6
    have h8 := stepEvents_rustDealloc_any M 33 1 (by decide) s7
    set s8 := M.stepEvents (rustDeallocEvents 33 1) s7
    have h9 := stepEvents_rustDealloc_any M smLen 1 (by decide) s8
    have hc_ky := bytesCumAlloc_le_aff hM (WireSignalHelpers.kyberPayloadLen kp)
    have hl_ky := bytesLargeLive_le_aff hM (WireSignalHelpers.kyberPayloadLen kp)
    have hl_33 := bytesLargeLive_le_aff hM 33
    have hl_sm := bytesLargeLive_le_aff hM smLen
    have hl_out := bytesLargeLive_le_aff hM outLen
    exact ⟨by omega, by omega, by omega⟩

abbrev preKeyMsgNewDeltaCum (x : PreKeyMsgNewCall) : Nat :=
  preKeyMsgNewRawDeltaCum x.kp x.msg.serialized.length x.model.serialized.length

abbrev preKeyMsgNewDeltaLive (x : PreKeyMsgNewCall) : Nat :=
  preKeyMsgNewRawDeltaLive x.model.serialized.length

abbrev preKeyMsgNewDeltaPeak (x : PreKeyMsgNewCall) : Nat :=
  preKeyMsgNewRawDeltaPeak x.kp x.msg.serialized.length x.model.serialized.length

abbrev preKeyMsgNewMaxReq (x : PreKeyMsgNewCall) : Nat :=
  preKeyMsgNewRawMaxReq x.kp x.msg.serialized.length x.model.serialized.length

theorem preKeyMsgNew_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : PreKeyMsgNewCall) :
    PhaseCreditSpec M (PreKeyMsgNewEnv x)
      (preKeyMsgNewDeltaCum x)
      (preKeyMsgNewDeltaLive x)
      (preKeyMsgNewDeltaPeak x)
      (preKeyMsgNewMaxReq x) :=
  preKeyMsgNewRaw_phaseCredit hM x.kp x.msg.serialized.length x.model.serialized.length

/-! ## 3. `<SignalMessage as TryFrom<&[u8]>>::try_from` (`SigTryFromBoundedEnv`) -/

/-- Bounded `<DecodeError>::push` envelope matching `SpqrV1.Alloc.newCap32` (`max (2 * n) 4`). -/
def DecodeErrorPushBoundedEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents 128 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

inductive SigTryFromField where
  | rk | ct | pq | ad

structure SigTryFromCaps where
  rk : Nat
  ct : Nat
  pq : Nat
  ad : Nat

def SigTryFromCaps.zero : SigTryFromCaps := ⟨0, 0, 0, 0⟩

def SigTryFromCaps.get (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => c.rk | .ct => c.ct | .pq => c.pq | .ad => c.ad

def SigTryFromCaps.set (c : SigTryFromCaps) : SigTryFromField → Nat → SigTryFromCaps
  | .rk, v => { c with rk := v }
  | .ct, v => { c with ct := v }
  | .pq, v => { c with pq := v }
  | .ad, v => { c with ad := v }

inductive SigTryFromErrTailEnv : List AllocEvent → Prop where
  | nil : SigTryFromErrTailEnv []
  | fromOnly : SigTryFromErrTailEnv (rustAllocEvents 72 8)
  | fromPush {evs_p : List AllocEvent} :
      DecodeErrorPushBoundedEnv 0 evs_p →
      SigTryFromErrTailEnv (rustAllocEvents 72 8 ++ evs_p)

/-- Slice-budgeted protobuf decode loop envelope for `SignalMessage::try_from`:
indexed by remaining input byte count `rem` and the 4 `ProtoSignalMessage` `Vec<u8>` field
capacities `(rk, ct, pq, ad)`. -/
inductive SigTryFromLoopBoundedEnv : Nat → SigTryFromCaps → List AllocEvent → Prop where
  | done {rem : Nat} {caps : SigTryFromCaps} {evs : List AllocEvent} :
      SigTryFromErrTailEnv evs →
      SigTryFromLoopBoundedEnv rem caps evs
  | skipStep {rem rem' : Nat} {caps : SigTryFromCaps} {evs : List AllocEvent} :
      rem' < rem →
      SigTryFromLoopBoundedEnv rem' caps evs →
      SigTryFromLoopBoundedEnv rem caps evs
  | bytesStep (f : SigTryFromField) {rem rem' : Nat} {caps : SigTryFromCaps}
      (wt : WireType) (bs v rest : List (BitVec 8)) {evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ rem →
      rem' + v.length + 1 ≤ rem →
      caps.get f < 2 ^ 63 →
      SigTryFromLoopBoundedEnv rem'
        (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
        evs₂ →
      SigTryFromLoopBoundedEnv rem caps
        (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂)

def intoBoxedCapEvents (cap : BitVec 64) (bs : List (BitVec 8)) : List AllocEvent :=
  if cap.toNat ≤ bs.length then []
  else if bs = [] then rustDeallocEvents cap.toNat 1
  else rustReallocEvents cap.toNat bs.length 1

def IntoBoxedBoundedEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ evs = intoBoxedCapEvents cap bs

def IntoBoxedOptBoundedEnv : Option (List (BitVec 8)) → List AllocEvent → Prop
  | none => (· = [])
  | some ad => IntoBoxedBoundedEnv ad

def TryCloneBytesEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = if bs = [] then [] else rustAllocEvents bs.length 1

def SigTryFromPostOkAllocEnv (bs ct : List (BitVec 8))
    (adOpt : Option (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (IntoBoxedBoundedEnv ct) (SeqEnv (IntoBoxedOptBoundedEnv adOpt) (TryCloneBytesEnv bs))

def SigTryFromPostOutPreEnv : Except SignalProtocolError SignalMessage → List AllocEvent → Prop
  | .error _ => (· = [])
  | .ok msg =>
    SeqEnv FreeOnlyEvs (SigTryFromPostOkAllocEnv msg.serialized msg.ciphertext msg.addresses)

def SigTryFromPostEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SigTryFromPostOutPreEnv (SignalMessage.tryFrom protoSignalCodec bs)) FreeOnlyEvs

/-- Full `<SignalMessage as TryFrom<&[u8]>>::try_from` envelope for `SigTryFromPlacedBudget`. -/
def SigTryFromBoundedEnv (x : TryFromGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  SeqEnv (SigTryFromLoopBoundedEnv x.bytes.length SigTryFromCaps.zero)
         (SigTryFromPostEnv x.bytes) evs

def sigTryFromCapDeltaCum (N : Nat) : Nat :=
  94 * N + 16 * min (max 8 (2 * N)) 135167 + 38156 * wireRemGrows N 0 + 6 * min N 135167 + 48095

def sigTryFromCapDeltaLive (N : Nat) : Nat :=
  5 * N + 57397

def sigTryFromCapDeltaPeak (N : Nat) : Nat :=
  5 * N + 57397

def sigTryFromCapMaxReq (N : Nat) : Nat :=
  max 128 (2 * N)

def sigTryFromDeltaCum (x : TryFromGhost) : Nat :=
  94 * x.bytes.length + 16 * min (max 8 (2 * x.bytes.length)) 135167 +
    38156 * wireRemGrows x.bytes.length 0 + 6 * min x.bytes.length 135167 + 48095

def sigTryFromDeltaLive (x : TryFromGhost) : Nat :=
  5 * x.bytes.length + 57397

def sigTryFromDeltaPeak (x : TryFromGhost) : Nat :=
  5 * x.bytes.length + 57397

def sigTryFromMaxReq (x : TryFromGhost) : Nat :=
  max 128 (2 * x.bytes.length)

private theorem min_right_mono {a b S : Nat} (h : a ≤ b) : min a S ≤ min b S := by
  omega

private theorem max8_two_mul_mono {a b : Nat} (h : a ≤ b) : max 8 (2 * a) ≤ max 8 (2 * b) := by
  omega

theorem sigTryFromCapDeltaCum_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromCapDeltaCum N₁ ≤ sigTryFromCapDeltaCum N₂ := by
  unfold sigTryFromCapDeltaCum
  refine Nat.add_le_add ?_ (Nat.le_refl 48095)
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left 6 (min_right_mono h))
  refine Nat.add_le_add ?_ (Nat.mul_le_mul_left 38156 (wireRemGrows_mono 0 h))
  exact Nat.add_le_add (Nat.mul_le_mul_left 94 h)
    (Nat.mul_le_mul_left 16 (min_right_mono (max8_two_mul_mono h)))

theorem sigTryFromCapDeltaLive_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromCapDeltaLive N₁ ≤ sigTryFromCapDeltaLive N₂ :=
  Nat.add_le_add (Nat.mul_le_mul_left 5 h) (Nat.le_refl 57397)

theorem sigTryFromCapDeltaPeak_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromCapDeltaPeak N₁ ≤ sigTryFromCapDeltaPeak N₂ :=
  Nat.add_le_add (Nat.mul_le_mul_left 5 h) (Nat.le_refl 57397)

theorem sigTryFromCapMaxReq_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromCapMaxReq N₁ ≤ sigTryFromCapMaxReq N₂ := by
  unfold sigTryFromCapMaxReq
  omega

theorem sigTryFromDeltaCum_le_cap {x : TryFromGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    sigTryFromDeltaCum x ≤ sigTryFromCapDeltaCum N :=
  sigTryFromCapDeltaCum_mono h

theorem sigTryFromDeltaLive_le_cap {x : TryFromGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    sigTryFromDeltaLive x ≤ sigTryFromCapDeltaLive N :=
  sigTryFromCapDeltaLive_mono h

theorem sigTryFromDeltaPeak_le_cap {x : TryFromGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    sigTryFromDeltaPeak x ≤ sigTryFromCapDeltaPeak N :=
  sigTryFromCapDeltaPeak_mono h

theorem sigTryFromMaxReq_le_cap {x : TryFromGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    sigTryFromMaxReq x ≤ sigTryFromCapMaxReq N :=
  sigTryFromCapMaxReq_mono h

private def capsLarge (M : AllocCostModel) [HasFineReallocCredit M] (c : SigTryFromCaps) : Nat :=
  bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.pq + bytesLargeLive M c.ad

private def capsOtherLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => bytesLargeLive M c.ct + bytesLargeLive M c.pq + bytesLargeLive M c.ad
  | .ct => bytesLargeLive M c.rk + bytesLargeLive M c.pq + bytesLargeLive M c.ad
  | .pq => bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.ad
  | .ad => bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.pq

private def capsSum (c : SigTryFromCaps) : Nat :=
  c.rk + c.ct + c.pq + c.ad

private def capsOtherSum (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => c.ct + c.pq + c.ad
  | .ct => c.rk + c.pq + c.ad
  | .pq => c.rk + c.ct + c.ad
  | .ad => c.rk + c.ct + c.pq

private def capsMinSum (S : Nat) (c : SigTryFromCaps) : Nat :=
  min c.rk S + min c.ct S + min c.pq S + min c.ad S

private def capsRemGrows (N : Nat) (c : SigTryFromCaps) : Nat :=
  wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.pq + wireRemGrows N c.ad

private def capsOtherRemGrows (N : Nat) (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => wireRemGrows N c.ct + wireRemGrows N c.pq + wireRemGrows N c.ad
  | .ct => wireRemGrows N c.rk + wireRemGrows N c.pq + wireRemGrows N c.ad
  | .pq => wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.ad
  | .ad => wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.pq

private def capsBounded (maxLen : Nat) (c : SigTryFromCaps) : Prop :=
  c.rk ≤ max 8 (2 * maxLen) ∧
  c.ct ≤ max 8 (2 * maxLen) ∧
  c.pq ≤ max 8 (2 * maxLen) ∧
  c.ad ≤ max 8 (2 * maxLen)

private def capsBoundedG (c g : SigTryFromCaps) : Prop :=
  c.rk ≤ max (2 * g.rk) 8 ∧
  c.ct ≤ max (2 * g.ct) 8 ∧
  c.pq ≤ max (2 * g.pq) 8 ∧
  c.ad ≤ max (2 * g.ad) 8

private theorem capsLarge_decomp (M : AllocCostModel) [HasFineReallocCredit M]
    (c : SigTryFromCaps) (f : SigTryFromField) (v : Nat) :
    capsLarge M c = capsOtherLarge M c f + bytesLargeLive M (c.get f) ∧
    capsLarge M (c.set f v) = capsOtherLarge M c f + bytesLargeLive M v := by
  cases f <;> dsimp only [capsLarge, capsOtherLarge, SigTryFromCaps.get, SigTryFromCaps.set] <;>
    exact ⟨by omega, by omega⟩

private theorem capsRemGrows_decomp (N : Nat) (c : SigTryFromCaps) (f : SigTryFromField) (v : Nat) :
    capsRemGrows N c = capsOtherRemGrows N c f + wireRemGrows N (c.get f) ∧
    capsRemGrows N (c.set f v) = capsOtherRemGrows N c f + wireRemGrows N v := by
  cases f <;> dsimp only [capsRemGrows, capsOtherRemGrows, SigTryFromCaps.get, SigTryFromCaps.set] <;>
    exact ⟨by omega, by omega⟩

private theorem capsG_props {c g : SigTryFromCaps} (hcg : capsBoundedG c g)
    (f : SigTryFromField) {v_cap v_g : Nat} (hv : v_cap ≤ max (2 * v_g) 8) :
    capsSum g = capsOtherSum g f + g.get f ∧
    capsSum (g.set f v_g) = capsOtherSum g f + v_g ∧
    c.get f ≤ max (2 * g.get f) 8 ∧
    capsBoundedG (c.set f v_cap) (g.set f v_g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  cases f <;>
    dsimp only [SigTryFromCaps.get, SigTryFromCaps.set, capsSum, capsOtherSum, capsBoundedG] <;>
    exact ⟨by omega, by omega, by omega, ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem capsMinSum_props {S maxLen : Nat} {c : SigTryFromCaps}
    (hc : capsBounded maxLen c) (f : SigTryFromField) {v : Nat}
    (hle : min (c.get f) S ≤ min v S) (hv : v ≤ max 8 (2 * maxLen)) :
    c.get f ≤ max 8 (2 * maxLen) ∧
    capsBounded maxLen (c.set f v) ∧
    capsMinSum S c ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    capsMinSum S (c.set f v) ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    capsMinSum S (c.set f v) + min (c.get f) S = capsMinSum S c + min v S := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  cases f <;>
    dsimp only [SigTryFromCaps.get, SigTryFromCaps.set, capsBounded, capsMinSum] at hle ⊢ <;>
    exact ⟨by omega, ⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

private theorem capsOtherLarge_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : SigTryFromCaps} (hcg : capsBoundedG c g) (f : SigTryFromField) :
    capsOtherLarge M c f ≤ 2 * capsOtherSum g f + 24585 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  cases f <;> simp only [capsOtherLarge, capsOtherSum] <;> omega

private theorem capsLarge_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : SigTryFromCaps} (hcg : capsBoundedG c g) :
    capsLarge M c ≤ 2 * capsSum g + 32780 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  unfold capsLarge capsSum
  omega

private theorem sigTryFromErrTail_cases {evs : List AllocEvent}
    (h : SigTryFromErrTailEnv evs) :
    evs = [] ∨ evs = rustAllocEvents 72 8 ∨
    evs = rustAllocEvents 72 8 ++ [] ∨
    evs = rustAllocEvents 72 8 ++ rustAllocEvents 128 8 := by
  cases h with
  | nil => exact Or.inl rfl
  | fromOnly => exact Or.inr (Or.inl rfl)
  | fromPush hp =>
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · omega

private theorem loop_step_credit_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S maxLen base rem : Nat}
    (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    {caps : SigTryFromCaps} {evs : List AllocEvent}
    (hloop : SigTryFromLoopBoundedEnv rem caps evs) :
    ∀ (st : M.σ) (g : SigTryFromCaps),
      rem ≤ maxLen →
      capsBounded maxLen caps →
      capsBoundedG caps g →
      capsSum g + rem ≤ maxLen →
      HasFineReallocCredit.liveLarge st ≤ base + capsLarge M caps →
      (∀ ev ∈ evs, eventStepReq ev ≤ max 128 (2 * maxLen) ∧ eventStepAlign ev ≤ 16) ∧
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (4 * min (max 8 (2 * maxLen)) S - capsMinSum S caps) +
          9539 * capsRemGrows maxLen caps + 19478 ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        base + (2 * maxLen + 32780) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) := by
  have hS8 : 8 ≤ S := by omega
  induction hloop with
  | @done rem caps evs herr =>
    intro st g _ _ hcg hg_rem hlive
    have hcl := capsLarge_le_g hM hSm hS8 hcg
    have hlive_bd : HasFineReallocCredit.liveLarge st ≤ base + (2 * maxLen + 32780) := by omega
    obtain ⟨hreq, hcum, hlv, hpk⟩ :=
      errTail_nil_or_from_or_push_tight hM (maxLen := maxLen) hSm hS128 st hlive_bd
        (sigTryFromErrTail_cases herr)
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set MS := capsMinSum S caps
    set GW := capsRemGrows maxLen caps
    have hcum' : HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (Mmax - MS) + 9539 * GW + 19478 :=
      Nat.le_trans hcum (by omega)
    have hpk' : HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) :=
      Nat.le_trans hpk (max_le_max (Nat.le_refl _) (by omega))
    exact ⟨hreq, hcum', hlv, hpk'⟩
  | @skipStep rem rem' caps evs hlt _ ih =>
    intro st g hrem hcaps hcg hg_rem hlive
    obtain ⟨hreq, hcum, hlv, hpk⟩ :=
      ih st g (by omega) hcaps hcg (by omega) hlive
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set MS := capsMinSum S caps
    set GW := capsRemGrows maxLen caps
    have hmono : 94 * rem' ≤ 94 * rem := Nat.mul_le_mul_left 94 (Nat.le_of_lt hlt)
    exact ⟨hreq, Nat.le_trans hcum (by omega), hlv, hpk⟩
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm _ hrem_step hcap63 _ ih =>
    intro st g hrem hcaps hcg hg_rem hlive
    have hcap64 : caps.get f < 2 ^ 64 := by omega
    have hcap_max : caps.get f ≤ max 8 (2 * maxLen) := by
      obtain ⟨h0, h1, h2, h3⟩ := hcaps
      cases f <;> simp only [SigTryFromCaps.get] <;> omega
    set cap := caps.get f
    set cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    set g_f := g.get f
    set g_f' := if v.length ≤ cap then g_f else v.length
    obtain ⟨hg_sum_pre, _, hcap_g_pre, _⟩ :=
      capsG_props hcg f (v_cap := cap) (v_g := g_f)
        (by obtain ⟨h0, h1, h2, h3⟩ := hcg; dsimp only [cap, g_f]; cases f <;> dsimp only [SigTryFromCaps.get] <;> omega)
    change capsSum g = capsOtherSum g f + g_f at hg_sum_pre
    change cap ≤ max (2 * g_f) 8 at hcap_g_pre
    obtain ⟨hdec_pre, hdec_post⟩ := capsLarge_decomp M caps f cap'
    change capsLarge M caps = capsOtherLarge M caps f + bytesLargeLive M cap at hdec_pre
    have hlive' : HasFineReallocCredit.liveLarge st ≤
        base + capsOtherLarge M caps f + bytesLargeLive M cap := by omega
    obtain ⟨hreq1, hmin_le, _, hcap'_max, hcap'_g, hg_rem', hcum1, hlive1, hpeak1⟩ :=
      bytesMergeEventsCore_step_tight hM hLow hSm hS8 hm hrem_step hrem hcap64 hcap_max
        hcap_g_pre (capsOtherLarge_le_g hM hSm hS8 hcg f) (by omega) st hlive'
    change min cap S ≤ min cap' S at hmin_le
    change cap' ≤ max 8 (2 * maxLen) at hcap'_max
    change cap' ≤ max (2 * g_f') 8 at hcap'_g
    change capsOtherSum g f + g_f' + rem' ≤ maxLen at hg_rem'
    obtain ⟨_, hcaps', _, hms'_le, hms_eq⟩ := capsMinSum_props hcaps f hmin_le hcap'_max
    obtain ⟨_, hg_sum_post, _, hcg'⟩ := capsG_props hcg f hcap'_g
    obtain ⟨hgw_pre, hgw_post⟩ := capsRemGrows_decomp maxLen caps f cap'
    rw [AllocCostModel.stepEvents_append]
    set evs₁ := bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs
    set st₁ := M.stepEvents evs₁ st
    change HasFineReallocCredit.liveLarge st₁ ≤
      base + capsOtherLarge M caps f + bytesLargeLive M cap' at hlive1
    change capsLarge M (caps.set f cap') =
      capsOtherLarge M caps f + bytesLargeLive M cap' at hdec_post
    have hlive1' : HasFineReallocCredit.liveLarge st₁ ≤
        base + capsLarge M (caps.set f cap') := by omega
    obtain ⟨hreq2, hcum2, hlv2, hpk2⟩ :=
      ih st₁ (g.set f g_f') (by omega) hcaps' hcg' (by omega) hlive1'
    set st₂ := M.stepEvents evs₂ st₁
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set W := wireRemGrows maxLen cap
    set W' := wireRemGrows maxLen cap'
    set GW_other := capsOtherRemGrows maxLen caps f
    set MS := capsMinSum S caps
    set MS' := capsMinSum S (caps.set f cap')
    set MC := min cap S
    set MC' := min cap' S
    change HasFineReallocCredit.cumSmall st₁ + 9539 * W' ≤
      HasFineReallocCredit.cumSmall st + 94 * (rem - rem') + 4 * (MC' - MC) + 9539 * W at hcum1
    change capsRemGrows maxLen caps = GW_other + W at hgw_pre
    change capsRemGrows maxLen (caps.set f cap') = GW_other + W' at hgw_post
    change MS' ≤ Mmax at hms'_le
    change MS' + MC = MS + MC' at hms_eq
    have hcum_comb : HasFineReallocCredit.cumSmall st₂ ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (Mmax - MS) + 9539 * capsRemGrows maxLen caps + 19478 := by
      have hrem_mul : 94 * (rem - rem') + 94 * rem' = 94 * rem := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      set R1 := 94 * (rem - rem')
      set R2 := 94 * rem'
      set R := 94 * rem
      rw [hgw_post] at hcum2
      rw [hgw_pre]
      omega
    have hpk_comb : HasFineReallocCredit.peakLarge st₂ ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) :=
      Nat.le_trans hpk2 (Nat.max_le.mpr ⟨hpeak1, Nat.le_max_right _ _⟩)
    refine ⟨?_, hcum_comb, hlv2, hpk_comb⟩
    intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · obtain ⟨hr, hal⟩ := hreq1 ev h1
      exact ⟨Nat.le_trans hr (by omega), hal⟩
    · exact hreq2 ev h2

private theorem phaseCredit_sigTryFromLoop_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    (N : Nat) :
    PhaseCreditSpec M (SigTryFromLoopBoundedEnv N SigTryFromCaps.zero)
      (94 * N + 16 * min (max 8 (2 * N)) S + 38156 * wireRemGrows N 0 + 19478)
      (2 * N + 32780) (3 * N + 49170) (max 128 (2 * N)) where
  req_align evs hloop := by
    have hzero_bd : capsBounded N SigTryFromCaps.zero := by
      simp [capsBounded, SigTryFromCaps.zero]
    have hzero_g : capsBoundedG SigTryFromCaps.zero SigTryFromCaps.zero := by
      simp [capsBoundedG, SigTryFromCaps.zero]
    have hzero_lg : capsLarge M SigTryFromCaps.zero = 0 := by
      simp [capsLarge, SigTryFromCaps.zero, bytesLargeLive_zero]
    have hzero_sum : capsSum SigTryFromCaps.zero = 0 := rfl
    exact (loop_step_credit_S hM hLow (maxLen := N) (base := HasFineReallocCredit.liveLarge M.init)
      hSm hS128 hloop M.init SigTryFromCaps.zero (Nat.le_refl N) hzero_bd hzero_g
      (by omega) (by omega)).1
  credit_le st0 {_} hloop := by
    have hzero_bd : capsBounded N SigTryFromCaps.zero := by
      simp [capsBounded, SigTryFromCaps.zero]
    have hzero_g : capsBoundedG SigTryFromCaps.zero SigTryFromCaps.zero := by
      simp [capsBoundedG, SigTryFromCaps.zero]
    have hzero_lg : capsLarge M SigTryFromCaps.zero = 0 := by
      simp [capsLarge, SigTryFromCaps.zero, bytesLargeLive_zero]
    have hzero_sum : capsSum SigTryFromCaps.zero = 0 := rfl
    have hzero_ms : capsMinSum S SigTryFromCaps.zero = 0 := by
      simp [capsMinSum, SigTryFromCaps.zero]
    have hzero_gw : capsRemGrows N SigTryFromCaps.zero = 4 * wireRemGrows N 0 := by
      simp only [capsRemGrows, SigTryFromCaps.zero]
      omega
    obtain ⟨_, hcum, hlv, hpk⟩ :=
      loop_step_credit_S hM hLow (maxLen := N) (base := HasFineReallocCredit.liveLarge st0)
        hSm hS128 hloop st0 SigTryFromCaps.zero (Nat.le_refl N) hzero_bd hzero_g
        (by omega) (by omega)
    rw [hzero_ms, Nat.sub_zero, hzero_gw] at hcum
    set A := min (max 8 (2 * N)) S
    set K := wireRemGrows N 0
    exact ⟨Nat.le_trans hcum (by omega), hlv, hpk⟩

private theorem phaseCredit_intoBoxedOpt_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (adOpt : Option (List (BitVec 8))) :
    PhaseCreditSpec M (IntoBoxedOptBoundedEnv adOpt)
      (2 * min (adOpt.getD []).length S + 9539)
      ((adOpt.getD []).length + 8195)
      ((adOpt.getD []).length + 8195)
      (adOpt.getD []).length := by
  cases adOpt with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (Nat.le_refl 0)
  | some ad =>
    exact phaseCredit_intoBoxedSlice_S hM hSm ad

private theorem phaseCredit_sigTryFromPost_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8)) :
    PhaseCreditSpec M (SigTryFromPostEnv bs)
      (6 * min bs.length S + 28617)
      (3 * bs.length + 24585) (3 * bs.length + 24585) bs.length := by
  unfold SigTryFromPostEnv
  have hf_tail := PhaseCreditSpec.freeOnly_of_hyps hM
  cases hout : SignalMessage.tryFrom protoSignalCodec bs with
  | error err =>
    have hpre : PhaseCreditSpec M (SigTryFromPostOutPreEnv (.error err)) 0 0 0 0 :=
      PhaseCreditSpec.nil M
    exact (hpre.seq hf_tail).mono (by omega) (by omega) (by omega) (by omega)
  | ok msg =>
    obtain ⟨hser, hct, had⟩ := tryFrom_ok_field_lengths hout
    have hbox_ct : PhaseCreditSpec M (IntoBoxedBoundedEnv msg.ciphertext)
        (2 * min msg.ciphertext.length S + 9539) (msg.ciphertext.length + 8195)
        (msg.ciphertext.length + 8195) msg.ciphertext.length :=
      phaseCredit_intoBoxedSlice_S hM hSm msg.ciphertext
    have hbox_ad := phaseCredit_intoBoxedOpt_S hM hSm msg.addresses
    have hclone : PhaseCreditSpec M (TryCloneBytesEnv msg.serialized)
        (2 * min msg.serialized.length S + 9539) (msg.serialized.length + 8195)
        (msg.serialized.length + 8195) msg.serialized.length :=
      phaseCredit_tryCloneBytes_S hM hSm msg.serialized
    have hok_alloc := hbox_ct.seq (hbox_ad.seq hclone)
    have hpre := (PhaseCreditSpec.freeOnly_of_hyps hM).seq hok_alloc
    exact (hpre.seq hf_tail).mono (by omega) (by omega) (by omega) (by omega)

private theorem sigTryFrom_join_cum {A B k₁ k₂ k : Nat} (hk : k₁ + k₂ ≤ k) :
    max 0 (((A + k₁) + (B + k₂))) ≤ A + B + k := by
  omega

private theorem sigTryFrom_join_live {N : Nat} :
    max 0 ((2 * N + 32780) + (3 * N + 24585)) ≤ 5 * N + 57397 := by
  omega

private theorem sigTryFrom_join_peak {N : Nat} :
    max 0 (max (3 * N + 49170) ((2 * N + 32780) + (3 * N + 24585))) ≤ 5 * N + 57397 := by
  omega

theorem sigTryFrom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : TryFromGhost) :
    PhaseCreditSpec M (SigTryFromBoundedEnv x)
      (sigTryFromDeltaCum x)
      (sigTryFromDeltaLive x)
      (sigTryFromDeltaPeak x)
      (sigTryFromMaxReq x) := by
  unfold SigTryFromBoundedEnv sigTryFromDeltaCum sigTryFromDeltaLive
    sigTryFromDeltaPeak sigTryFromMaxReq
  have hloop := phaseCredit_sigTryFromLoop_S hM hLow hLow.hSmallMaxEq (by decide) x.bytes.length
  have hpost := phaseCredit_sigTryFromPost_S hM hLow.hSmallMaxEq x.bytes
  have hseq := hloop.seq hpost
  exact ((PhaseCreditSpec.nil M).or hseq).mono
    (sigTryFrom_join_cum (by decide))
    sigTryFrom_join_live
    sigTryFrom_join_peak
    (by omega)

/-! ## Small-Allocation Group Bounds (`PhaseGroupSpec`) -/

/-- `FineScale`-scaled group delta for `<SignalMessage>::new` (`4 * 16659 + 5 * 140011 = 766,691`,
`≤ 12` groups). -/
def signalMessageNewDeltaGrpS : Nat := 766691

/-- `FineScale`-scaled group delta for `<PreKeySignalMessage>::new`
(`2 * 16659 + 3 * 140011 = 453,351`, `≤ 7` groups). -/
def preKeyMsgNewDeltaGrpS : Nat := 453351

/-- Closed-form `FineScale`-scaled group delta for `SigTryFromLoopBoundedEnv N SigTryFromCaps.zero`:
`2369 * N` for `copy_to_bytes` across `sc = 0..47` and `mmap`, `560044 * wireRemGrows N 0`
(`4 * 140011`) for the 4 `Vec<u8>` fields' `reserveCap` doublings, plus `183475` (`43464 + 140011`)
for the decode error tail. -/
def sigTryFromLoopDeltaGrpS (N : Nat) : Nat :=
  2369 * N + 560044 * wireRemGrows N 0 + 183475

/-- Closed-form `FineScale`-scaled group cap for `SigTryFromBoundedEnv x` when `x.bytes.length ≤ N`
(`= 2,495,320,888` = `38,076` groups at `N = 1,048,576`). -/
def sigTryFromCapDeltaGrpS (N : Nat) : Nat :=
  2369 * N + 560044 * wireRemGrows N 0 + 603508

/-- Exact-ghost `FineScale`-scaled group delta for `SigTryFromBoundedEnv x`. -/
def sigTryFromDeltaGrpS (x : TryFromGhost) : Nat :=
  2369 * x.bytes.length + 560044 * wireRemGrows x.bytes.length 0 + 603508

theorem sigTryFromLoopDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromLoopDeltaGrpS N₁ ≤ sigTryFromLoopDeltaGrpS N₂ :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 2369 h)
      (Nat.mul_le_mul_left 560044 (wireRemGrows_mono 0 h)))
    (Nat.le_refl 183475)

theorem sigTryFromCapDeltaGrpS_mono {N₁ N₂ : Nat} (h : N₁ ≤ N₂) :
    sigTryFromCapDeltaGrpS N₁ ≤ sigTryFromCapDeltaGrpS N₂ :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left 2369 h)
      (Nat.mul_le_mul_left 560044 (wireRemGrows_mono 0 h)))
    (Nat.le_refl 603508)

theorem sigTryFromDeltaGrpS_le_cap {x : TryFromGhost} {N : Nat} (h : x.bytes.length ≤ N) :
    sigTryFromDeltaGrpS x ≤ sigTryFromCapDeltaGrpS N :=
  sigTryFromCapDeltaGrpS_mono h

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

private theorem phaseGroup_computeMac {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) :
    PhaseGroupSpec M (· = computeMacEvents) 33318 := by
  have h33 : PhaseGroupSpec M (· = publicKeySerializeEvents) 16659 :=
    phaseGroupSpec_rustAlloc_le44 hGrp (by decide : 33 ≤ 44) (by decide : 1 ≤ 16)
  have hd33 := PhaseGroupSpec.rustDealloc M 33 1
  have hPair := pg_append h33 hd33
  exact (pg_append hPair hPair).mono (by decide : (16659 + 0) + (16659 + 0) ≤ 33318)

theorem signalMessageNew_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (parse : UuidParser) (x : SignalMessageNewGhost) :
    PhaseGroupSpec M (SignalMessageNewEnv parse x) signalMessageNewDeltaGrpS := by
  have h1 : PhaseGroupSpec M
      (· = if (x.addresses parse).isSome then rustAllocEvents 36 1 else []) 16659 := by
    cases (x.addresses parse).isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 16659)
    · simp only [↓reduceIte]
      exact phaseGroupSpec_rustAlloc_le44 hGrp (by decide : 36 ≤ 44) (by decide : 1 ≤ 16)
  have h2 : PhaseGroupSpec M (· = publicKeySerializeEvents) 16659 :=
    phaseGroupSpec_rustAlloc_le44 hGrp (by decide : 33 ≤ 44) (by decide : 1 ≤ 16)
  have h3 := phaseGroupSpec_optBytesAlloc hGrp x.ciphertext
  have h4 := phaseGroupSpec_optBytesAlloc hGrp x.pqRatchet
  have h5 := phaseGroupSpec_rustAlloc_cap hGrp ((encode (x.protoMsg parse)).length + 9)
    (by decide : 1 ≤ 16)
  have h6 := phaseGroup_computeMac hGrp
  have h7 := phaseGroupSpec_optBytesAlloc hGrp x.ciphertext
  have h8 := phaseGroupSpec_optBytesAlloc hGrp x.pqRatchet
  have h9 := PhaseGroupSpec.rustDealloc M 33 1
  have h10 := phaseGroupSpec_optBytesDealloc M x.ciphertext
  have h11 := phaseGroupSpec_optBytesDealloc M x.pqRatchet
  have hAll :=
    pg_append (pg_append (pg_append (pg_append (pg_append (pg_append (pg_append (pg_append
      (pg_append (pg_append h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  exact hAll.mono
    (by decide :
      ((((((((((16659 + 16659) + 140011) + 140011) + 140011) + 33318) + 140011) + 140011) +
        0) + 0) + 0) ≤
        signalMessageNewDeltaGrpS)

private theorem phaseGroup_kyberCopy {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (kp : Option KyberPayload) :
    PhaseGroupSpec M (· = kyberCopyEvs kp) 140011 := by
  cases kp with
  | none =>
    exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 140011)
  | some k =>
    dsimp only [kyberCopyEvs]
    exact phaseGroupSpec_tryCloneBytes hGrp k.ciphertext

private theorem phaseGroup_kyberDealloc (M : AllocCostModel) [HasFineGroupCredit M]
    (kp : Option KyberPayload) :
    PhaseGroupSpec M (· = kyberDeallocEvs kp) 0 := by
  cases kp with
  | none =>
    exact PhaseGroupSpec.nil M
  | some k =>
    dsimp only [kyberDeallocEvs]
    split
    · exact PhaseGroupSpec.nil M
    · exact PhaseGroupSpec.rustDealloc M k.ciphertext.length 1

theorem preKeyMsgNewRaw_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (kp : Option KyberPayload) (smLen outLen : Nat) :
    PhaseGroupSpec M (PreKeyMsgNewRawEnv kp smLen outLen) preKeyMsgNewDeltaGrpS := by
  have h1 := phaseGroup_kyberCopy hGrp kp
  have h2 := phaseGroupSpec_rustAlloc_le44 hGrp (by decide : 33 ≤ 44) (by decide : 1 ≤ 16)
  have h3 := phaseGroupSpec_rustAlloc_le44 hGrp (by decide : 33 ≤ 44) (by decide : 1 ≤ 16)
  have h4 := phaseGroupSpec_rustAlloc_cap hGrp smLen (by decide : 1 ≤ 16)
  have h5 := phaseGroupSpec_rustAlloc_cap hGrp outLen (by decide : 1 ≤ 16)
  have h6 := phaseGroup_kyberDealloc M kp
  have h7 := PhaseGroupSpec.rustDealloc M 33 1
  have h8 := PhaseGroupSpec.rustDealloc M 33 1
  have h9 := PhaseGroupSpec.rustDealloc M smLen 1
  have hPro : PhaseGroupSpec M (· = preKeyMsgNewRawPrologueEvents kp smLen outLen)
      ((((140011 + (16659 + 16659)) + 140011) + 140011)) :=
    pg_append (pg_append (pg_append h1 (pg_append h2 h3)) h4) h5
  have hAll := pg_append (pg_append (pg_append hPro h6) (pg_append h7 h8)) h9
  exact hAll.mono
    (by decide :
      (((((140011 + (16659 + 16659)) + 140011) + 140011) + 0) + (0 + 0)) + 0 ≤
        preKeyMsgNewDeltaGrpS)

theorem preKeyMsgNew_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyMsgNewCall) :
    PhaseGroupSpec M (PreKeyMsgNewEnv x) preKeyMsgNewDeltaGrpS :=
  preKeyMsgNewRaw_phaseGroup hGrp x.kp x.msg.serialized.length x.model.serialized.length

private theorem errTail_groups_le {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (st : M.σ) {evs : List AllocEvent}
    (herr : SigTryFromErrTailEnv evs) :
    HasFineGroupCredit.groupsScaled (M.stepEvents evs st) ≤
      HasFineGroupCredit.groupsScaled st + 183475 := by
  have h72 := phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 72 ≤ 108) (by decide : 8 ≤ 16)
  have h128 := phaseGroupSpec_rustAlloc_cap hGrp 128 (by decide : 8 ≤ 16)
  rcases sigTryFromErrTail_cases herr with rfl | rfl | rfl | rfl
  · simp only [AllocCostModel.stepEvents_nil]
    exact Nat.le_add_right _ 183475
  · exact (h72.mono (by decide : 43464 ≤ 183475)).groups_le st rfl
  · rw [List.append_nil]
    exact (h72.mono (by decide : 43464 ≤ 183475)).groups_le st rfl
  · exact ((h72.concat h128).mono (by decide : 43464 + 140011 ≤ 183475)).groups_le st
      ⟨_, _, rfl, rfl, rfl⟩

private theorem loop_grp_tail {g0 gf R W T : Nat} (h : gf ≤ g0 + T) :
    gf ≤ g0 + R + W + T := by
  omega

private theorem loop_grp_skip {g0 gf R' R W T : Nat}
    (h : gf ≤ g0 + R' + W + T) (hr : R' ≤ R) :
    gf ≤ g0 + R + W + T := by
  omega

private theorem loop_grp_comb {g0 g1 g2 r1 r2 r kw kw' kother t : Nat}
    (hstep : g1 + kw' ≤ g0 + r1 + kw)
    (hih : g2 ≤ g1 + r2 + (kother + kw') + t)
    (hr : r1 + r2 = r) :
    g2 ≤ g0 + r + (kother + kw) + t := by
  omega

private theorem loop_step_groups {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {maxLen rem : Nat}
    {caps : SigTryFromCaps} {evs : List AllocEvent}
    (hloop : SigTryFromLoopBoundedEnv rem caps evs) :
    ∀ (st : M.σ),
      rem ≤ maxLen →
      HasFineGroupCredit.groupsScaled (M.stepEvents evs st) ≤
        HasFineGroupCredit.groupsScaled st + 2369 * rem +
          140011 * capsRemGrows maxLen caps + 183475 := by
  induction hloop with
  | @done rem caps evs herr =>
    intro st _
    exact loop_grp_tail (errTail_groups_le hGrp st herr)
  | @skipStep rem rem' caps evs hlt _ ih =>
    intro st hrem
    exact loop_grp_skip (ih st (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hrem)))
      (Nat.mul_le_mul_left 2369 (Nat.le_of_lt hlt))
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm _ hrem_step hcap63 _ ih =>
    intro st hrem
    have hcap64 : caps.get f < 2 ^ 64 := Nat.lt_trans hcap63 (by decide : 2 ^ 63 < 2 ^ 64)
    set cap := caps.get f
    set cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    have hstep := bytesMergeEventsCore_groups_step hGrp hm hrem_step hrem hcap64 st
    change HasFineGroupCredit.groupsScaled
        (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) +
        140011 * wireRemGrows maxLen cap' ≤
      HasFineGroupCredit.groupsScaled st + 2369 * (rem - rem') +
        140011 * wireRemGrows maxLen cap at hstep
    rw [AllocCostModel.stepEvents_append]
    set st₁ := M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st
    have hrem' : rem' ≤ maxLen := by omega
    have hih := ih st₁ hrem'
    obtain ⟨hgw_pre, hgw_post⟩ := capsRemGrows_decomp maxLen caps f cap'
    rw [hgw_post, Nat.mul_add] at hih
    rw [hgw_pre, Nat.mul_add]
    have hrem_mul : 2369 * (rem - rem') + 2369 * rem' = 2369 * rem := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    exact loop_grp_comb hstep hih hrem_mul

private theorem loop_grp_assoc {gf g0 a b c : Nat} (h : gf ≤ g0 + a + b + c) :
    gf ≤ g0 + (a + b + c) := by
  omega

/-- Loop-level `PhaseGroupSpec` for `SigTryFromLoopBoundedEnv N SigTryFromCaps.zero`. -/
theorem sigTryFromLoop_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (N : Nat) :
    PhaseGroupSpec M (SigTryFromLoopBoundedEnv N SigTryFromCaps.zero)
      (sigTryFromLoopDeltaGrpS N) where
  groups_le st0 {_} hloop := by
    have h := loop_step_groups hGrp hloop st0 (Nat.le_refl N)
    have hzero_gw : capsRemGrows N SigTryFromCaps.zero = 4 * wireRemGrows N 0 := by
      simp only [capsRemGrows, SigTryFromCaps.zero]
      omega
    have hmul4 : 140011 * (4 * wireRemGrows N 0) = 560044 * wireRemGrows N 0 := by
      rw [← Nat.mul_assoc]
    rw [hzero_gw, hmul4] at h
    exact loop_grp_assoc h

private theorem phaseGroup_intoBoxedOpt {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (adOpt : Option (List (BitVec 8))) :
    PhaseGroupSpec M (IntoBoxedOptBoundedEnv adOpt) 140011 := by
  cases adOpt with
  | none => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le 140011)
  | some ad => exact phaseGroupSpec_intoBoxedSlice hGrp ad

private theorem phaseGroup_sigTryFromPost {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (SigTryFromPostEnv bs) 420033 := by
  unfold SigTryFromPostEnv
  have hf_tail := PhaseGroupSpec.freeOnly M
  cases SignalMessage.tryFrom protoSignalCodec bs with
  | error err =>
    have hpre : PhaseGroupSpec M (SigTryFromPostOutPreEnv (.error err)) 0 :=
      PhaseGroupSpec.nil M
    exact (hpre.seq hf_tail).mono (Nat.zero_le 420033)
  | ok msg =>
    have hbox_ct : PhaseGroupSpec M (IntoBoxedBoundedEnv msg.ciphertext) 140011 :=
      phaseGroupSpec_intoBoxedSlice hGrp msg.ciphertext
    have hbox_ad := phaseGroup_intoBoxedOpt hGrp msg.addresses
    have hclone : PhaseGroupSpec M (TryCloneBytesEnv msg.serialized) 140011 :=
      phaseGroupSpec_tryCloneBytes hGrp msg.serialized
    have hpre := (PhaseGroupSpec.freeOnly M).seq (hbox_ct.seq (hbox_ad.seq hclone))
    exact (hpre.seq hf_tail).mono (by decide : 0 + (140011 + (140011 + 140011)) + 0 ≤ 420033)

private theorem sigTryFrom_join_grp {A k₁ k₂ k : Nat} (hk : k₁ + k₂ ≤ k) :
    max 0 ((A + k₁) + k₂) ≤ A + k := by
  omega

/-- `PhaseGroupSpec` for `SigTryFromBoundedEnv x`. -/
theorem sigTryFrom_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : TryFromGhost) :
    PhaseGroupSpec M (SigTryFromBoundedEnv x) (sigTryFromDeltaGrpS x) := by
  unfold SigTryFromBoundedEnv sigTryFromDeltaGrpS
  have hloop := sigTryFromLoop_phaseGroup hGrp x.bytes.length
  unfold sigTryFromLoopDeltaGrpS at hloop
  have hpost := phaseGroup_sigTryFromPost hGrp x.bytes
  exact ((PhaseGroupSpec.nil M).or (hloop.seq hpost)).mono
    (sigTryFrom_join_grp (by decide : 183475 + 420033 ≤ 603508))

end LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
