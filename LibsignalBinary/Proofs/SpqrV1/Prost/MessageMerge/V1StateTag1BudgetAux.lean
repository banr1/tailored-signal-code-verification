/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Shared Budget-Threaded Tag Infrastructure for `V1State::merge` (Tags 1–11)

Uniform `optInnerStatePolyCapBound` preservation and sub-message capacity extraction lemmas across
all 11 `V1State.InnerState` arms, together with `RustCliAllocBudget` `[LibsignalPlacement]` tag
entry/continuation bundles, `SpqrMergeLoopEnv` combinators, `deallocFreeOnlySpec`, and shared latch
tails (`+2680`, `+2692`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent AllocCallPreserved BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeIterEnv SpqrMergeLoopEnv
   ct1AcknowledgedPolyCapBound ct1ReceivedPolyCapBound ct1SampledPolyCapBound
   ekSentCt1ReceivedPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ct2SampledPolyCapBound ekReceivedCt1SampledPolyCapBound headerReceivedPolyCapBound
   headerSentPolyCapBound keysSampledPolyCapBound noHeaderReceivedPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (innerStatePolyCapMax optInnerStatePolyCapBound optInnerStatePolyCapMax
   v1StateErrFramePlaced v1StateLoopPrePlaced v1StateMergePlacedSpec)
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (DecodeErr mergeMessage mergeOptMessage)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound
   V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
   bv64_add_zero bv64_sub_zero chunkedInlStack
   codecWireTypeToProto mergeMessage_measure_lt
   optPolyDecoderPtsLen optPolyDecoder_getD_default_pts_len
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
   polyDecoder_mergeMessage_pts_len polyEncoder_mergeMessage_pts_polys_len
   protoPrefixStep_chunked_ct1Acknowledged_mergeField
   protoPrefixStep_chunked_ct1Received_mergeField
   protoPrefixStep_chunked_ct1Sampled_mergeField
   protoPrefixStep_chunked_ct2Sampled_mergeField
   protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField
   protoPrefixStep_chunked_ekSentCt1Received_mergeField
   protoPrefixStep_chunked_headerReceived_mergeField
   protoPrefixStep_chunked_headerSent_mergeField
   protoPrefixStep_chunked_keysSampled_mergeField
   protoPrefixStep_chunked_noHeaderReceived_mergeField
   proto_mergeMessage_len_le)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## 1. `optInnerStatePolyCapBound` Preservation & Sub-Message Extraction Across Tags `1..11` -/

private theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => nomatch h
  | ok a => exact ⟨a, rfl, h⟩

private theorem mergeOptPolyDecoder_pts_le {opt v : Option PolynomialDecoder}
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat}
    (h : mergeOptMessage PolynomialDecoder.mergeField wt opt r1 depth = .ok (v, r2)) :
    optPolyDecoderPtsLen v + r2.length ≤ optPolyDecoderPtsLen opt + r1.length := by
  unfold mergeOptMessage at h
  rcases hm : mergeMessage PolynomialDecoder.mergeField wt (opt.getD default) r1 depth with _ | ⟨d, r2'⟩
  · simp [hm, Bind.bind, Except.bind] at h
  · simp only [hm, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hlt := polyDecoder_mergeMessage_pts_len
      (show (mergeMessage PolynomialDecoder.mergeField wt (opt.getD default) r1 depth).toOption = some (d, r2') by
        rw [hm]; rfl)
    rw [optPolyDecoder_getD_default_pts_len] at hlt
    change d.pts.length + r2'.length ≤ optPolyDecoderPtsLen opt + r1.length
    omega

private theorem mergeOptPolyEncoder_pts_polys_le {opt v : Option PolynomialEncoder}
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat}
    (h : mergeOptMessage PolynomialEncoder.mergeField wt opt r1 depth = .ok (v, r2)) :
    optPolyEncoderPtsLen v + r2.length ≤ optPolyEncoderPtsLen opt + r1.length ∧
      optPolyEncoderPolysLen v + r2.length ≤ optPolyEncoderPolysLen opt + r1.length := by
  unfold mergeOptMessage at h
  rcases hm : mergeMessage PolynomialEncoder.mergeField wt (opt.getD default) r1 depth with _ | ⟨e, r2'⟩
  · simp [hm, Bind.bind, Except.bind] at h
  · simp only [hm, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨hlt1, hlt2⟩ := polyEncoder_mergeMessage_pts_polys_len
      (show (mergeMessage PolynomialEncoder.mergeField wt (opt.getD default) r1 depth).toOption = some (e, r2') by
        rw [hm]; rfl)
    rw [optPolyEncoder_getD_default_pts_len] at hlt1
    rw [optPolyEncoder_getD_default_polys_len] at hlt2
    change e.pts.length + r2'.length ≤ optPolyEncoderPtsLen opt + r1.length ∧
      e.polys.length + r2'.length ≤ optPolyEncoderPolysLen opt + r1.length
    exact ⟨by omega, by omega⟩

theorem optPolyDecoderPtsLen_of_chunked_merge {M : Type}
    (mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType → List (BitVec 8) → Nat → Except DecodeErr (M × List (BitVec 8)))
    (getDec : M → Option PolynomialDecoder)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) →
      (getDec m' = getDec m ∧ r2.length ≤ r1.length) ∨
      mergeOptMessage PolynomialDecoder.mergeField wt (getDec m) r1 depth = .ok (getDec m', r2))
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {m m' : M} {bs after : List (BitVec 8)} {depth : Nat}
    (hm : (mergeMessage mf wt m bs depth).toOption = some (m', after)) :
    optPolyDecoderPtsLen (getDec m') + after.length ≤ optPolyDecoderPtsLen (getDec m) + bs.length := by
  have hlt := mergeMessage_measure_lt mf (fun x => optPolyDecoderPtsLen (getDec x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact mergeOptPolyDecoder_pts_le hopt) hm
  omega

private theorem max_add_le_of_add_le {x y z w n m : Nat}
    (h1 : x + n ≤ y + m) (h2 : z + n ≤ w + m) :
    Nat.max x z + n ≤ Nat.max y w + m := by
  simp only [Nat.max_def]; split <;> split <;> omega

theorem optPolyEncoderMax_of_chunked_merge {M : Type}
    (mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType → List (BitVec 8) → Nat → Except DecodeErr (M × List (BitVec 8)))
    (getEnc : M → Option PolynomialEncoder)
    (hstep : ∀ {m m' : M} {tag : BitVec 32} {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {r1 r2 : List (BitVec 8)} {depth : Nat},
      mf m tag wt r1 depth = .ok (m', r2) →
      (getEnc m' = getEnc m ∧ r2.length ≤ r1.length) ∨
      mergeOptMessage PolynomialEncoder.mergeField wt (getEnc m) r1 depth = .ok (getEnc m', r2))
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType} {m m' : M} {bs after : List (BitVec 8)} {depth : Nat}
    (hm : (mergeMessage mf wt m bs depth).toOption = some (m', after)) :
    Nat.max (optPolyEncoderPtsLen (getEnc m')) (optPolyEncoderPolysLen (getEnc m')) + after.length ≤
      Nat.max (optPolyEncoderPtsLen (getEnc m)) (optPolyEncoderPolysLen (getEnc m)) + bs.length := by
  have hlt1 := mergeMessage_measure_lt mf (fun x => optPolyEncoderPtsLen (getEnc x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact (mergeOptPolyEncoder_pts_polys_le hopt).1) hm
  have hlt2 := mergeMessage_measure_lt mf (fun x => optPolyEncoderPolysLen (getEnc x))
    (fun h => by
      rcases hstep h with ⟨heq, hle⟩ | hopt
      · rw [heq]; omega
      · exact (mergeOptPolyEncoder_pts_polys_le hopt).2) hm
  exact max_add_le_of_add_le (by omega) (by omega)

theorem optInnerStatePolyCapBound_ge_len (opt : Option V1State.InnerState) (n : Nat) :
    n ≤ optInnerStatePolyCapBound opt n := by
  unfold optInnerStatePolyCapBound; omega

theorem keysSampledPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    keysSampledPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.keysSampled x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem headerSentPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    headerSentPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.headerSent x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ct1ReceivedPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ct1ReceivedPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ct1Received x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ekSentCt1ReceivedPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ekSentCt1ReceivedPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ekSentCt1Received x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem noHeaderReceivedPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    noHeaderReceivedPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.noHeaderReceived x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem headerReceivedPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    headerReceivedPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.headerReceived x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ct1SampledPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ct1SampledPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ct1Sampled x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ekReceivedCt1SampledPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ekReceivedCt1SampledPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ekReceivedCt1Sampled x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ct1AcknowledgedPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ct1AcknowledgedPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ct1Acknowledged x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem ct2SampledPolyCapBound_le (iwt : WireType) (msgPtr bufRef slot ptr : BitVec 64)
    (rest : List (BitVec 8)) (opt : Option V1State.InnerState) :
    ct2SampledPolyCapBound
        ⟨iwt, msgPtr, match opt with | some (.ct2Sampled x) => x | _ => default, bufRef, slot, ptr, rest⟩ ≤
      optInnerStatePolyCapBound opt rest.length := by
  cases opt with
  | none => exact Nat.le_refl _
  | some st => cases st <;> first | exact Nat.le_refl _ | exact Nat.add_le_add_right (Nat.zero_le _) _

theorem optInnerStatePolyCapBound_of_keysUnsampled {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType}
    {m m' : V1State.Chunked.KeysUnsampled} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField wt m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.keysUnsampled m')) after.length ≤ bs.length := by
  have hle := proto_mergeMessage_len_le hm
  change 0 + after.length ≤ bs.length
  omega

theorem optInnerStatePolyCapBound_of_keysSampled {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.KeysSampled} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.keysSampled m')) after.length ≤
      keysSampledPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax keysSampledPolyCapBound
  refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.KeysSampled.mergeField (·.sendingHdr) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_keysSampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.KeysSampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_headerSent {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.HeaderSent} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.headerSent m')) after.length ≤
      headerSentPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax headerSentPolyCapBound
  have h1 : Nat.max (optPolyEncoderPtsLen m'.sendingEk) (optPolyEncoderPolysLen m'.sendingEk) + after.length ≤
      Nat.max (optPolyEncoderPtsLen m.sendingEk) (optPolyEncoderPolysLen m.sendingEk) + bs.length := by
    refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.HeaderSent.mergeField (·.sendingEk) (fun h => ?_) hm
    have hle := (protoPrefixStep_chunked_headerSent_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.HeaderSent.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
      · split at h
        · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  have h2 : optPolyDecoderPtsLen m'.receivingCt1 + after.length ≤
      optPolyDecoderPtsLen m.receivingCt1 + bs.length := by
    refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.HeaderSent.mergeField (·.receivingCt1) (fun h => ?_) hm
    have hle := (protoPrefixStep_chunked_headerSent_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.HeaderSent.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
      · split at h
        · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  exact max_add_le_of_add_le h1 h2

theorem optInnerStatePolyCapBound_of_ct1Received {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.Ct1Received} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ct1Received m')) after.length ≤
      ct1ReceivedPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ct1ReceivedPolyCapBound
  refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.Ct1Received.mergeField (·.sendingEk) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_ct1Received_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct1Received.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_ekSentCt1Received {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.EkSentCt1Received} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ekSentCt1Received m')) after.length ≤
      ekSentCt1ReceivedPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ekSentCt1ReceivedPolyCapBound
  refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.EkSentCt1Received.mergeField (·.receivingCt2) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_ekSentCt1Received_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.EkSentCt1Received.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_noHeaderReceived {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.NoHeaderReceived} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.noHeaderReceived m')) after.length ≤
      noHeaderReceivedPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax noHeaderReceivedPolyCapBound
  refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.NoHeaderReceived.mergeField (·.receivingHdr) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_noHeaderReceived_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.NoHeaderReceived.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_headerReceived {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.HeaderReceived} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.headerReceived m')) after.length ≤
      headerReceivedPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax headerReceivedPolyCapBound
  refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.HeaderReceived.mergeField (·.receivingEk) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_headerReceived_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.HeaderReceived.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_ct1Sampled {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.Ct1Sampled} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ct1Sampled m')) after.length ≤
      ct1SampledPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ct1SampledPolyCapBound
  have h1 : Nat.max (optPolyEncoderPtsLen m'.sendingCt1) (optPolyEncoderPolysLen m'.sendingCt1) + after.length ≤
      Nat.max (optPolyEncoderPtsLen m.sendingCt1) (optPolyEncoderPolysLen m.sendingCt1) + bs.length := by
    refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.Ct1Sampled.mergeField (·.sendingCt1) (fun h => ?_) hm
    have hle := (protoPrefixStep_chunked_ct1Sampled_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.Ct1Sampled.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
      · split at h
        · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  have h2 : optPolyDecoderPtsLen m'.receivingEk + after.length ≤
      optPolyDecoderPtsLen m.receivingEk + bs.length := by
    refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.Ct1Sampled.mergeField (·.receivingEk) (fun h => ?_) hm
    have hle := (protoPrefixStep_chunked_ct1Sampled_mergeField _ _ _ _).length_le h
    unfold V1State.Chunked.Ct1Sampled.mergeField at h
    split at h
    · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
    · split at h
      · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
      · split at h
        · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
        · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  exact max_add_le_of_add_le h1 h2

theorem optInnerStatePolyCapBound_of_ekReceivedCt1Sampled {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.EkReceivedCt1Sampled} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ekReceivedCt1Sampled m')) after.length ≤
      ekReceivedCt1SampledPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ekReceivedCt1SampledPolyCapBound
  refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.EkReceivedCt1Sampled.mergeField (·.sendingCt1) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_ct1Acknowledged {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.Ct1Acknowledged} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ct1Acknowledged m')) after.length ≤
      ct1AcknowledgedPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ct1AcknowledgedPolyCapBound
  refine optPolyDecoderPtsLen_of_chunked_merge V1State.Chunked.Ct1Acknowledged.mergeField (·.receivingEk) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_ct1Acknowledged_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct1Acknowledged.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩

theorem optInnerStatePolyCapBound_of_ct2Sampled {iwt : WireType}
    {msgPtr bufRef slot ptr : BitVec 64}
    {m m' : V1State.Chunked.Ct2Sampled} {bs after : List (BitVec 8)}
    (hm : (mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) m bs 99).toOption = some (m', after)) :
    optInnerStatePolyCapBound (some (.ct2Sampled m')) after.length ≤
      ct2SampledPolyCapBound ⟨iwt, msgPtr, m, bufRef, slot, ptr, bs⟩ := by
  unfold optInnerStatePolyCapBound optInnerStatePolyCapMax innerStatePolyCapMax ct2SampledPolyCapBound
  refine optPolyEncoderMax_of_chunked_merge V1State.Chunked.Ct2Sampled.mergeField (·.sendingCt2) (fun h => ?_) hm
  have hle := (protoPrefixStep_chunked_ct2Sampled_mergeField _ _ _ _).length_le h
  unfold V1State.Chunked.Ct2Sampled.mergeField at h
  split at h
  · obtain ⟨⟨v, r⟩, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩
  · split at h
    · obtain ⟨⟨v, r⟩, h1, h2⟩ := bind_ok_inv h; cases h2; exact Or.inr h1
    · obtain ⟨r, _, h2⟩ := bind_ok_inv h; cases h2; exact Or.inl ⟨rfl, hle⟩


/-! ## 2. Budget-Threaded Tag Entry/Continuation Bundles, Envelope Combinators & Shared Tails -/

/-- `AllocCostModel.stepEvents` distributes over list concatenation. -/
theorem stepEvents_append_eq {M : AllocCostModel} (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    M.stepEvents (evs₁ ++ evs₂) st = M.stepEvents evs₂ (M.stepEvents evs₁ st) := by
  induction evs₁ generalizing st with
  | nil => rfl
  | cons ev tl ih => exact ih (M.step ev st)

/-- Equality of `A.pool lim st` across a `VmPreserved` state transition. -/
theorem pool_eq_of_vmPreserved {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s1 s2 : State} (h : VmPreserved s1 s2) :
    A.pool lim st s1 = A.pool lim st s2 := by
  rw [← A.atState_pool, ← A.atState_eq_of_vmPreserved lim st h, A.atState_pool]

/-- Panic postcondition of `SepWPp` when `spec.onPanic = fun _ _ _ => ⌜False⌝`
(definitionally equal to the `Qp` produced by `wpp_init` on `v1StateMergePlacedSpec A lim`). -/
abbrev WppPanicFalse (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)

theorem wppPanicFalse_of_false {R F : SepProp} {sf : State} :
    WppPanicFalse R sf ((⌜False⌝ : SepProp) ∗ F) := fun hm => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

/-- Budget-threaded entry hypotheses for any tag arm `1..11` after `BR X10` (`+296`)
under `[LibsignalPlacement]`. -/
structure V1StateTagEntryBudgetPlaced [LibsignalPlacement] {M : AllocCostModel}
    (lim : BudgetLimits) (H : String → Option (State → State)) (s0 : State)
    (x : V1StateMergeGhost) (st : M.σ) (m : V1State) (rest : List (BitVec 8))
    (iwt : WireType) (limit : Nat) (s : State) : Prop where
  hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s
  hpoly_cap :
    optInnerStatePolyCapBound m.innerState rest.length ≤
      optInnerStatePolyCapBound x.msg.innerState x.bs.length
  hFit :
    FitsEnv M lim st
      (SpqrMergeLoopEnv (8 * rest.length + 24) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length))

/-- Budget-threaded continuation at `(blkPl_298).base + 2700#64` (`0x4f274`) for tag `k` (`1..11`)
under `[LibsignalPlacement]`. -/
structure V1StateTagContPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (s0 : State) (x : V1StateMergeGhost)
    (st0 st : M.σ) (R : SepProp) (k : Nat) (m : V1State)
    (rest : List (BitVec 8)) (iwt : WireType) (limit : Nat) : Prop where
  onErr :
    (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = none →
    ∀ (evs_tag : List AllocEvent) (s' : State) (err : BitVec 64) (n_err : Nat),
      SpqrMergeLoopEnv (8 * rest.length + 16) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_tag →
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = err → err ≠ 0#64 → n_err ≤ 3 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (decodeErrorAtStackLen A.repAlloc err n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
          memRegion (s0.sp - 816#64) 720 ∗
          v1StateErrFramePlaced A lim (M.stepEvents evs_tag st) s0 s' x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)
  onOk :
    ∀ (evs_tag : List AllocEvent) (m' : V1State) (rest' : List (BitVec 8)) (s' : State),
      (V1State.mergeField m (BitVec.ofNat 32 k) (codecWireTypeToProto iwt) rest 99).toOption = some (m', rest') →
      OptInnerStatePolyBound rest'.length m'.innerState →
      optInnerStatePolyCapBound m'.innerState rest'.length ≤
        optInnerStatePolyCapBound x.msg.innerState x.bs.length →
      rest'.length ≤ rest.length →
      SpqrMergeLoopEnv (8 * (rest.length - rest'.length) + 8) x.bs.length
        (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs_tag →
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s0.sp - 816#64 → s'.v1TraceEq s0 →
      s'.readReg64 (Reg.gpr 21#5) = 0#64 →
      V1StateLoopRegsPlaced s0 x limit s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim (M.stepEvents evs_tag st) s0 s' x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest')
        (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)

/-- Uniform per-tag step hypothesis shape consumed by `V1StateLoopBudget` for tag `k` at `entryOff`. -/
abbrev V1StateTagStepHypPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) (k : Nat) (entryOff : BitVec 64) : Prop :=
  ∀ {s0 s : State} {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat},
    V1StateTagEntryBudgetPlaced lim H s0 x st m rest iwt limit s →
    s.pc = (blkPl_298).base + entryOff →
    V1StateTagContPlaced A lim H s0 x st0 st R k m rest iwt limit →
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A lim) (x, st0) R s0) (WppPanicFalse R)

theorem spqrMergeLoopEnv_of_freeOnly {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hf : FreeOnlyEvs evs) :
    SpqrMergeLoopEnv 1 maxLen polyCapBound evs :=
  SpqrMergeLoopEnv.single (fuel := 0) (.deallocs hf)

theorem tag_fitsEnv_sub {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {restLen bsLen subCap outerCap : Nat}
    (hrest : restLen ≤ bsLen) (hsub : subCap ≤ outerCap)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv (8 * restLen + 24) bsLen outerCap)) :
    FitsEnv M lim st (SpqrMergeLoopEnv (6 * restLen + 12) restLen subCap) :=
  hFit.mono fun _ he => he.mono (by omega) hrest hsub

theorem tag_err_env_inplace {restLen bsLen subCap outerCap : Nat} {evs : List AllocEvent}
    (hrest : restLen ≤ bsLen) (hsub : subCap ≤ outerCap)
    (hevs : SpqrMergeLoopEnv (6 * restLen + 12) restLen subCap evs) :
    SpqrMergeLoopEnv (8 * restLen + 16) bsLen outerCap evs :=
  hevs.mono (by omega) hrest hsub

theorem tag_err_env_of_free {restLen bsLen subCap outerCap : Nat}
    {evs₁ evs₂ : List AllocEvent}
    (hrest : restLen ≤ bsLen) (hsub : subCap ≤ outerCap)
    (hevs₁ : SpqrMergeLoopEnv (6 * restLen + 12) restLen subCap evs₁)
    (hevs₂ : FreeOnlyEvs evs₂) :
    SpqrMergeLoopEnv (8 * restLen + 16) bsLen outerCap (evs₁ ++ evs₂) :=
  ((hevs₁.mono (Nat.le_refl _) hrest hsub).append (spqrMergeLoopEnv_of_freeOnly hevs₂)).mono_fuel (by omega)

theorem tag_ok_env_inplace {restLen rest'Len bsLen subCap outerCap : Nat}
    {evs : List AllocEvent}
    (hrest : restLen ≤ bsLen) (hsub : subCap ≤ outerCap)
    (hevs : SpqrMergeLoopEnv (6 * (restLen - rest'Len)) restLen subCap evs) :
    SpqrMergeLoopEnv (8 * (restLen - rest'Len) + 8) bsLen outerCap evs :=
  hevs.mono (by omega) hrest hsub

theorem tag_ok_env_of_free {restLen rest'Len bsLen subCap outerCap : Nat}
    {evs₁ evs₂ : List AllocEvent}
    (hrest : restLen ≤ bsLen) (hsub : subCap ≤ outerCap)
    (hevs₁ : SpqrMergeLoopEnv (6 * (restLen - rest'Len)) restLen subCap evs₁)
    (hevs₂ : FreeOnlyEvs evs₂) :
    SpqrMergeLoopEnv (8 * (restLen - rest'Len) + 8) bsLen outerCap (evs₁ ++ evs₂) :=
  ((hevs₁.mono (Nat.le_refl _) hrest hsub).append (spqrMergeLoopEnv_of_freeOnly hevs₂)).mono_fuel (by omega)

/-- Deallocation contract specialized to `FreeOnlyEvs`-compatible `rustDeallocEvents` for tag error cleanup. -/
def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem freeOnlyEvs_rustDeallocEvents (sz al : Nat) :
    FreeOnlyEvs (rustDeallocEvents sz al) :=
  LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz

theorem align_pre {prog : Program} {pc : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} (h : P = P') (hwp : SepWP prog pc s P' post) :
    SepWP prog pc s P post :=
  h ▸ hwp

theorem sepWPp_congr_state_pre {prog : Program} {ret : BitVec 64} {s s' : State}
    {P : State → SepProp} {post panic : State → SepProp → Prop}
    (hpool : P s = P s')
    (hwp : SepWPp prog ret s' (P s') post panic) :
    SepWPp prog ret s' (P s) post panic :=
  hpool ▸ hwp

theorem v1State_tail_2692_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_298).base + 2692#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      VmPreserved s s' →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ mpl, LibsignalCodeRoLoaded mpl s.mem → LibsignalCodeRoLoaded mpl s'.mem) →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
     by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
     fun _ _ _ => by simp only [arm64_norm]⟩
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => by simpa only [arm64_norm] using hinv)

theorem v1State_tail_2680_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {P : SepProp} {post panic : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_298).base + 2680#64)
    (hrun : s.status = .Running)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_298).base + 2700#64 →
      s'.status = .Running → s'.sp = s.sp → s'.v1TraceEq s →
      VmPreserved s s' →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) →
      s'.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) →
      s'.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 27#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.sp + 240#64 →
      s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) →
      s'.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 →
      s'.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) →
      s'.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) →
      (∀ mpl, LibsignalCodeRoLoaded mpl s.mem → LibsignalCodeRoLoaded mpl s'.mem) →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 2700#64)
  wp_steps; wp_reach
  exact hcont _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
     by simp only [arm64_norm], fun _ => by simp only [arm64_norm],
     fun _ _ _ => by simp only [arm64_norm]⟩
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ hinv => by simpa only [arm64_norm] using hinv)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
