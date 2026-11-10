/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget

@[expose] public section

set_option autoImplicit false

/-!
# Peak Credit and Group Specifications for SPQR `<States>::recv`

Sequential `PhaseCreditSpec` and `PhaseGroupSpec` bounds for all 12 dispatch arms of
`<spqr::v1::chunked::states::States>::recv` in binary call order, both in regime-uniform affine form
over `rawV1State st.into_pb` (`ModelHyps M`) and specialized to `fineCostModel` under protocol field
sizes (`StatesProtocolSizes`, `Δcum = 1,647,247`, `Δlive = Δpeak = 0`, `3,732` groups).
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec

open Arm64 (MMAP_MIN_ADDR PAGE_SIZE pageAlignUp)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes CIPHERTEXT1_SIZE Chunk DECAPSULATION_KEY_SIZE ENCAPSULATION_KEY_SIZE
   ENCAPSULATION_STATE_SIZE Epoch HEADER_SIZE Message Poly PolyDecoder PolynomialDecoder
   Pt SortedSetPt States StatesResult V1State decoderFromPbStateDecode pbToProtoPolyDecoder
   protoPolyDecoderToPb spqrAuthApi spqrPolyApi u16ToBeBytes)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1Sampled Ct2Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (Ct1Received EkSentCt1Received HeaderSent KeysSampled KeysUnsampled)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkLoopTotal addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (collectPointsVecsTotal decodedMessageLoopTotal decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk (NoHeaderReceivedRecvHdrChunkGhost)
open CryptoVerification.SpqrV1.Top.StateSize
  (except_bind_eq_ok optRaw rawAuth rawChCt1Acknowledged rawChCt1Received rawChCt1Sampled
   rawChCt2Sampled rawChEkReceivedCt1Sampled rawChEkSentCt1Received rawChHeaderReceived
   rawChHeaderSent rawChKeysSampled rawChKeysUnsampled rawChNoHeaderReceived rawInnerState
   rawPolyDec rawUcCt1Sent rawUcCt1SentEkReceived rawUcEkSentCt1Received rawUcHeaderSent
   rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale FineStepBound fineCostModel fineSmallAllocCost fineSmallReallocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq fineDynIvsOfCum fineMaxGroupsOfCum
   fineMaxMetaAreasOfCum fineStepReserveOfCum smallAllocCost_le_488_of_le_28
   smallAllocCost_le_738_of_le_44 smallAllocCost_le_two_mul_add)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound PhaseGroupSpec fineDynIvsOfGroups fineStepReserveOfGroups
   fitsEnv_fineCostModel_of_phaseCredit_groups)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit nonVacLimits)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit (encodeBytes_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
  (NonFreeBound.append_eq PhaseCreditSpec.append_eq PhaseCreditSpec.rustRealloc_aff
   PhaseCreditSpec.rustRealloc_small_exact addChunkSlots_fine_576_phaseCreditSpec
   addChunkSlots_fine_640_phaseCreditSpec addChunkSlots_fine_replicate16_phaseCreditSpec
   addChunkSlots_fine_two_mul_phaseCreditSpec addChunkSlots_nonFreeBound
   addChunkSlots_phaseCreditSpec computeAtCall_small_phaseCreditSpec
   decodedMessage_fine_tight_phaseCreditSpec decodedMessage_nonFreeBound
   decodedMessage_phaseCreditSpec decodedMessage_ptsNeeded_le_576_nonFreeBound
   decodedMessage_ptsNeeded_le_576_phaseCreditSpec encodeBytes_fine_160_phaseCreditSpec
   encodeBytes_fine_1152_phaseCreditSpec encodeBytes_nonFreeBound
   encodeBytes_small_phaseCreditSpec fineSmallAllocCost_le_1607_of_le_74
   fineSmallAllocCost_le_9789_of_le_1280 fineSmallReallocCost_le_9789_of_le_296
   fineSmallReallocCost_le_10747_of_le_2430 libcruxHmacSha256_fine_phaseCreditSpec
   libcruxHmacSha256_nonFreeBound libcruxHmacSha256_phaseCreditSpec ptsLenSum
   sendCt2ConcatHmac_nonFreeBound sendCt2Reserve128_fine_le_1088_phaseCreditSpec
   sendCt2Reserve128_nonFreeBound sendCt2Reserve128_phaseCreditSpec
   sendCt2Seg23_fine_phaseCreditSpec sendCt2Seg23_nonFreeBound sendCt2Seg23_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotsEnv addChunkSlotsEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv RecvHdrChunkTailEnv recvHdrChunkAllocMacHdrEvents
   recvHdrChunkHmacEvents)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env UnchunkedSendCt2Env sendCt2ConcatHmacEvents sendCt2Seg23Events)

/-! ## `rawPolyDec` and `decodedMessageTotal` Size Bounds -/

private theorem flatMap_ptSerialize_length (l : List Pt) :
    (l.flatMap Pt.serialize).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hp : (Pt.serialize p).length = 4 := rfl
    omega

/-- Relates `rawPolyDec (protoPolyDecoderToPb dec.intoPb)` to `4 * ptsLenSum dec.pts + 22 * dec.pts.length`.
-/
theorem rawPolyDec_intoPb_eq (dec : PolyDecoder) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) = 4 * ptsLenSum dec.pts + 22 * dec.pts.length := by
  unfold PolyDecoder.intoPb protoPolyDecoderToPb rawPolyDec ptsLenSum
  dsimp only
  induction dec.pts with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, flatMap_ptSerialize_length]
    omega

private theorem ptsLenSum_replicate_empty :
    ∀ n : Nat, ptsLenSum (List.replicate n SortedSetPt.new) = 0
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, ptsLenSum, List.map_cons, List.sum_cons]
    have h0 : SortedSetPt.new.vec.length = 0 := rfl
    rw [h0, Nat.zero_add]
    exact ptsLenSum_replicate_empty n

private theorem decodedMessageLoopTotal_snd_length (dec : PolyDecoder) (pv : List (List Pt)) :
    ∀ (rem i : Nat) (polys : List (Option Poly)) (out : List (BitVec 8)),
      (decodedMessageLoopTotal dec pv i rem polys out).2.length = out.length + 2 * rem
  | 0, _, _, out => by simp [decodedMessageLoopTotal]
  | rem + 1, i, polys, out => by
    unfold decodedMessageLoopTotal
    dsimp only
    rw [decodedMessageLoopTotal_snd_length dec pv rem (i + 1)]
    simp [u16ToBeBytes]
    omega

/-- Whenever `decodedMessageTotal dec = some out`, `out.length = 2 * dec.ptsNeeded`. -/
theorem decodedMessageTotal_some_length {dec : PolyDecoder} {out : Bytes}
    (h : decodedMessageTotal dec = some out) :
    out.length = 2 * dec.ptsNeeded := by
  unfold decodedMessageTotal at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · injection h with h_eq
      rw [← h_eq]
      simpa using decodedMessageLoopTotal_snd_length dec
        (collectPointsVecsTotal dec 0 dec.pts.length false []).2
        dec.ptsNeeded 0 (List.replicate 16 none) []

def optBytesLen : Option Bytes → Nat
  | none => 0
  | some bs => bs.length

theorem optBytesLen_decodedMessageTotal_le (dec : PolyDecoder) :
    optBytesLen (decodedMessageTotal dec) ≤ 2 * dec.ptsNeeded := by
  cases h : decodedMessageTotal dec with
  | none => exact Nat.zero_le _
  | some bs =>
    dsimp only [optBytesLen]
    rw [decodedMessageTotal_some_length h]

private theorem addChunkLoopTotal_ptsNeeded_eq (chunk : Chunk) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      (addChunkLoopTotal chunk i rem self).ptsNeeded = self.ptsNeeded
  | 0, _, _ => rfl
  | rem + 1, i, self => by
    unfold addChunkLoopTotal
    dsimp only
    rw [addChunkLoopTotal_ptsNeeded_eq chunk rem (i + 1)]
    split <;> rfl

/-- `addChunkTotal` preserves `ptsNeeded` unconditionally. -/
theorem addChunkTotal_ptsNeeded_uncond (self : PolyDecoder) (chunk : Chunk) :
    (addChunkTotal self chunk).ptsNeeded = self.ptsNeeded :=
  addChunkLoopTotal_ptsNeeded_eq chunk 16 0 self

private theorem seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) (hlp : l ≤ p) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem addChunkSlots_replicate16_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
      153136 131376 131376 16 := by
  have h := addChunkSlots_phaseCreditSpec hM (List.replicate 16 SortedSetPt.new)
  rw [ptsLenSum_replicate_empty 16, List.length_replicate] at h
  exact h.mono (by decide) (by decide) (by decide) (by decide)

private theorem lin_const_cap {a x xMax k : Nat} (hx : x ≤ xMax) :
    a * x + k ≤ a * xMax + k :=
  Nat.add_le_add_right (Nat.mul_le_mul_left a hx) k

private theorem id_const_cap {x xMax k : Nat} (hx : x ≤ xMax) :
    x + k ≤ xMax + k :=
  Nat.add_le_add_right hx k

private theorem mono_const_le {k1 m raw k2 : Nat} (hk : k1 ≤ k2) :
    k1 ≤ m * raw + k2 :=
  Nat.le_trans hk (Nat.le_add_left k2 (m * raw))

private theorem mono_lin_same_le {m x k1 raw k2 : Nat}
    (hx : x ≤ raw) (hk : k1 ≤ k2) :
    m * x + k1 ≤ m * raw + k2 :=
  Nat.add_le_add (Nat.mul_le_mul_left m hx) hk

private theorem keysSampled_arm_le {a0 k0 kstep ek m raw k2 : Nat}
    (ha : 16 * a0 ≤ m) (hek : ek ≤ raw) (hk : k0 + 16 * kstep ≤ k2) :
    k0 + 16 * (a0 * ek + kstep) ≤ m * raw + k2 := by
  have hmul : (16 * a0) * ek ≤ m * raw := Nat.mul_le_mul ha hek
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

private theorem keysSampled_live_le {k0 kstep ek m raw k2 : Nat}
    (hm : 16 ≤ m) (hek : ek ≤ raw) (hk : k0 + 16 * kstep ≤ k2) :
    k0 + 16 * (ek + kstep) ≤ m * raw + k2 := by
  have hmul : 16 * ek ≤ m * raw := Nat.mul_le_mul hm hek
  rw [Nat.mul_add]
  omega

private theorem keysSampled_peak_le {k0 kstep ek m raw k2 : Nat}
    (hm : 16 ≤ m) (hek : ek ≤ raw) (hk : k0 + 16 * kstep ≤ k2) :
    max k0 (k0 + 16 * (ek + kstep)) ≤ m * raw + k2 := by
  have hmul : 16 * ek ≤ m * raw := Nat.mul_le_mul hm hek
  rw [Nat.mul_add]
  omega

private theorem sendCt2_enc_add_le {a ct1 k1 k2 m raw kOut : Nat}
    (ha : a ≤ m) (hct1 : ct1 ≤ raw) (hk : k1 + k2 ≤ kOut) :
    (a * ct1 + k1) + k2 ≤ m * raw + kOut := by
  have hmul : a * ct1 ≤ m * raw := Nat.mul_le_mul ha hct1
  omega

private theorem sendCt2_enc_peak_le {a ct1 k1 kp1 k2 m raw kOut : Nat}
    (ha : a ≤ m) (hct1 : ct1 ≤ raw) (hk1 : kp1 ≤ kOut) (hk2 : k1 + k2 ≤ kOut) :
    max (a * ct1 + kp1) ((a * ct1 + k1) + k2) ≤ m * raw + kOut := by
  have hmul : a * ct1 ≤ m * raw := Nat.mul_le_mul ha hct1
  omega

private theorem ct2Tail_cum_cap {n nMax rk ct1 k : Nat} (hn : n ≤ nMax) :
    2 * n + 2 * rk + 6 * ct1 + k ≤ 6 * (rk + ct1) + (2 * nMax + k) := by
  omega

private theorem ct2Tail_live_cap {n nMax rk ct1 k : Nat} (hn : n ≤ nMax) :
    n + rk + 3 * ct1 + k ≤ 3 * (rk + ct1) + (nMax + k) := by
  omega

private theorem dec_slots_extra_le {aS aL aE ptsSum ptsLen extra rawDec m raw : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * ptsLen)
    (hsum : extra + rawDec ≤ raw)
    (hS : aS ≤ 4 * m) (hL : aL ≤ 22 * m) (hE : aE ≤ m) :
    aS * ptsSum + aL * ptsLen + aE * extra ≤ m * raw := by
  have h1 : aS * ptsSum ≤ (4 * m) * ptsSum := Nat.mul_le_mul_right ptsSum hS
  have h2 : aL * ptsLen ≤ (22 * m) * ptsLen := Nat.mul_le_mul_right ptsLen hL
  have hE' : aE * extra ≤ m * extra := Nat.mul_le_mul_right extra hE
  have h3 : m * (extra + rawDec) ≤ m * raw := Nat.mul_le_mul_left m hsum
  rw [Nat.mul_add, hraw, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc,
    Nat.mul_comm m 4, Nat.mul_comm m 22] at h3
  omega

private theorem twoPhase_bound_le {aS aL ptsSum ptsLen rawDec c2 m raw kOut : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * ptsLen)
    (hdec : rawDec ≤ raw)
    (hS : aS ≤ 4 * m) (hL : aL ≤ 22 * m)
    (hk : c2 ≤ kOut) :
    (aS * ptsSum + aL * ptsLen) + c2 ≤ m * raw + kOut := by
  have h0 : 0 + rawDec ≤ raw := by omega
  have hbase := dec_slots_extra_le hraw h0 hS hL (Nat.zero_le m)
  omega

private theorem twoPhase_peak_le {aS aL ptsSum ptsLen rawDec l2 m raw kOut : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * ptsLen)
    (hdec : rawDec ≤ raw)
    (hS : aS ≤ 4 * m) (hL : aL ≤ 22 * m)
    (hk : l2 ≤ kOut) :
    max (aS * ptsSum + aL * ptsLen) ((aS * ptsSum + aL * ptsLen) + l2) ≤ m * raw + kOut := by
  have h0 : 0 + rawDec ≤ raw := by omega
  have hbase := dec_slots_extra_le hraw h0 hS hL (Nat.zero_le m)
  omega

private theorem threePhase_bound_le {aS aL aE ptsSum ptsLen extra rawDec c2 c3 m raw kOut : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * ptsLen)
    (hsum : extra + rawDec ≤ raw)
    (hS : aS ≤ 4 * m) (hL : aL ≤ 22 * m) (hE : aE ≤ m)
    (hk : c2 + c3 ≤ kOut) :
    (aS * ptsSum + aL * ptsLen) + (c2 + (aE * extra + c3)) ≤ m * raw + kOut := by
  have hbase := dec_slots_extra_le hraw hsum hS hL hE
  omega

private theorem threePhase_peak_le {aS aL aE ptsSum ptsLen extra rawDec l2 p3 m raw kOut : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * ptsLen)
    (hsum : extra + rawDec ≤ raw)
    (hS : aS ≤ 4 * m) (hL : aL ≤ 22 * m) (hE : aE ≤ m)
    (hk : l2 + p3 ≤ kOut) :
    max (aS * ptsSum + aL * ptsLen)
      ((aS * ptsSum + aL * ptsLen) + max l2 (l2 + (aE * extra + p3))) ≤ m * raw + kOut := by
  have hbase := dec_slots_extra_le hraw hsum hS hL hE
  omega

private theorem quad_linear_le_aux {n K a0 a1 b0 b1 c1 c2 m1 mTotal bTotal cTotal : Nat}
    (hK_b : b0 * K + b1 ≤ m1)
    (hK_c : 16 * (c1 * K + c2) ≤ bTotal)
    (hm : a0 + m1 ≤ mTotal)
    (hc : a1 + bTotal ≤ cTotal) :
    a0 * n + a1 + n * (b0 * K + b1) + 16 * (c1 * K + c2) ≤ mTotal * n + cTotal := by
  have hn1 : n * (b0 * K + b1) ≤ m1 * n := by
    rw [Nat.mul_comm m1 n]
    exact Nat.mul_le_mul_left n hK_b
  have hn2 : a0 * n + m1 * n ≤ mTotal * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right n hm
  omega

private theorem linear_step_le {K kMax b0 b1 m1 : Nat}
    (hK : K ≤ kMax) (h : b0 * kMax + b1 ≤ m1) : b0 * K + b1 ≤ m1 :=
  Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left b0 hK) b1) h

private theorem linear_step16_le {K kMax c1 c2 bTotal : Nat}
    (hK : K ≤ kMax) (h : 16 * (c1 * kMax + c2) ≤ bTotal) : 16 * (c1 * K + c2) ≤ bTotal :=
  Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (Nat.mul_le_mul_left c1 hK) c2)) h

private theorem decodedMessage_aff_cum_le_576 {n : Nat} (hn : n ≤ 576) :
    let K := n / 16 + 1
    4 * n + 19590 + n * (4 * K + 19098) + 16 * (12 * K + 28625) ≤ 19250 * n + 484694 := by
  intro K
  have hK : K ≤ 37 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.div_le_div_right hn) 1) (by decide)
  exact quad_linear_le_aux (m1 := 19246) (bTotal := 465104)
    (linear_step_le hK (by decide))
    (linear_step16_le hK (by decide))
    (by decide)
    (by decide)

private theorem decodedMessage_aff_live_le_576 {n : Nat} (hn : n ≤ 576) :
    let K := n / 16 + 1
    2 * n + 16646 + n * (2 * K + 16400) + 16 * (6 * K + 24589) ≤ 16476 * n + 413622 := by
  intro K
  have hK : K ≤ 37 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.div_le_div_right hn) 1) (by decide)
  exact quad_linear_le_aux (m1 := 16474) (bTotal := 396976)
    (linear_step_le hK (by decide))
    (linear_step16_le hK (by decide))
    (by decide)
    (by decide)

private theorem decodedMessage_aff_req_le_576 {n : Nat} (hn : n ≤ 576) :
    max 256 (max (2 * n) (2 * (n / 16 + 1) + 2)) ≤ max 256 (2 * n) := by
  omega

/-- Regime-uniform `PhaseCreditSpec` for `DecodedMessageEnv dec` when `dec.ptsNeeded ≤ 576`. -/
theorem decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dec : PolyDecoder} (hpts : dec.ptsNeeded ≤ 576) :
    PhaseCreditSpec M (DecodedMessageEnv dec)
      (19250 * dec.ptsNeeded + 484694)
      (16476 * dec.ptsNeeded + 413622)
      (16476 * dec.ptsNeeded + 413622)
      (max 256 (2 * dec.ptsNeeded)) :=
  (decodedMessage_phaseCreditSpec hM dec).mono
    (decodedMessage_aff_cum_le_576 hpts)
    (decodedMessage_aff_live_le_576 hpts)
    (decodedMessage_aff_live_le_576 hpts)
    (decodedMessage_aff_req_le_576 hpts)

/-! ## `sliceConcat2Events`, `send_ct2_encoder`, and `<Authenticator>::update` Envelopes -/

theorem sliceConcat2Events_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (n : Nat) :
    PhaseCreditSpec M (· = sliceConcat2Events n)
      (2 * n + 9539) (n + 8195) (n + 8195) n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · exact PhaseCreditSpec.rustAlloc_aff hM (req := n) (al := 1) (by decide)

/-- Allocation step for `extend_from_slice(mac)` inside `send_ct2_encoder`. -/
def SendCt2EncoderGrowEnv (ct2Len macLen : Nat) (evs : List AllocEvent) : Prop :=
  (macLen = 0 ∧ evs = []) ∨
    ∃ newCap : Nat,
      1 ≤ newCap ∧ newCap ≤ 2 * ct2Len + macLen + 8 ∧
      evs = (if ct2Len = 0 then rustAllocEvents newCap 1 else rustReallocEvents ct2Len newCap 1)

/-- Binary-order allocator trace envelope for `spqr::v1::chunked::send_ct::send_ct2_encoder`. -/
def SendCt2EncoderEnv (ct2Len macLen : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = sliceConcat2Events ct2Len)
    (SeqEnv (SendCt2EncoderGrowEnv ct2Len macLen)
      (SeqEnv (EncodeBytesEnv (ct2Len + macLen)) FreeOnlyEvs))

theorem sendCt2EncoderGrow_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ct2Len macLen : Nat) :
    PhaseCreditSpec M (SendCt2EncoderGrowEnv ct2Len macLen)
      (4 * ct2Len + 2 * macLen + 9555)
      (2 * ct2Len + macLen + 8203)
      (2 * ct2Len + macLen + 8203)
      (2 * ct2Len + macLen + 8) := by
  refine { req_align := ?_, credit_le := ?_ }
  · rintro evs (⟨_, rfl⟩ | ⟨newCap, hlo, hhi, rfl⟩)
    · intro ev hev; nomatch hev
    · split
      · exact ((PhaseCreditSpec.rustAlloc_aff hM (req := newCap) (al := 1) (by decide)).mono
          (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hhi).req_align _ rfl
      · exact ((PhaseCreditSpec.rustRealloc_aff hM (old := ct2Len) (new := newCap) (al := 1)
          (by decide) hlo).mono
          (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hhi).req_align _ rfl
  · rintro st0 evs (⟨_, rfl⟩ | ⟨newCap, hlo, hhi, rfl⟩)
    · exact ((PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl 0)).credit_le st0 rfl
    · split
      · exact ((PhaseCreditSpec.rustAlloc_aff hM (req := newCap) (al := 1) (by decide)).mono
          (by omega) (by omega) (by omega) hhi).credit_le st0 rfl
      · exact ((PhaseCreditSpec.rustRealloc_aff hM (old := ct2Len) (new := newCap) (al := 1)
          (by decide) hlo).mono (by omega) (by omega) (by omega) hhi).credit_le st0 rfl

/-- `PhaseCreditSpec` for `SendCt2EncoderEnv ct2Len macLen`. -/
theorem sendCt2Encoder_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ct2Len macLen : Nat) :
    PhaseCreditSpec M (SendCt2EncoderEnv ct2Len macLen)
      (38 * ct2Len + 34 * macLen + 171718)
      (19 * ct2Len + 17 * macLen + 147518)
      (19 * ct2Len + 17 * macLen + 147518)
      (2 * ct2Len + macLen + 8) := by
  unfold SendCt2EncoderEnv
  have h1 := sliceConcat2Events_phaseCreditSpec hM ct2Len
  have h2 := sendCt2EncoderGrow_phaseCreditSpec hM ct2Len macLen
  have h3 := encodeBytes_phaseCreditSpec hM (ct2Len + macLen)
  have h4 := PhaseCreditSpec.freeOnly_of_hyps hM
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by omega) (by omega) (by omega) (by omega)

theorem sendCt2Encoder_128_32_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (SendCt2EncoderEnv 128 32) 177670 150494 150494 296 :=
  (sendCt2Encoder_phaseCreditSpec hM 128 32).mono (by omega) (by omega) (by omega) (by omega)

/-- Binary-order allocator trace envelope for `<Authenticator>::update`. -/
def AuthUpdateEnv (rootKeyLen kLen : Nat) : List AllocEvent → Prop :=
  SeqEnv (· = sliceConcat2Events (rootKeyLen + kLen))
    (SeqEnv (· = sliceConcat2Events (Authenticator.updateLabel.length + 8))
      (SeqEnv (· = rustAllocEvents 64 1)
        (SeqEnv (· = rustAllocEvents 32 1)
          (SeqEnv FreeOnlyEvs
            (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs)))))

theorem authUpdate_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rootKeyLen kLen : Nat) :
    PhaseCreditSpec M (AuthUpdateEnv rootKeyLen kLen)
      (2 * (rootKeyLen + kLen) + 48057)
      (rootKeyLen + kLen + 41156)
      (rootKeyLen + kLen + 41156)
      (max (rootKeyLen + kLen) 64) := by
  unfold AuthUpdateEnv
  have hlbl : Authenticator.updateLabel.length = 45 := by decide
  rw [hlbl]
  have h1 := sliceConcat2Events_phaseCreditSpec hM (rootKeyLen + kLen)
  have h2 := sliceConcat2Events_phaseCreditSpec hM 53
  have h3 := PhaseCreditSpec.rustAlloc_aff hM (req := 64) (al := 1) (by decide)
  have h4 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have h5 := PhaseCreditSpec.freeOnly_of_hyps hM
  have h6 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have h7 := PhaseCreditSpec.freeOnly_of_hyps hM
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Value-parameterized allocator trace envelope for `<Ct1SentEkReceived>::send_ct2`. -/
def UnchunkedSendCt2BySizesEnv (es : Bytes) (ct1Len : Nat) : List AllocEvent → Prop :=
  ConcatEnv
    (ConcatEnv
      (ConcatEnv (· = sendCt2Seg23Events es) (SendCt2Reserve128Env ct1Len))
      (· = sendCt2ConcatHmacEvents ct1Len))
    FreeOnlyEvs

theorem unchunkedSendCt2BySizes_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (es : Bytes) (ct1Len : Nat) :
    PhaseCreditSpec M (UnchunkedSendCt2BySizesEnv es ct1Len)
      (6 * ct1Len + 82026) (3 * ct1Len + 58130) (3 * ct1Len + 68405)
      (max 2080 (2 * ct1Len + 254)) := by
  unfold UnchunkedSendCt2BySizesEnv
  have hSeg23 := sendCt2Seg23_phaseCreditSpec hM es
  have hRes := sendCt2Reserve128_phaseCreditSpec hM ct1Len
  have hConcatHmac :
      PhaseCreditSpec M (· = sendCt2ConcatHmacEvents ct1Len)
        (2 * ct1Len + 48485) (ct1Len + 41358) (ct1Len + 41358) (max (ct1Len + 171) 64) := by
    unfold sendCt2ConcatHmacEvents
    have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 35 + 8 + (ct1Len + 128)) (al := 1)
      (by decide)
    exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  exact (((hSeg23.concat hRes).concat hConcatHmac).concat (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem unchunkedSendCt2Env_iff_bySizes {F : ShaCompress} (x : UnchunkedSendCt2Ghost F)
    (evs : List AllocEvent) :
    UnchunkedSendCt2Env x evs ↔ UnchunkedSendCt2BySizesEnv x.st.es x.st.ct1.length evs := by
  constructor
  · rintro ⟨evsPre, evsFree, ⟨evsRes, hRes, rfl⟩, hFree, rfl⟩
    exact ⟨_, evsFree, rfl,
      ⟨sendCt2Seg23Events x.st.es ++ evsRes, sendCt2ConcatHmacEvents x.st.ct1.length, rfl,
        ⟨sendCt2Seg23Events x.st.es, evsRes, rfl, rfl, hRes⟩, rfl⟩,
      hFree⟩
  · rintro ⟨evsPre, evsFree, rfl, ⟨e12, e3, rfl, ⟨e1, evsRes, rfl, rfl, hRes⟩, rfl⟩, hFree⟩
    exact ⟨_, evsFree, ⟨evsRes, hRes, rfl⟩, hFree, rfl⟩

/-! ## `<NoHeaderReceived>::recv_hdr_chunk` and `<EkSentCt1Received>::recv_ct2_chunk` Envelopes -/

theorem recvHdrChunkTail_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (optHdr : Option Bytes) :
    let n := optBytesLen optHdr
    PhaseCreditSpec M (RecvHdrChunkTailEnv optHdr)
      (2 * n + 67559) (n + 57746) (n + 57746) (max n 105) := by
  cases optHdr with
  | none =>
    change PhaseCreditSpec M (RecvHdrChunkTailEnv none)
      (2 * 0 + 67559) (0 + 57746) (0 + 57746) (max 0 105)
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some hdrFull =>
    change PhaseCreditSpec M (RecvHdrChunkTailEnv (some hdrFull))
      (2 * hdrFull.length + 67559) (hdrFull.length + 57746) (hdrFull.length + 57746)
      (max hdrFull.length 105)
    by_cases hlt : hdrFull.length < 64
    · have heq : RecvHdrChunkTailEnv (some hdrFull) = (· = []) := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    · have heq :
          RecvHdrChunkTailEnv (some hdrFull) =
            SeqEnv
              (· = recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents)
              FreeOnlyEvs := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      have h_mac :
          PhaseCreditSpec M (· = recvHdrChunkAllocMacHdrEvents hdrFull.length)
            (2 * hdrFull.length + 19206) (hdrFull.length + 16454) (hdrFull.length + 16454)
            (max hdrFull.length 64) := by
        unfold recvHdrChunkAllocMacHdrEvents
        have ha :
            PhaseCreditSpec M
              (· = if hdrFull.length = 64 then [] else rustAllocEvents (hdrFull.length - 64) 1)
              (2 * (hdrFull.length - 64) + 9539) (hdrFull.length - 64 + 8195)
              (hdrFull.length - 64 + 8195) (hdrFull.length - 64) := by
          split
          · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
          · exact PhaseCreditSpec.rustAlloc_aff hM (req := hdrFull.length - 64) (al := 1)
              (by decide)
        have hb := PhaseCreditSpec.rustAlloc_aff hM (req := 64) (al := 1) (by decide)
        exact (PhaseCreditSpec.append_eq ha hb).mono (by omega) (by omega) (by omega) (by omega)
      have h_hmac :
          PhaseCreditSpec M (· = recvHdrChunkHmacEvents) 48353 41292 41292 105 := by
        unfold recvHdrChunkHmacEvents
        have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 105) (al := 1) (by decide)
        exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
          (by omega) (by omega) (by omega) (by omega)
      exact ((PhaseCreditSpec.append_eq h_mac h_hmac).seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
        (by omega) (by omega) (by omega) (by omega)

/-- Value-parameterized allocator trace envelope for `<NoHeaderReceived>::recv_hdr_chunk`. -/
def NoHeaderReceivedRecvHdrChunkBodyEnv {F : ShaCompress}
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (epoch : Epoch) (chunk : Chunk)
    (evs : List AllocEvent) : Prop :=
  if epoch != s.uc.epoch then
    evs = []
  else
    let receivingHdr := addChunkTotal s.receiving_hdr chunk
    SeqEnv (AddChunkSlotsEnv s.receiving_hdr.pts)
      (SeqEnv (DecodedMessageEnv receivingHdr)
        (RecvHdrChunkTailEnv (decodedMessageTotal receivingHdr)))
      evs

theorem noHeaderReceivedRecvHdrChunkBody_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (epoch : Epoch) (chunk : Chunk)
    (hpts : s.receiving_hdr.ptsNeeded ≤ 48) :
    PhaseCreditSpec M (NoHeaderReceivedRecvHdrChunkBodyEnv s epoch chunk)
      (436 * rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) + 1476445)
      (374 * rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) + 1262312)
      (374 * rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) + 1262312)
      (max 256 (2 * rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) + 16)) := by
  have hraw := rawPolyDec_intoPb_eq s.receiving_hdr
  have hdec0 :
      0 + rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤
        rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) :=
    Nat.le_of_eq (Nat.zero_add _)
  unfold NoHeaderReceivedRecvHdrChunkBodyEnv
  split
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · dsimp only
    let receivingHdr := addChunkTotal s.receiving_hdr chunk
    have hr_pts : receivingHdr.ptsNeeded ≤ 48 :=
      Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
    have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_hdr.pts
    have h2 :
        PhaseCreditSpec M (DecodedMessageEnv receivingHdr)
          (19250 * 48 + 484694) (16476 * 48 + 413622) (16476 * 48 + 413622) 256 :=
      (decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec hM (dec := receivingHdr) (by omega)).mono
        (lin_const_cap hr_pts) (lin_const_cap hr_pts) (lin_const_cap hr_pts) (by omega)
    have hn96 : optBytesLen (decodedMessageTotal receivingHdr) ≤ 96 := by
      have := optBytesLen_decodedMessageTotal_le receivingHdr; omega
    have h3 :
        PhaseCreditSpec M (RecvHdrChunkTailEnv (decodedMessageTotal receivingHdr))
          (0 * 0 + (2 * 96 + 67559)) (0 * 0 + (96 + 57746)) (0 * 0 + (96 + 57746)) 105 :=
      (recvHdrChunkTail_phaseCreditSpec hM (decodedMessageTotal receivingHdr)).mono
        (by rw [Nat.zero_mul, Nat.zero_add]; exact lin_const_cap hn96)
        (by rw [Nat.zero_mul, Nat.zero_add]; exact id_const_cap hn96)
        (by rw [Nat.zero_mul, Nat.zero_add]; exact id_const_cap hn96)
        (by omega)
    exact (h1.seq (h2.seq h3)).mono
      (threePhase_bound_le hraw hdec0 (by decide) (by decide) (by decide) (by decide))
      (threePhase_bound_le hraw hdec0 (by decide) (by decide) (by decide) (by decide))
      (threePhase_peak_le hraw hdec0 (by decide) (by decide) (by decide) (by decide))
      (by omega)

theorem noHeaderReceivedRecvHdrChunk_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (hpts : x.self.receiving_hdr.ptsNeeded ≤ 48) :
    let rawDec := rawPolyDec (protoPolyDecoderToPb x.self.receiving_hdr.intoPb)
    PhaseCreditSpec M (NoHeaderReceivedRecvHdrChunkEnv x)
      (436 * rawDec + 1476445)
      (374 * rawDec + 1262312)
      (374 * rawDec + 1262312)
      (max 256 (2 * rawDec + 16)) :=
  noHeaderReceivedRecvHdrChunkBody_phaseCreditSpec hM x.self x.epoch x.chunk hpts

/-- Slice allocations splitting `ct2Full` into `mac` and `ct2` (`128` bytes) in `<EkSentCt1Received>::recv_ct2_chunk`.
-/
def recvCt2AllocMacCt2Events (ct2FullLen : Nat) : List AllocEvent :=
  (if ct2FullLen = 128 then [] else rustAllocEvents (ct2FullLen - 128) 1) ++
    rustAllocEvents 128 1

/-- Post-`decoded_message` allocator trace envelope for `<EkSentCt1Received>::recv_ct2_chunk`. -/
def RecvCt2ChunkTailEnv (rootKeyLen ct1Len : Nat) : Option Bytes → List AllocEvent → Prop
  | none, evs => FreeOnlyEvs evs
  | some ct2Full, evs =>
    if ct2Full.length < 128 then
      FreeOnlyEvs evs
    else
      SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
        (SeqEnv (· = rustAllocEvents 32 1)
          (SeqEnv (· = sliceConcat2Events 41)
            (SeqEnv (· = rustAllocEvents 32 1)
              (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                (SeqEnv (SendCt2Reserve128Env ct1Len)
                  (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len) FreeOnlyEvs))))))
        evs

/-- Pre-state-pinned allocator trace envelope for `<EkSentCt1Received>::recv_ct2_chunk`. -/
def EkSentCt1ReceivedRecvCt2ChunkEnv {F : ShaCompress}
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (epoch : Epoch) (chunk : Chunk)
    (evs : List AllocEvent) : Prop :=
  if epoch != s.uc.epoch then
    evs = []
  else
    let receivingCt2 := addChunkTotal s.receiving_ct2 chunk
    SeqEnv (AddChunkSlotsEnv s.receiving_ct2.pts)
      (SeqEnv (DecodedMessageEnv receivingCt2)
        (RecvCt2ChunkTailEnv s.uc.auth.rootKey.length s.uc.ct1.length
          (decodedMessageTotal receivingCt2)))
      evs

theorem recvCt2ChunkTail_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rootKeyLen ct1Len : Nat) (optCt2 : Option Bytes) :
    let n := optBytesLen optCt2
    PhaseCreditSpec M (RecvCt2ChunkTailEnv rootKeyLen ct1Len optCt2)
      (2 * n + 2 * rootKeyLen + 6 * ct1Len + 154814)
      (n + rootKeyLen + 3 * ct1Len + 132203)
      (n + rootKeyLen + 3 * ct1Len + 132203)
      (max n (max (rootKeyLen + 64) (2 * ct1Len + 254))) := by
  cases optCt2 with
  | none =>
    change PhaseCreditSpec M (RecvCt2ChunkTailEnv rootKeyLen ct1Len none)
      (2 * 0 + 2 * rootKeyLen + 6 * ct1Len + 154814)
      (0 + rootKeyLen + 3 * ct1Len + 132203)
      (0 + rootKeyLen + 3 * ct1Len + 132203)
      (max 0 (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)
  | some ct2Full =>
    change PhaseCreditSpec M (RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full))
      (2 * ct2Full.length + 2 * rootKeyLen + 6 * ct1Len + 154814)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 132203)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 132203)
      (max ct2Full.length (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)
    · have heq :
          RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) =
            SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
              (SeqEnv (· = rustAllocEvents 32 1)
                (SeqEnv (· = sliceConcat2Events 41)
                  (SeqEnv (· = rustAllocEvents 32 1)
                    (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                      (SeqEnv (SendCt2Reserve128Env ct1Len)
                        (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len) FreeOnlyEvs)))))) := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      have h1 :
          PhaseCreditSpec M (· = recvCt2AllocMacCt2Events ct2Full.length)
            (2 * ct2Full.length + 19334) (ct2Full.length + 16518) (ct2Full.length + 16518)
            (max ct2Full.length 128) := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            PhaseCreditSpec M
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
              (2 * (ct2Full.length - 128) + 9539) (ct2Full.length - 128 + 8195)
              (ct2Full.length - 128 + 8195) (ct2Full.length - 128) := by
          split
          · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
          · exact PhaseCreditSpec.rustAlloc_aff hM (req := ct2Full.length - 128) (al := 1)
              (by decide)
        have hb := PhaseCreditSpec.rustAlloc_aff hM (req := 128) (al := 1) (by decide)
        exact (PhaseCreditSpec.append_eq ha hb).mono (by omega) (by omega) (by omega) (by omega)
      have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
      have h3 := sliceConcat2Events_phaseCreditSpec hM 41
      have h4 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
      have h5 := authUpdate_phaseCreditSpec hM rootKeyLen 32
      have h6 := sendCt2Reserve128_phaseCreditSpec hM ct1Len
      have h7 :
          PhaseCreditSpec M (· = sendCt2ConcatHmacEvents ct1Len)
            (2 * ct1Len + 48485) (ct1Len + 41358) (ct1Len + 41358) (max (ct1Len + 171) 64) := by
        unfold sendCt2ConcatHmacEvents
        have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 35 + 8 + (ct1Len + 128)) (al := 1)
          (by decide)
        exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
          (by omega) (by omega) (by omega) (by omega)
      have h8 := PhaseCreditSpec.freeOnly_of_hyps hM
      exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))).mono
        (by omega) (by omega) (by omega) (by omega)

/-! ## Unified 12-Arm `<States>::recv` Envelope and Linear `rawV1State` Bounds -/

/-- Post-`decoded_message` tail envelope for `<Ct1Sampled>::recv_ek_chunk` and `<Ct1Acknowledged>::recv_ek_chunk`.
-/
def RecvEkChunkSendCt2TailEnv (sendCt2OnDone : Bool) (es : Bytes) (ct1Len : Nat) :
    Option Bytes → List AllocEvent → Prop
  | none, evs => FreeOnlyEvs evs
  | some ekBytes, evs =>
    if sendCt2OnDone && (ekBytes.length == 1184) then
      SeqEnv (UnchunkedSendCt2BySizesEnv es ct1Len)
        (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs)
        evs
    else
      FreeOnlyEvs evs

theorem recvEkChunkSendCt2Tail_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (sendCt2OnDone : Bool) (es : Bytes) (ct1Len : Nat) (optEk : Option Bytes) :
    PhaseCreditSpec M (RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len optEk)
      (6 * ct1Len + 259696)
      (3 * ct1Len + 208624)
      (3 * ct1Len + 218899)
      (max 2080 (2 * ct1Len + 254)) := by
  cases optEk with
  | none =>
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)
  | some ekBytes =>
    by_cases hcond : (sendCt2OnDone && (ekBytes.length == 1184)) = true
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) =
            SeqEnv (UnchunkedSendCt2BySizesEnv es ct1Len)
              (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs) := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      have h1 := unchunkedSendCt2BySizes_phaseCreditSpec hM es ct1Len
      have h2 := sendCt2Encoder_128_32_phaseCreditSpec hM
      have h3 := PhaseCreditSpec.freeOnly_of_hyps hM
      exact (h1.seq (h2.seq h3)).mono (by omega) (by omega) (by omega) (by omega)
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)

/-- Whether `msg.payload` triggers `<EkReceivedCt1Sampled>::send_ct2` in `<States>::recv`. -/
def isEkReceivedCt1AckMsg (msg : Message spqrPolyApi) : Bool :=
  match msg.payload with
  | .ct1Ack true => true
  | .ekCt1Ack _ => true
  | _ => false

/-- Pre-state-pinned allocator trace envelope for `<spqr::v1::chunked::states::States>::recv` across all 12 dispatch arms.
-/
def StatesRecvEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  match st with
  | .keysUnsampled _ => FreeOnlyEvs
  | .keysSampled s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct1 _ =>
        SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
          (SeqEnv (EncodeBytesEnv s.uc.ek.length) FreeOnlyEvs)
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .headerSent s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct1 chunk =>
        SeqEnv (AddChunkSlotsEnv s.receiving_ct1.pts)
          (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ct1 chunk)) FreeOnlyEvs)
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct1Received s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct2 _ =>
        SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ekSentCt1Received s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .ct2 chunk =>
        SeqEnv (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .noHeaderReceived s =>
    if msg.epoch == s.uc.epoch then
      match msg.payload with
      | .hdr chunk =>
        SeqEnv (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) FreeOnlyEvs
      | _ => FreeOnlyEvs
    else
      FreeOnlyEvs
  | .headerReceived _ => FreeOnlyEvs
  | .ct1Sampled s =>
    if msg.epoch == s.uc.epoch then
      let chunkAck? : Option (Chunk × Bool) := match msg.payload with
        | .ek chunk => some (chunk, false)
        | .ekCt1Ack chunk => some (chunk, true)
        | _ => none
      match chunkAck? with
      | none => FreeOnlyEvs
      | some (chunk, ack) =>
        let receivingEk := addChunkTotal s.receiving_ek chunk
        SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
          (SeqEnv (DecodedMessageEnv receivingEk)
            (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
              (decodedMessageTotal receivingEk)))
    else
      FreeOnlyEvs
  | .ekReceivedCt1Sampled s =>
    if msg.epoch == s.uc.epoch then
      if isEkReceivedCt1AckMsg msg then
        SeqEnv (UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length)
          (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs)
      else
        FreeOnlyEvs
    else
      FreeOnlyEvs
  | .ct1Acknowledged s =>
    if msg.epoch == s.uc.epoch then
      let chunk? : Option Chunk := match msg.payload with
        | .ek chunk => some chunk
        | .ekCt1Ack chunk => some chunk
        | _ => none
      match chunk? with
      | none => FreeOnlyEvs
      | some chunk =>
        let receivingEk := addChunkTotal s.receiving_ek chunk
        SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
          (SeqEnv (DecodedMessageEnv receivingEk)
            (RecvEkChunkSendCt2TailEnv true s.uc.es s.uc.ct1.length
              (decodedMessageTotal receivingEk)))
    else
      FreeOnlyEvs
  | .ct2Sampled _ => FreeOnlyEvs

def statesRecvDeltaCum {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  436 * rawV1State st.into_pb + 12000000

def statesRecvDeltaLive {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  374 * rawV1State st.into_pb + 10200000

def statesRecvDeltaPeak {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  374 * rawV1State st.into_pb + 10200000

/-- Tightened `Δlive` bound when `8195 ≤ smallMaxReq M` (keeping Lagrange interpolation temporaries in small classes).
-/
def statesRecvSmall8kDeltaLive {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  374 * rawV1State st.into_pb + 280000

def statesRecvSmall8kDeltaPeak {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  374 * rawV1State st.into_pb + 280000

def statesRecvMaxReq {F : ShaCompress} (st : States spqrPolyApi (spqrAuthApi F)) : Nat :=
  2 * rawV1State st.into_pb + 2080

theorem statesRecvEnv_nonempty {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs : List AllocEvent, StatesRecvEnv st msg evs := by
  have hFree : ∃ evs, FreeOnlyEvs evs := ⟨[], FreeOnlyEvs.nil⟩
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
    · exact hFree
  | ct1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      unfold EkSentCt1ReceivedRecvCt2ChunkEnv
      split
      · exact ⟨[], SeqEnv.inl rfl⟩
      · exact ⟨[], SeqEnv.inl (SeqEnv.inl (addChunkSlotsEnv_nil _))⟩
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      unfold NoHeaderReceivedRecvHdrChunkBodyEnv
      split
      · exact ⟨[], SeqEnv.inl rfl⟩
      · exact ⟨[], SeqEnv.inl (SeqEnv.inl (addChunkSlotsEnv_nil _))⟩
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> dsimp only <;>
        try exact hFree
      · exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
      · exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        refine ⟨(sendCt2Seg23Events s.uc.es ++ [] ++ sendCt2ConcatHmacEvents s.uc.ct1.length) ++ [],
          SeqEnv.inl ?_⟩
        exact ⟨_, [], rfl,
          ⟨_, _, rfl, ⟨_, [], rfl, rfl, Or.inl rfl⟩, rfl⟩,
          FreeOnlyEvs.nil⟩
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> dsimp only <;>
        try exact hFree
      · exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
      · exact ⟨[], SeqEnv.inl (addChunkSlotsEnv_nil _)⟩
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Regime-uniform `PhaseCreditSpec` for `StatesRecvEnv st msg` across all 12 dispatch arms under `ModelHyps M` and `StatesDecPtsNeededBound st`.
-/
theorem statesRecv_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseCreditSpec M (StatesRecvEnv st msg)
      (statesRecvDeltaCum st)
      (statesRecvDeltaLive st)
      (statesRecvDeltaPeak st)
      (statesRecvMaxReq st) := by
  have hFree :
      PhaseCreditSpec M FreeOnlyEvs
        (statesRecvDeltaCum st) (statesRecvDeltaLive st)
        (statesRecvDeltaPeak st) (statesRecvMaxReq st) :=
    (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      have h1 := addChunkSlots_replicate16_phaseCreditSpec hM
      have h2 := seq_freeOnly hM (encodeBytes_phaseCreditSpec hM s.uc.ek.length) (Nat.le_refl _)
      have hek : s.uc.ek.length ≤ rawV1State (States.keysSampled s).into_pb := by
        dsimp only [States.into_pb, KeysSampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.into_pb,
          rawV1State, rawInnerState, rawChKeysSampled, rawUcHeaderSent, optRaw]
        omega
      exact (h1.seq h2).mono
        (keysSampled_arm_le (by decide) hek (by decide))
        (keysSampled_live_le (by decide) hek (by decide))
        (keysSampled_peak_le (by decide) hek (by decide))
        (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct1
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_ct1.intoPb) ≤
              rawV1State (States.headerSent s).into_pb := by
          dsimp only [States.into_pb, HeaderSent.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChHeaderSent, optRaw]
          omega
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ct1.pts
        have h2 :
            PhaseCreditSpec M (SeqEnv (DecodedMessageEnv rCt1) FreeOnlyEvs)
              (19250 * 480 + 484694) (16476 * 480 + 413622) (16476 * 480 + 413622) 960 :=
          (seq_freeOnly hM
            (decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec hM (dec := rCt1) (by omega))
            (Nat.le_refl _)).mono
            (lin_const_cap hr_pts) (lin_const_cap hr_pts) (lin_const_cap hr_pts) (by omega)
        exact (h1.seq h2).mono
          (twoPhase_bound_le hraw hdec_le (by decide) (by decide) (by decide))
          (twoPhase_bound_le hraw hdec_le (by decide) (by decide) (by decide))
          (twoPhase_peak_le hraw hdec_le (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
      | _ => exact hFree
    · exact hFree
  | ct1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly hM (addChunkSlots_replicate16_phaseCreditSpec hM) (Nat.le_refl _)).mono
        (mono_const_le (by decide))
        (mono_const_le (by decide))
        (mono_const_le (by decide))
        (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct2
        have hsum_le :
            (s.uc.auth.rootKey.length + s.uc.ct1.length) +
              rawPolyDec (protoPolyDecoderToPb s.receiving_ct2.intoPb) ≤
              rawV1State (States.ekSentCt1Received s).into_pb := by
          dsimp only [States.into_pb, EkSentCt1Received.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb,
            spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
            rawV1State, rawInnerState, rawChEkSentCt1Received, rawUcEkSentCt1Received,
            rawAuth, optRaw]
          omega
        have hbody :
            PhaseCreditSpec M (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk)
              (statesRecvDeltaCum (.ekSentCt1Received s))
              (statesRecvDeltaLive (.ekSentCt1Received s))
              (statesRecvDeltaPeak (.ekSentCt1Received s))
              (statesRecvMaxReq (.ekSentCt1Received s)) := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact (PhaseCreditSpec.nil M).mono
              (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ct2.pts
            have h2 :
                PhaseCreditSpec M (DecodedMessageEnv rCt2)
                  (19250 * 80 + 484694) (16476 * 80 + 413622) (16476 * 80 + 413622) 256 :=
              (decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec hM (dec := rCt2) (by omega)).mono
                (lin_const_cap hr_pts) (lin_const_cap hr_pts) (lin_const_cap hr_pts) (by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 :
                PhaseCreditSpec M
                  (RecvCt2ChunkTailEnv s.uc.auth.rootKey.length s.uc.ct1.length
                    (decodedMessageTotal rCt2))
                  (6 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (2 * 160 + 154814))
                  (3 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (160 + 132203))
                  (3 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (160 + 132203))
                  (2 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + 254) :=
              (recvCt2ChunkTail_phaseCreditSpec hM
                s.uc.auth.rootKey.length s.uc.ct1.length (decodedMessageTotal rCt2)).mono
                (ct2Tail_cum_cap hn160) (ct2Tail_live_cap hn160) (ct2Tail_live_cap hn160)
                (by omega)
            exact (h1.seq (h2.seq h3)).mono
              (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (by unfold statesRecvMaxReq; omega)
        exact seq_freeOnly hM hbody (Nat.le_refl _)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤
              rawV1State (States.noHeaderReceived s).into_pb := by
          dsimp only [States.into_pb, NoHeaderReceived.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChNoHeaderReceived, optRaw]
          omega
        have hbody := seq_freeOnly hM
          (noHeaderReceivedRecvHdrChunkBody_phaseCreditSpec hM s msg.epoch chunk hpts)
          (Nat.le_refl _)
        exact hbody.mono
          (mono_lin_same_le hdec_le (by decide))
          (mono_lin_same_le hdec_le (by decide))
          (mono_lin_same_le hdec_le (by decide))
          (by unfold statesRecvMaxReq; omega)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound] at hpts
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      have hsum_le :
          s.uc.ct1.length + rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤
            rawV1State (States.ct1Sampled s).into_pb := by
        dsimp only [States.into_pb, Ct1Sampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Sampled, rawUcCt1Sent, optRaw]
        omega
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec M
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            (statesRecvDeltaCum (States.ct1Sampled s))
            (statesRecvDeltaLive (States.ct1Sampled s))
            (statesRecvDeltaPeak (States.ct1Sampled s))
            (statesRecvMaxReq (States.ct1Sampled s)) := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ek.pts
        have h2 :
            PhaseCreditSpec M (DecodedMessageEnv rEk)
              (19250 * 576 + 484694) (16476 * 576 + 413622) (16476 * 576 + 413622) 1152 :=
          (decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec hM (dec := rEk) hr_pts).mono
            (lin_const_cap hr_pts) (lin_const_cap hr_pts) (lin_const_cap hr_pts) (by omega)
        have h3 := recvEkChunkSendCt2Tail_phaseCreditSpec hM ack s.uc.es s.uc.ct1.length
          (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        have hct1_le :
            s.uc.ct1.length ≤ rawV1State (States.ekReceivedCt1Sampled s).into_pb := by
          dsimp only [States.into_pb, EkReceivedCt1Sampled.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.into_pb,
            rawV1State, rawInnerState, rawChEkReceivedCt1Sampled, rawUcCt1SentEkReceived, optRaw]
          omega
        have h1 := unchunkedSendCt2BySizes_phaseCreditSpec hM s.uc.es s.uc.ct1.length
        have h2 := seq_freeOnly hM (sendCt2Encoder_128_32_phaseCreditSpec hM) (Nat.le_refl _)
        exact (h1.seq h2).mono
          (sendCt2_enc_add_le (by decide) hct1_le (by decide))
          (sendCt2_enc_add_le (by decide) hct1_le (by decide))
          (sendCt2_enc_peak_le (by decide) hct1_le (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound] at hpts
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      have hsum_le :
          s.uc.ct1.length + rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤
            rawV1State (States.ct1Acknowledged s).into_pb := by
        dsimp only [States.into_pb, Ct1Acknowledged.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Acknowledged, rawUcCt1Sent, optRaw]
        omega
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ek.pts
        have h2 :
            PhaseCreditSpec M (DecodedMessageEnv rEk)
              (19250 * 576 + 484694) (16476 * 576 + 413622) (16476 * 576 + 413622) 1152 :=
          (decodedMessage_ptsNeeded_le_576_aff_phaseCreditSpec hM (dec := rEk) hr_pts).mono
            (lin_const_cap hr_pts) (lin_const_cap hr_pts) (lin_const_cap hr_pts) (by omega)
        have h3 := recvEkChunkSendCt2Tail_phaseCreditSpec hM true s.uc.es s.uc.ct1.length
          (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Tightened `PhaseCreditSpec` for `StatesRecvEnv st msg` when `8195 ≤ smallMaxReq M` (`cLive = cPeak = 280,000`).
-/
theorem statesRecv_small8k_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hsmall8k : 8195 ≤ HasFineReallocCredit.smallMaxReq M)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseCreditSpec M (StatesRecvEnv st msg)
      (statesRecvDeltaCum st)
      (statesRecvSmall8kDeltaLive st)
      (statesRecvSmall8kDeltaPeak st)
      (statesRecvMaxReq st) := by
  have hFree :
      PhaseCreditSpec M FreeOnlyEvs
        (statesRecvDeltaCum st) (statesRecvSmall8kDeltaLive st)
        (statesRecvSmall8kDeltaPeak st) (statesRecvMaxReq st) :=
    (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      have h1 := addChunkSlots_replicate16_phaseCreditSpec hM
      have h2 := seq_freeOnly hM (encodeBytes_phaseCreditSpec hM s.uc.ek.length) (Nat.le_refl _)
      have hek : s.uc.ek.length ≤ rawV1State (States.keysSampled s).into_pb := by
        dsimp only [States.into_pb, KeysSampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.into_pb,
          rawV1State, rawInnerState, rawChKeysSampled, rawUcHeaderSent, optRaw]
        omega
      exact (h1.seq h2).mono
        (keysSampled_arm_le (by decide) hek (by decide))
        (keysSampled_live_le (by decide) hek (by decide))
        (keysSampled_peak_le (by decide) hek (by decide))
        (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct1
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_ct1.intoPb) ≤
              rawV1State (States.headerSent s).into_pb := by
          dsimp only [States.into_pb, HeaderSent.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChHeaderSent, optRaw]
          omega
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ct1.pts
        have h2 :
            PhaseCreditSpec M (SeqEnv (DecodedMessageEnv rCt1) FreeOnlyEvs)
              (19250 * 480 + 484694) 0 0 960 :=
          (seq_freeOnly hM
            (decodedMessage_ptsNeeded_le_576_phaseCreditSpec hM (dec := rCt1) (by omega) hsmall8k)
            (Nat.le_refl 0)).mono
            (lin_const_cap hr_pts) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        exact (h1.seq h2).mono
          (twoPhase_bound_le hraw hdec_le (by decide) (by decide) (by decide))
          (twoPhase_bound_le hraw hdec_le (by decide) (by decide) (by decide))
          (twoPhase_peak_le hraw hdec_le (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
      | _ => exact hFree
    · exact hFree
  | ct1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly hM (addChunkSlots_replicate16_phaseCreditSpec hM) (Nat.le_refl _)).mono
        (mono_const_le (by decide))
        (mono_const_le (by decide))
        (mono_const_le (by decide))
        (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct2
        have hsum_le :
            (s.uc.auth.rootKey.length + s.uc.ct1.length) +
              rawPolyDec (protoPolyDecoderToPb s.receiving_ct2.intoPb) ≤
              rawV1State (States.ekSentCt1Received s).into_pb := by
          dsimp only [States.into_pb, EkSentCt1Received.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb,
            spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
            rawV1State, rawInnerState, rawChEkSentCt1Received, rawUcEkSentCt1Received,
            rawAuth, optRaw]
          omega
        have hbody :
            PhaseCreditSpec M (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk)
              (statesRecvDeltaCum (.ekSentCt1Received s))
              (statesRecvSmall8kDeltaLive (.ekSentCt1Received s))
              (statesRecvSmall8kDeltaPeak (.ekSentCt1Received s))
              (statesRecvMaxReq (.ekSentCt1Received s)) := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact (PhaseCreditSpec.nil M).mono
              (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ct2.pts
            have h2 :
                PhaseCreditSpec M (DecodedMessageEnv rCt2) (19250 * 80 + 484694) 0 0 256 :=
              (decodedMessage_ptsNeeded_le_576_phaseCreditSpec hM
                (dec := rCt2) (by omega) hsmall8k).mono
                (lin_const_cap hr_pts) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 :
                PhaseCreditSpec M
                  (RecvCt2ChunkTailEnv s.uc.auth.rootKey.length s.uc.ct1.length
                    (decodedMessageTotal rCt2))
                  (6 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (2 * 160 + 154814))
                  (3 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (160 + 132203))
                  (3 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + (160 + 132203))
                  (2 * (s.uc.auth.rootKey.length + s.uc.ct1.length) + 254) :=
              (recvCt2ChunkTail_phaseCreditSpec hM
                s.uc.auth.rootKey.length s.uc.ct1.length (decodedMessageTotal rCt2)).mono
                (ct2Tail_cum_cap hn160) (ct2Tail_live_cap hn160) (ct2Tail_live_cap hn160)
                (by omega)
            exact (h1.seq (h2.seq h3)).mono
              (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
              (by unfold statesRecvMaxReq; omega)
        exact seq_freeOnly hM hbody (Nat.le_refl _)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound] at hpts
        have hraw := rawPolyDec_intoPb_eq s.receiving_hdr
        have hdec_le :
            0 + rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤
              rawV1State (States.noHeaderReceived s).into_pb := by
          dsimp only [States.into_pb, NoHeaderReceived.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChNoHeaderReceived, optRaw]
          omega
        have hbody :
            PhaseCreditSpec M (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk)
              (statesRecvDeltaCum (.noHeaderReceived s))
              (statesRecvSmall8kDeltaLive (.noHeaderReceived s))
              (statesRecvSmall8kDeltaPeak (.noHeaderReceived s))
              (statesRecvMaxReq (.noHeaderReceived s)) := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseCreditSpec.nil M).mono
              (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 48 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_hdr.pts
            have h2 :
                PhaseCreditSpec M (DecodedMessageEnv rHdr) (19250 * 48 + 484694) 0 0 256 :=
              (decodedMessage_ptsNeeded_le_576_phaseCreditSpec hM
                (dec := rHdr) (by omega) hsmall8k).mono
                (lin_const_cap hr_pts) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
            have hn96 : optBytesLen (decodedMessageTotal rHdr) ≤ 96 := by
              have := optBytesLen_decodedMessageTotal_le rHdr; omega
            have h3 :
                PhaseCreditSpec M (RecvHdrChunkTailEnv (decodedMessageTotal rHdr))
                  (0 * 0 + (2 * 96 + 67559)) (0 * 0 + (96 + 57746)) (0 * 0 + (96 + 57746)) 105 :=
              (recvHdrChunkTail_phaseCreditSpec hM (decodedMessageTotal rHdr)).mono
                (by rw [Nat.zero_mul, Nat.zero_add]; exact lin_const_cap hn96)
                (by rw [Nat.zero_mul, Nat.zero_add]; exact id_const_cap hn96)
                (by rw [Nat.zero_mul, Nat.zero_add]; exact id_const_cap hn96)
                (by omega)
            exact (h1.seq (h2.seq h3)).mono
              (threePhase_bound_le hraw hdec_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_bound_le hraw hdec_le (by decide) (by decide) (by decide) (by decide))
              (threePhase_peak_le hraw hdec_le (by decide) (by decide) (by decide) (by decide))
              (by unfold statesRecvMaxReq; omega)
        exact seq_freeOnly hM hbody (Nat.le_refl _)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound] at hpts
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      have hsum_le :
          s.uc.ct1.length + rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤
            rawV1State (States.ct1Sampled s).into_pb := by
        dsimp only [States.into_pb, Ct1Sampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Sampled, rawUcCt1Sent, optRaw]
        omega
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec M
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            (statesRecvDeltaCum (States.ct1Sampled s))
            (statesRecvSmall8kDeltaLive (States.ct1Sampled s))
            (statesRecvSmall8kDeltaPeak (States.ct1Sampled s))
            (statesRecvMaxReq (States.ct1Sampled s)) := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ek.pts
        have h2 :
            PhaseCreditSpec M (DecodedMessageEnv rEk) (19250 * 576 + 484694) 0 0 1152 :=
          (decodedMessage_ptsNeeded_le_576_phaseCreditSpec hM (dec := rEk) hr_pts hsmall8k).mono
            (lin_const_cap hr_pts) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have h3 := recvEkChunkSendCt2Tail_phaseCreditSpec hM ack s.uc.es s.uc.ct1.length
          (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        have hct1_le :
            s.uc.ct1.length ≤ rawV1State (States.ekReceivedCt1Sampled s).into_pb := by
          dsimp only [States.into_pb, EkReceivedCt1Sampled.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.into_pb,
            rawV1State, rawInnerState, rawChEkReceivedCt1Sampled, rawUcCt1SentEkReceived, optRaw]
          omega
        have h1 := unchunkedSendCt2BySizes_phaseCreditSpec hM s.uc.es s.uc.ct1.length
        have h2 := seq_freeOnly hM (sendCt2Encoder_128_32_phaseCreditSpec hM) (Nat.le_refl _)
        exact (h1.seq h2).mono
          (sendCt2_enc_add_le (by decide) hct1_le (by decide))
          (sendCt2_enc_add_le (by decide) hct1_le (by decide))
          (sendCt2_enc_peak_le (by decide) hct1_le (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound] at hpts
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      have hsum_le :
          s.uc.ct1.length + rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤
            rawV1State (States.ct1Acknowledged s).into_pb := by
        dsimp only [States.into_pb, Ct1Acknowledged.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Acknowledged, rawUcCt1Sent, optRaw]
        omega
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_phaseCreditSpec hM s.receiving_ek.pts
        have h2 :
            PhaseCreditSpec M (DecodedMessageEnv rEk) (19250 * 576 + 484694) 0 0 1152 :=
          (decodedMessage_ptsNeeded_le_576_phaseCreditSpec hM (dec := rEk) hr_pts hsmall8k).mono
            (lin_const_cap hr_pts) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have h3 := recvEkChunkSendCt2Tail_phaseCreditSpec hM true s.uc.es s.uc.ct1.length
          (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_bound_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (threePhase_peak_le hraw hsum_le (by decide) (by decide) (by decide) (by decide))
          (by unfold statesRecvMaxReq; omega)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- `States.from_pb` corollary of `statesRecv_phaseCreditSpec`. -/
theorem statesRecv_of_from_pb_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    PhaseCreditSpec M (StatesRecvEnv st msg)
      (statesRecvDeltaCum st)
      (statesRecvDeltaLive st)
      (statesRecvDeltaPeak st)
      (statesRecvMaxReq st) :=
  statesRecv_phaseCreditSpec hM st msg (StatesDecPtsNeededBound.of_from_pb hfrom)

theorem statesRecv_small8k_of_from_pb_phaseCreditSpec {F : ShaCompress}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (hsmall8k : 8195 ≤ HasFineReallocCredit.smallMaxReq M)
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    PhaseCreditSpec M (StatesRecvEnv st msg)
      (statesRecvDeltaCum st)
      (statesRecvSmall8kDeltaLive st)
      (statesRecvSmall8kDeltaPeak st)
      (statesRecvMaxReq st) :=
  statesRecv_small8k_phaseCreditSpec hM hsmall8k st msg (StatesDecPtsNeededBound.of_from_pb hfrom)

/-! ## Concrete `fineCostModel` Instantiation and `FitsEnv` Bounds -/

theorem statesRecv_fineCostModel_phaseCreditSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      (statesRecvDeltaCum st)
      (statesRecvSmall8kDeltaLive st)
      (statesRecvSmall8kDeltaPeak st)
      (statesRecvMaxReq st) := by
  refine statesRecv_small8k_phaseCreditSpec fineCostModel_modelHyps ?_ st msg hpts
  rw [fineCostModel_smallMaxReq_eq]
  decide

/-- `FitsEnv fineCostModel` bound under `nonVacLimits` when `StatesDecPtsNeededBound st` and `rawV1State st.into_pb ≤ 60,000`.
-/
theorem statesRecv_fineCostModel_fitsEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st)
    (hraw : rawV1State st.into_pb ≤ 60000) :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init (StatesRecvEnv st msg) := by
  have hSpec :
      PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
        38160000 22720000 22720000 122080 :=
    (statesRecv_fineCostModel_phaseCreditSpec st msg hpts).mono
      (by unfold statesRecvDeltaCum; omega)
      (by unfold statesRecvSmall8kDeltaLive; omega)
      (by unfold statesRecvSmall8kDeltaPeak; omega)
      (by unfold statesRecvMaxReq; omega)
  have hstep : fineStepReserveOfCum 122080 16 38160000 = 427425792 := by
    unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    omega
  have hdyn : fineDynIvsOfCum 38160000 = 322361 := by
    unfold fineDynIvsOfCum fineMaxMetaAreasOfCum fineMaxGroupsOfCum
    omega
  have hsc : nonVacLimits.staticCount = 16 := rfl
  have hsb : nonVacLimits.staticBytes = 16 * 1024 * 1024 := rfl
  have hcap : nonVacLimits.physCap = 2 ^ 30 := rfl
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (Nat.le_refl _) rfl ?_ ?_
  · rw [hsb, hcap, hstep]
    omega
  · rw [hsc, hsb, hdyn, hstep]
    unfold MMAP_MIN_ADDR PAGE_SIZE
    omega

-- Non-vacuity witness: active `.keysSampled` state receiving a `.ct1` chunk fits within `nonVacLimits`.
example (F : ShaCompress) :
    let st : States spqrPolyApi (spqrAuthApi F) :=
      .keysSampled {
        uc := {
          epoch := 1#64
          auth := { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 }
          ek := List.replicate 1184 0#8
          dk := List.replicate 2400 0#8
        }
        sending_hdr := { idx := 0#32, s := .points [] }
      }
    let msg : Message spqrPolyApi :=
      { epoch := 1#64, payload := .ct1 { data := List.Vector.replicate 32 0#8, index := 0#16 } }
    (∃ evs : List AllocEvent, StatesRecvEnv st msg evs ∧ 0 < evs.length) ∧
      FitsEnv fineCostModel nonVacLimits fineCostModel.init (StatesRecvEnv st msg) := by
  intro st msg
  refine ⟨?_, ?_⟩
  · refine ⟨rustAllocEvents 16 2 ++ (List.replicate 16 (rustAllocEvents 1184 2)).flatten, ?_, ?_⟩
    · dsimp only [st, msg, StatesRecvEnv, beq_self_eq_true, ↓reduceIte]
      rw [List.length_replicate]
      refine SeqEnv.append ?_ (SeqEnv.inl ?_)
      · exact Or.inr ⟨rustAllocEvents 16 2, [], by simp, Or.inr rfl, addChunkSlotsEnv_nil _⟩
      · unfold EncodeBytesEnv encodeBytesAllocEvents
        simp only [show (1184 ≤ 1048576 ∧ 1184 % 2 = 0 ∧ 0 < 1184) from by decide,
          and_self, ite_true]
    · rw [List.length_append]
      have hlen1 : (rustAllocEvents 16 2).length = 1 := rfl
      omega
  · refine statesRecv_fineCostModel_fitsEnv st msg trivial ?_
    dsimp only [st, States.into_pb, KeysSampled.into_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.into_pb,
      spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
      CryptoVerification.LibsignalSpqrV1.PolyEncoder.intoPb,
      CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb,
      rawV1State, rawInnerState, rawChKeysSampled, rawUcHeaderSent, rawAuth,
      CryptoVerification.SpqrV1.Top.StateSize.rawPolyEnc, optRaw]
    simp only [List.length_replicate, List.map_nil, List.sum_nil]
    omega

/-! ## Protocol-Sized Tight `fineCostModel` Credit, Group, and `FitsEnv` Specs -/

private theorem addChunkLoopTotal_pts_length_eq (chunk : Chunk) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      (addChunkLoopTotal chunk i rem self).pts.length = self.pts.length
  | 0, _, _ => rfl
  | rem + 1, i, self => by
    unfold addChunkLoopTotal
    dsimp only
    rw [addChunkLoopTotal_pts_length_eq chunk rem (i + 1)]
    split
    · simp
    · rfl

/-- `addChunkTotal` preserves `pts.length` unconditionally. -/
theorem addChunkTotal_pts_length_uncond (self : PolyDecoder) (chunk : Chunk) :
    (addChunkTotal self chunk).pts.length = self.pts.length :=
  addChunkLoopTotal_pts_length_eq chunk 16 0 self

theorem addChunkTotal_pts_length {self : PolyDecoder} (chunk : Chunk)
    (hlen : self.pts.length = 16) :
    (addChunkTotal self chunk).pts.length = 16 :=
  (addChunkTotal_pts_length_uncond self chunk).trans hlen

private theorem decodeDecoderPbPts_length :
    ∀ (bss : List (List (BitVec 8))) (out : List SortedSetPt),
      PolyDecoder.decodeDecoderPbPts bss = .ok (.ok out) →
      out.length = bss.length
  | [], out, h => by
    have hinj := Except.ok.inj (Except.ok.inj h)
    subst hinj
    rfl
  | bs :: rest, out, h => by
    unfold PolyDecoder.decodeDecoderPbPts at h
    split at h
    · simp [Pure.pure, Except.pure] at h
    · rcases except_bind_eq_ok h with ⟨v, _, h2⟩
      rcases except_bind_eq_ok h2 with ⟨tailRes, htail, h3⟩
      cases tailRes with
      | error _ => simp [Pure.pure, Except.pure] at h3
      | ok tail =>
        have hinj := Except.ok.inj (Except.ok.inj h3)
        subst hinj
        simp [decodeDecoderPbPts_length rest tail htail]

theorem polyDecoder_fromPb_pts_length_16 {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    dec.pts.length = 16 := by
  unfold PolyDecoder.fromPb pbToProtoPolyDecoder at h
  split at h
  · simp [Pure.pure, Except.pure] at h
  · rename_i hfls
    have hlen16 : pb.pts.length = 16 :=
      bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hfls)
    rcases except_bind_eq_ok h with ⟨ptsRes, hpts, h2⟩
    cases ptsRes with
    | error _ => simp [Pure.pure, Except.pure] at h2
    | ok outPts =>
      have hinj := Except.ok.inj (Except.ok.inj h2)
      subst hinj
      exact (decodeDecoderPbPts_length pb.pts outPts hpts).trans hlen16

/-- Every `PolyDecoder` decoded via `decoderFromPbStateDecode` has `dec.pts.length = 16`. -/
theorem decoderFromPbStateDecode_pts_length_16 {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    dec.pts.length = 16 := by
  unfold decoderFromPbStateDecode spqrPolyApi at h
  cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok res := by
      dsimp only [StatesResult.ofPanic] at h1
      cases hr : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) with
      | error _ => rw [hr] at h1; contradiction
      | ok v =>
        rw [hr] at h1
        simp only [Except.mapError, Except.ok.injEq] at h1
        subst h1
        rfl
    cases res with
    | error _ => contradiction
    | ok dec' =>
      have hinj := Except.ok.inj h2
      subst hinj
      exact polyDecoder_fromPb_pts_length_16 h1'

/-- Protocol field-size invariant (`dec.pts.length = 16`, `ek.length = 1152`, `ct1.length = 960`) established by `States.from_pb`.
-/
def StatesProtocolSizes {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => s.uc.ek.length = 1152
  | .headerSent s => s.receiving_ct1.pts.length = 16
  | .ct1Received _ => True
  | .ekSentCt1Received s => s.receiving_ct2.pts.length = 16 ∧ s.uc.ct1.length = 960
  | .noHeaderReceived s => s.receiving_hdr.pts.length = 16
  | .headerReceived _ => True
  | .ct1Sampled s => s.receiving_ek.pts.length = 16 ∧ s.uc.ct1.length = 960
  | .ekReceivedCt1Sampled s => s.uc.ct1.length = 960
  | .ct1Acknowledged s => s.receiving_ek.pts.length = 16 ∧ s.uc.ct1.length = 960
  | .ct2Sampled _ => True

private theorem ucHeaderSent_from_pb_ek_len {F : ShaCompress}
    {pb : V1State.Unchunked.HeaderSent}
    {s : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent (spqrAuthApi F)}
    (h : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.from_pb
      (spqrAuthApi F) pb = .ok s) :
    s.ek.length = 1152 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hcond
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · cases Except.ok.inj h
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2

private theorem ucEkSentCt1Received_from_pb_ct1_len {F : ShaCompress}
    {pb : V1State.Unchunked.EkSentCt1Received}
    {s : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)}
    (h : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb
      (spqrAuthApi F) pb = .ok s) :
    s.ct1.length = 960 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hcond
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · cases Except.ok.inj h
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2

private theorem ucCt1Sent_from_pb_ct1_len {F : ShaCompress}
    {pb : V1State.Unchunked.Ct1Sent}
    {s : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (h : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb
      (spqrAuthApi F) pb = .ok s) :
    s.ct1.length = 960 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hcond
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · cases Except.ok.inj h
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2

private theorem ucCt1SentEkReceived_from_pb_ct1_len {F : ShaCompress}
    {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    (h : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.from_pb
      (spqrAuthApi F) pb = .ok s) :
    s.ct1.length = 960 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hcond
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · cases Except.ok.inj h
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcond).1).2

/-- `States.from_pb` establishes `StatesProtocolSizes`. -/
theorem StatesProtocolSizes.of_from_pb {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    StatesProtocolSizes st := by
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    cases inner with
    | keysUnsampled _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      cases Except.ok.inj h
      trivial
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold KeysSampled.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
        cases Except.ok.inj hv3
        exact ucHeaderSent_from_pb_ek_len huc'
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold HeaderSent.from_pb at hv
      cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hv; dsimp only [Bind.bind, Except.bind] at hv
        cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
          rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩; contradiction
      | some d =>
        rw [hrec] at hv; dsimp only at hv
        split at hv
        · contradiction
        · cases huc : s.uc with
          | none => rw [huc] at hv; contradiction
          | some u =>
            rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
            rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
            rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
            rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩
            cases Except.ok.inj hv4
            exact decoderFromPbStateDecode_pts_length_16 hdec
    | ct1Received _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      cases Except.ok.inj h
      trivial
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold EkSentCt1Received.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        cases hrec : s.receivingCt2 with
        | none =>
          rw [hrec] at hv; dsimp only at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
          simp [decoderFromPbStateDecode] at hv2
        | some d =>
          rw [hrec] at hv; dsimp only at hv
          split at hv
          · contradiction
          · rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
            rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
            cases Except.ok.inj hv3
            exact ⟨decoderFromPbStateDecode_pts_length_16 hdec,
              ucEkSentCt1Received_from_pb_ct1_len huc'⟩
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold NoHeaderReceived.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        cases hrec : s.receivingHdr with
        | none =>
          rw [hrec] at hv; dsimp only at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
          simp [decoderFromPbStateDecode] at hv2
        | some d =>
          rw [hrec] at hv; dsimp only at hv
          split at hv
          · contradiction
          · rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
            rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
            cases Except.ok.inj hv3
            exact decoderFromPbStateDecode_pts_length_16 hdec
    | headerReceived _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      cases Except.ok.inj h
      trivial
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold Ct1Sampled.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        cases hrec : s.receivingEk with
        | none =>
          rw [hrec] at hv; dsimp only at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
          rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
          simp [decoderFromPbStateDecode] at hv3
        | some d =>
          rw [hrec] at hv; dsimp only at hv
          split at hv
          · contradiction
          · rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
            rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
            rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩
            cases Except.ok.inj hv4
            exact ⟨decoderFromPbStateDecode_pts_length_16 hdec, ucCt1Sent_from_pb_ct1_len huc'⟩
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold EkReceivedCt1Sampled.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩
        cases Except.ok.inj hv3
        exact ucCt1SentEkReceived_from_pb_ct1_len huc'
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      rename_i v hv
      cases Except.ok.inj h
      unfold Ct1Acknowledged.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        cases hrec : s.receivingEk with
        | none =>
          rw [hrec] at hv; dsimp only at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩
          simp [decoderFromPbStateDecode] at hv2
        | some d =>
          rw [hrec] at hv; dsimp only at hv
          split at hv
          · contradiction
          · rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
            rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
            cases Except.ok.inj hv3
            exact ⟨decoderFromPbStateDecode_pts_length_16 hdec, ucCt1Sent_from_pb_ct1_len huc'⟩
    | ct2Sampled _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> [contradiction; skip]
      cases Except.ok.inj h
      trivial

/-- Tight `Δcum` bound (`1,647,247` bytes) for `<States>::recv` on `fineCostModel`. -/
def statesRecvTightDeltaCum : Nat := 1647247

/-- Conservative `Δcum` bound (`5,335,951` bytes) without assuming `ptsNeeded ≥ 32`. -/
def statesRecvTightAnyKDeltaCum : Nat := 5335951

/-- Exact sub-phase sum (`1,435,018` bytes) under the 576-point per-slot cap. -/
def statesRecvTightExactDeltaCum : Nat := 1435018

def statesRecvTightDeltaLive : Nat := 0

def statesRecvTightDeltaPeak : Nat := 0

def statesRecvTightMaxReq : Nat := 4608

def statesRecvTightRawMaxReq : Nat := 93776

/-- `FineScale`-scaled slot-group bound (`3 * FineScale * 1244`, `3,732` groups) for `<States>::recv`.
-/
def statesRecvTightGroupS : Nat := 3 * FineScale * 1244

theorem statesRecvTightExactDeltaCum_eq :
    statesRecvTightExactDeltaCum = 206800 + 1022346 + 205872 := rfl

theorem statesRecvTightExactDeltaCum_le :
    statesRecvTightExactDeltaCum ≤ statesRecvTightDeltaCum := by decide

theorem statesRecvTightDeltaCum_le_anyK :
    statesRecvTightDeltaCum ≤ statesRecvTightAnyKDeltaCum := by decide

/-- Per-slot point-count cap (`s.vec.length ≤ cap`) and 32-byte `rootKey` bound on active `PolyDecoder` states.
-/
def StatesDecSlotCap {F : ShaCompress} (cap : Nat) : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled _ => True
  | .headerSent s => ∀ sl ∈ s.receiving_ct1.pts, sl.vec.length ≤ cap
  | .ct1Received _ => True
  | .ekSentCt1Received s =>
    (∀ sl ∈ s.receiving_ct2.pts, sl.vec.length ≤ cap) ∧ s.uc.auth.rootKey.length ≤ 32
  | .noHeaderReceived s => ∀ sl ∈ s.receiving_hdr.pts, sl.vec.length ≤ cap
  | .headerReceived _ => True
  | .ct1Sampled s => ∀ sl ∈ s.receiving_ek.pts, sl.vec.length ≤ cap
  | .ekReceivedCt1Sampled _ => True
  | .ct1Acknowledged s => ∀ sl ∈ s.receiving_ek.pts, sl.vec.length ≤ cap
  | .ct2Sampled _ => True

private theorem sliceConcat2Events_fine_le_44 {n : Nat} (hn : n ≤ 44) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) 738 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (smallAllocCost_le_738_of_le_44 hn) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

private theorem sliceConcat2Events_fine_le_74 {n : Nat} (hn : n ≤ 74) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) 1607 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (fineSmallAllocCost_le_1607_of_le_74 hn) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

private theorem sliceConcat2Events_fine_le_1280 {n : Nat} (hn : n ≤ 1280) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) 9789 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (fineSmallAllocCost_le_9789_of_le_1280 hn) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

private theorem sliceConcat2Events_fine_two_mul {n : Nat} (hsm_in : n ≤ 135167) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) (2 * n + 9539) 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; exact hsm_in
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (smallAllocCost_le_two_mul_add n) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

theorem sendCt2EncoderGrow_fine_128_32_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (SendCt2EncoderGrowEnv 128 32) 9789 0 0 296 := by
  refine { req_align := ?_, credit_le := ?_ }
  · rintro evs (⟨_, rfl⟩ | ⟨newCap, hlo, hhi, rfl⟩)
    · intro ev hev; nomatch hev
    · have h296 : newCap ≤ 296 := by omega
      have hsm : newCap ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      split
      · exact ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := newCap) (al := 1) (by decide) hsm).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) h296).req_align _ rfl
      · exact ((PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
          (old := 128) (new := newCap) (al := 1) (by decide) hlo hsm).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) h296).req_align _ rfl
  · rintro st0 evs (⟨_, rfl⟩ | ⟨newCap, hlo, hhi, rfl⟩)
    · exact ((PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le 9789) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le 296)).credit_le st0 rfl
    · have h296 : newCap ≤ 296 := by omega
      have hsm : newCap ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; omega
      split
      · have hc := fineSmallAllocCost_le_9789_of_le_1280 (req := newCap) (by omega)
        exact ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := newCap) (al := 1) (by decide) hsm).mono
          hc (Nat.le_refl 0) (Nat.le_refl 0) h296).credit_le st0 rfl
      · have hc := fineSmallReallocCost_le_9789_of_le_296 h296
        exact ((PhaseCreditSpec.rustRealloc_small_exact fineCostModel_modelHyps
          (old := 128) (new := newCap) (al := 1) (by decide) hlo hsm).mono
          hc (Nat.le_refl 0) (Nat.le_refl 0) h296).credit_le st0 rfl

theorem sendCt2Encoder_fine_128_32_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (SendCt2EncoderEnv 128 32) 165770 0 0 296 := by
  unfold SendCt2EncoderEnv
  have h1 := sliceConcat2Events_fine_le_1280 (n := 128) (by decide)
  have h2 := sendCt2EncoderGrow_fine_128_32_phaseCreditSpec
  have h3 := encodeBytes_fine_160_phaseCreditSpec
  have h4 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (h1.seq (h2.seq (h3.seq h4))).mono
    (by decide) (by decide) (by decide) (by decide)

theorem unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec
    (es : Bytes) {ct1Len : Nat} (hct1 : ct1Len ≤ 1088) :
    PhaseCreditSpec fineCostModel (UnchunkedSendCt2BySizesEnv es ct1Len) 40102 0 0 2430 := by
  unfold UnchunkedSendCt2BySizesEnv
  have hSeg23 := sendCt2Seg23_fine_phaseCreditSpec es
  have hRes := sendCt2Reserve128_fine_le_1088_phaseCreditSpec hct1
  have hConcatHmac :
      PhaseCreditSpec fineCostModel (· = sendCt2ConcatHmacEvents ct1Len) 15348 0 0 1280 := by
    unfold sendCt2ConcatHmacEvents
    have hsm : 35 + 8 + (ct1Len + 128) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 35 + 8 + (ct1Len + 128)) (al := 1) (by decide) hsm).mono
      (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
      (Nat.le_refl 0) (Nat.le_refl 0) (show 35 + 8 + (ct1Len + 128) ≤ 1280 by omega)
    exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
      (by decide) (by decide) (by decide) (by decide)
  exact (((hSeg23.concat hRes).concat hConcatHmac).concat
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by decide) (by decide) (by decide) (by decide)

theorem recvEkChunkSendCt2Tail_fine_le_1088_phaseCreditSpec
    (sendCt2OnDone : Bool) (es : Bytes) {ct1Len : Nat} (hct1 : ct1Len ≤ 1088)
    (optEk : Option Bytes) :
    PhaseCreditSpec fineCostModel (RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len optEk)
      205872 0 0 2430 := by
  cases optEk with
  | none =>
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ekBytes =>
    by_cases hcond : (sendCt2OnDone && (ekBytes.length == 1184)) = true
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) =
            SeqEnv (UnchunkedSendCt2BySizesEnv es ct1Len)
              (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs) := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec es hct1
      have h2 := sendCt2Encoder_fine_128_32_phaseCreditSpec
      have h3 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

theorem recvHdrChunkTail_fine_le_96_phaseCreditSpec {optHdr : Option Bytes}
    (hn : optBytesLen optHdr ≤ 96) :
    PhaseCreditSpec fineCostModel (RecvHdrChunkTailEnv optHdr) 17693 0 0 105 := by
  cases optHdr with
  | none =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some hdrFull =>
    dsimp only [optBytesLen] at hn
    by_cases hlt : hdrFull.length < 64
    · have heq : RecvHdrChunkTailEnv (some hdrFull) = (· = []) := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have heq :
          RecvHdrChunkTailEnv (some hdrFull) =
            SeqEnv
              (· = recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents)
              FreeOnlyEvs := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      have h_mac :
          PhaseCreditSpec fineCostModel (· = recvHdrChunkAllocMacHdrEvents hdrFull.length)
            2345 0 0 64 := by
        unfold recvHdrChunkAllocMacHdrEvents
        have ha :
            PhaseCreditSpec fineCostModel
              (· = if hdrFull.length = 64 then [] else rustAllocEvents (hdrFull.length - 64) 1)
              738 0 0 32 := by
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · have hsm : hdrFull.length - 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
              rw [fineCostModel_smallMaxReq_eq]; omega
            exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
              (req := hdrFull.length - 64) (al := 1) (by decide) hsm).mono
              (smallAllocCost_le_738_of_le_44 (by omega))
              (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have hb := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 64) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (fineSmallAllocCost_le_1607_of_le_74 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
        exact (PhaseCreditSpec.append_eq ha hb).mono
          (by decide) (by decide) (by decide) (by decide)
      have h_hmac :
          PhaseCreditSpec fineCostModel (· = recvHdrChunkHmacEvents) 15348 0 0 105 := by
        unfold recvHdrChunkHmacEvents
        have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 105) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 105)
        exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
          (by decide) (by decide) (by decide) (by decide)
      exact ((PhaseCreditSpec.append_eq h_mac h_hmac).seq
        (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
        (by decide) (by decide) (by decide) (by decide)

theorem authUpdate_fine_two_mul_phaseCreditSpec {rootKeyLen : Nat}
    (hsm : rootKeyLen + 32 ≤ 135167) :
    PhaseCreditSpec fineCostModel (AuthUpdateEnv rootKeyLen 32)
      (2 * rootKeyLen + 14293) 0 0 (max (rootKeyLen + 32) 64) := by
  unfold AuthUpdateEnv
  have hlbl : Authenticator.updateLabel.length = 45 := by decide
  rw [hlbl]
  have h1 := sliceConcat2Events_fine_two_mul hsm
  have h2 := sliceConcat2Events_fine_le_74 (n := 53) (by decide)
  have h3 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 64) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (fineSmallAllocCost_le_1607_of_le_74 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  have h4 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (smallAllocCost_le_738_of_le_44 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  have h5 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h4.seq h5)))))).mono
    (by omega) (by decide) (by decide) (by omega)

theorem recvCt2ChunkTail_fine_two_mul_phaseCreditSpec {rootKeyLen ct1Len : Nat}
    (hrk : rootKeyLen + 32 ≤ 135167) (hct1 : ct1Len ≤ 1088)
    {optCt2 : Option Bytes} (hn : optBytesLen optCt2 ≤ 160) :
    PhaseCreditSpec fineCostModel (RecvCt2ChunkTailEnv rootKeyLen ct1Len optCt2)
      (2 * rootKeyLen + 53129) 0 0 (max (rootKeyLen + 64) 2430) := by
  cases optCt2 with
  | none =>
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ct2Full =>
    dsimp only [optBytesLen] at hn
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have heq :
          RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) =
            SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
              (SeqEnv (· = rustAllocEvents 32 1)
                (SeqEnv (· = sliceConcat2Events 41)
                  (SeqEnv (· = rustAllocEvents 32 1)
                    (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                      (SeqEnv (SendCt2Reserve128Env ct1Len)
                        (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len) FreeOnlyEvs)))))) := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      have h1 :
          PhaseCreditSpec fineCostModel (· = recvCt2AllocMacCt2Events ct2Full.length)
            10527 0 0 128 := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            PhaseCreditSpec fineCostModel
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
              738 0 0 32 := by
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · have hsm : ct2Full.length - 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
              rw [fineCostModel_smallMaxReq_eq]; omega
            exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
              (req := ct2Full.length - 128) (al := 1) (by decide) hsm).mono
              (smallAllocCost_le_738_of_le_44 (by omega))
              (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have hb := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 128) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
        exact (PhaseCreditSpec.append_eq ha hb).mono
          (by decide) (by decide) (by decide) (by decide)
      have h32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
        (smallAllocCost_le_738_of_le_44 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
      have h41 := sliceConcat2Events_fine_le_44 (n := 41) (by decide)
      have h5 := authUpdate_fine_two_mul_phaseCreditSpec hrk
      have h6 := sendCt2Reserve128_fine_le_1088_phaseCreditSpec hct1
      have h7 :
          PhaseCreditSpec fineCostModel (· = sendCt2ConcatHmacEvents ct1Len)
            15348 0 0 1280 := by
        unfold sendCt2ConcatHmacEvents
        have hsm : 35 + 8 + (ct1Len + 128) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]; omega
        have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 35 + 8 + (ct1Len + 128)) (al := 1) (by decide) hsm).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) (show 35 + 8 + (ct1Len + 128) ≤ 1280 by omega)
        exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
          (by decide) (by decide) (by decide) (by decide)
      have h8 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq (h7.seq h8))))))).mono
        (by omega) (by decide) (by decide) (by omega)

/-- Exact sub-phase `PhaseCreditSpec` on `fineCostModel` (`Δcum = 1,435,018`, `Δlive = Δpeak = 0`, `maxReq = 4,608`) under `StatesDecSlotCap 576 st`.
-/
theorem statesRecv_tight_exact_phaseCreditSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hbound : StatesPtsBoundedAt 640 st ∧ StatesDecPtsNeededBound st)
    (hproto : StatesProtocolSizes st)
    (hslot : StatesDecSlotCap 576 st) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      statesRecvTightExactDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightMaxReq := by
  have hFree :
      PhaseCreditSpec fineCostModel FreeOnlyEvs
        statesRecvTightExactDeltaCum 0 0 statesRecvTightMaxReq :=
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  obtain ⟨hpts640, hpts⟩ := hbound
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      have hek : s.uc.ek.length = 1152 := hpts640.2
      have h1 := addChunkSlots_fine_replicate16_phaseCreditSpec
      have h2 :
          PhaseCreditSpec fineCostModel
            (SeqEnv (EncodeBytesEnv s.uc.ek.length) FreeOnlyEvs) 33744 0 0 1152 := by
        rw [hek]
        exact seq_freeOnly fineCostModel_modelHyps
          encodeBytes_fine_1152_phaseCreditSpec (Nat.le_refl 0)
      exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes, StatesDecSlotCap] at hpts hproto hslot
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_fine_576_phaseCreditSpec (Nat.le_of_eq hproto) hslot
        have h2 := (seq_freeOnly fineCostModel_modelHyps
          (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt1) (by omega))
          (Nat.le_refl 0)).mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rCt1.ptsNeeded) ≤ 960 by omega)
        exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly fineCostModel_modelHyps
        addChunkSlots_fine_replicate16_phaseCreditSpec (Nat.le_refl 0)).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes, StatesDecSlotCap] at hpts hproto hslot
        obtain ⟨hlen16, hct1⟩ := hproto
        obtain ⟨hsl, hrk32⟩ := hslot
        have hbody :
            PhaseCreditSpec fineCostModel
              (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk)
              statesRecvTightExactDeltaCum 0 0 statesRecvTightMaxReq := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := addChunkSlots_fine_576_phaseCreditSpec (Nat.le_of_eq hlen16) hsl
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt2) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rCt2.ptsNeeded) ≤ 256 by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 := (recvCt2ChunkTail_fine_two_mul_phaseCreditSpec
              (rootKeyLen := s.uc.auth.rootKey.length) (ct1Len := s.uc.ct1.length)
              (by omega) (by omega) hn160).mono
              (show 2 * s.uc.auth.rootKey.length + 53129 ≤ 53193 by omega)
              (Nat.le_refl 0) (Nat.le_refl 0)
              (show max (s.uc.auth.rootKey.length + 64) 2430 ≤ 2430 by omega)
            exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody (Nat.le_refl 0)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes, StatesDecSlotCap] at hpts hproto hslot
        have hbody :
            PhaseCreditSpec fineCostModel
              (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk)
              statesRecvTightExactDeltaCum 0 0 statesRecvTightMaxReq := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 48 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := addChunkSlots_fine_576_phaseCreditSpec (Nat.le_of_eq hproto) hslot
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rHdr) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rHdr.ptsNeeded) ≤ 256 by omega)
            have hn96 : optBytesLen (decodedMessageTotal rHdr) ≤ 96 := by
              have := optBytesLen_decodedMessageTotal_le rHdr; omega
            have h3 := recvHdrChunkTail_fine_le_96_phaseCreditSpec hn96
            exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody (Nat.le_refl 0)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes, StatesDecSlotCap] at hpts hproto hslot
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec fineCostModel
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            statesRecvTightExactDeltaCum 0 0 statesRecvTightMaxReq := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_fine_576_phaseCreditSpec (Nat.le_of_eq hlen16) hslot
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail_fine_le_1088_phaseCreditSpec ack s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega) (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        dsimp only [StatesProtocolSizes] at hproto
        have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega)
        have h2 := seq_freeOnly fineCostModel_modelHyps
          sendCt2Encoder_fine_128_32_phaseCreditSpec (Nat.le_refl 0)
        exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes, StatesDecSlotCap] at hpts hproto hslot
      obtain ⟨hlen16, hct1⟩ := hproto
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := addChunkSlots_fine_576_phaseCreditSpec (Nat.le_of_eq hlen16) hslot
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail_fine_le_1088_phaseCreditSpec true s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega) (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- Tight `PhaseCreditSpec` (`Δcum = 1,647,247`, `Δlive = Δpeak = 0`, `maxReq = 4,608`) under `StatesDecSlotCap 576 st`.
-/
theorem statesRecv_tight_phaseCreditSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hbound : StatesPtsBoundedAt 640 st ∧ StatesDecPtsNeededBound st)
    (hproto : StatesProtocolSizes st)
    (hslot : StatesDecSlotCap 576 st) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      statesRecvTightDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightMaxReq :=
  (statesRecv_tight_exact_phaseCreditSpec st msg hbound hproto hslot).mono
    statesRecvTightExactDeltaCum_le (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 4608)

theorem statesRecv_tight_anyK_phaseCreditSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hbound : StatesPtsBoundedAt 640 st ∧ StatesDecPtsNeededBound st)
    (hproto : StatesProtocolSizes st)
    (hslot : StatesDecSlotCap 576 st) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      statesRecvTightAnyKDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightMaxReq :=
  (statesRecv_tight_phaseCreditSpec st msg hbound hproto hslot).mono
    statesRecvTightDeltaCum_le_anyK (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 4608)

private theorem raw46880_dec_cum_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    16 * ptsSum + 9571 * 16 ≤ 339248 := by
  have hp : ptsSum ≤ 11632 := by omega
  have hm : 16 * ptsSum ≤ 16 * 11632 := Nat.mul_le_mul_left 16 hp
  exact Nat.le_trans (Nat.add_le_add_right hm _) (by decide)

private theorem raw46880_dec_req_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    8 * ptsSum + 16 ≤ 93072 := by
  omega

private theorem raw46880_ct2_cum_le {ptsSum rk rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hsum : (rk + 960) + rawDec ≤ 46880) :
    (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53129)) ≤ statesRecvTightDeltaCum := by
  have hcomb : 4 * ptsSum + rk ≤ 45568 := by omega
  have hlin : 16 * ptsSum + 2 * rk ≤ 4 * 45568 := by omega
  have hconst : 4 * 45568 + 9571 * 16 + 1022346 + 53129 ≤ statesRecvTightDeltaCum := by decide
  have h1 : (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53129)) =
      (16 * ptsSum + 2 * rk) + (9571 * 16 + 1022346 + 53129) := by omega
  rw [h1]
  exact Nat.le_trans (Nat.add_le_add_right hlin _) (by
    simpa only [Nat.add_assoc] using hconst)

/-- Slot-cap-free `PhaseCreditSpec` (`Δcum = 1,647,247`, `Δlive = Δpeak = 0`, `maxReq = 93,776`) requiring only `StatesProtocolSizes st`, `StatesDecPtsNeededBound st`, and `rawV1State st.into_pb ≤ 46,880`.
-/
theorem statesRecv_tight_of_protocolSizes_46880_phaseCreditSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st)
    (hraw46 : rawV1State st.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      statesRecvTightDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightRawMaxReq := by
  have hFree :
      PhaseCreditSpec fineCostModel FreeOnlyEvs
        statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq :=
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := addChunkSlots_fine_replicate16_phaseCreditSpec
      have h2 :
          PhaseCreditSpec fineCostModel
            (SeqEnv (EncodeBytesEnv s.uc.ek.length) FreeOnlyEvs) 33744 0 0 1152 := by
        rw [hproto]
        exact seq_freeOnly fineCostModel_modelHyps
          encodeBytes_fine_1152_phaseCreditSpec (Nat.le_refl 0)
      exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct1
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_ct1.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, HeaderSent.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChHeaderSent, optRaw]
          omega
        have hreq93 := raw46880_dec_req_le hraw hdec_le
        have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct1.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) hreq93
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h2 := (seq_freeOnly fineCostModel_modelHyps
          (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt1) (by omega))
          (Nat.le_refl 0)).mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rCt1.ptsNeeded) ≤ 960 by omega)
        exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly fineCostModel_modelHyps
        addChunkSlots_fine_replicate16_phaseCreditSpec (Nat.le_refl 0)).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct2
        rw [hlen16] at hraw
        have hsum_le :
            (s.uc.auth.rootKey.length + 960) +
              rawPolyDec (protoPolyDecoderToPb s.receiving_ct2.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, EkSentCt1Received.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb,
            spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
            rawV1State, rawInnerState, rawChEkSentCt1Received, rawUcEkSentCt1Received,
            rawAuth, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 :
                PhaseCreditSpec fineCostModel (AddChunkSlotsEnv s.receiving_ct2.pts)
                  (16 * ptsLenSum s.receiving_ct2.pts + 9571 * 16) 0 0 91152 := by
              have hb := addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct2.pts
                (by omega)
              rw [hlen16] at hb
              exact hb.mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt2) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rCt2.ptsNeeded) ≤ 256 by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 := (recvCt2ChunkTail_fine_two_mul_phaseCreditSpec
              (rootKeyLen := s.uc.auth.rootKey.length) (ct1Len := s.uc.ct1.length)
              (by omega) (by omega) hn160).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max (s.uc.auth.rootKey.length + 64) 2430 ≤ 45632 by omega)
            exact (h1.seq (h2.seq h3)).mono
              (raw46880_ct2_cum_le hraw hsum_le)
              (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody (Nat.le_refl 0)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_hdr
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, NoHeaderReceived.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChNoHeaderReceived, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 48 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_hdr.pts
              (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
              (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rHdr) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rHdr.ptsNeeded) ≤ 256 by omega)
            have hn96 : optBytesLen (decodedMessageTotal rHdr) ≤ 96 := by
              have := optBytesLen_decodedMessageTotal_le rHdr; omega
            have h3 := recvHdrChunkTail_fine_le_96_phaseCreditSpec hn96
            exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody (Nat.le_refl 0)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Sampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Sampled, rawUcCt1Sent, optRaw]
        omega
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec fineCostModel
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail_fine_le_1088_phaseCreditSpec ack s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega) (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        dsimp only [StatesProtocolSizes] at hproto
        have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega)
        have h2 := seq_freeOnly fineCostModel_modelHyps
          sendCt2Encoder_fine_128_32_phaseCreditSpec (Nat.le_refl 0)
        exact (h1.seq h2).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Acknowledged.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Acknowledged, rawUcCt1Sent, optRaw]
        omega
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail_fine_le_1088_phaseCreditSpec true s.uc.es
          (ct1Len := s.uc.ct1.length) (by omega) (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- `States.from_pb` corollary of `statesRecv_tight_of_protocolSizes_46880_phaseCreditSpec`. -/
theorem statesRecv_tight_of_from_pb_46880_phaseCreditSpec {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (hraw46 : rawV1State st.into_pb ≤ 46880)
    (msg : Message spqrPolyApi) :
    PhaseCreditSpec fineCostModel (StatesRecvEnv st msg)
      statesRecvTightDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightRawMaxReq :=
  statesRecv_tight_of_protocolSizes_46880_phaseCreditSpec st msg
    (StatesProtocolSizes.of_from_pb hfrom)
    (StatesDecPtsNeededBound.of_from_pb hfrom)
    hraw46

/-! ### `NonFreeBound` and `PhaseGroupSpec` for `StatesRecvEnv` -/

private theorem sliceConcat2Events_nonFreeBound (n : Nat) :
    NonFreeBound (· = sliceConcat2Events n) 1 := by
  unfold sliceConcat2Events
  split
  · exact NonFreeBound.nil.mono (by decide)
  · exact NonFreeBound.rustAlloc n 1

private theorem sendCt2EncoderGrow_nonFreeBound (ct2Len macLen : Nat) :
    NonFreeBound (SendCt2EncoderGrowEnv ct2Len macLen) 1 := by
  rintro evs (⟨_, rfl⟩ | ⟨newCap, _, _, rfl⟩)
  · exact (NonFreeBound.nil.mono (by decide)) _ rfl
  · split
    · exact NonFreeBound.rustAlloc newCap 1 _ rfl
    · exact NonFreeBound.rustRealloc ct2Len newCap 1 _ rfl

theorem sendCt2Encoder_nonFreeBound (ct2Len macLen : Nat) :
    NonFreeBound (SendCt2EncoderEnv ct2Len macLen) 18 := by
  unfold SendCt2EncoderEnv
  exact ((sliceConcat2Events_nonFreeBound ct2Len).seq
    ((sendCt2EncoderGrow_nonFreeBound ct2Len macLen).seq
      ((encodeBytes_nonFreeBound (ct2Len + macLen)).seq NonFreeBound.freeOnly))).mono (by decide)

theorem authUpdate_nonFreeBound (rootKeyLen kLen : Nat) :
    NonFreeBound (AuthUpdateEnv rootKeyLen kLen) 5 := by
  unfold AuthUpdateEnv
  exact ((sliceConcat2Events_nonFreeBound (rootKeyLen + kLen)).seq
    ((sliceConcat2Events_nonFreeBound (Authenticator.updateLabel.length + 8)).seq
      ((NonFreeBound.rustAlloc 64 1).seq
        ((NonFreeBound.rustAlloc 32 1).seq
          (NonFreeBound.freeOnly.seq
            ((NonFreeBound.rustAlloc 32 1).seq NonFreeBound.freeOnly)))))).mono (by decide)

theorem unchunkedSendCt2BySizes_nonFreeBound (es : Bytes) (ct1Len : Nat) :
    NonFreeBound (UnchunkedSendCt2BySizesEnv es ct1Len) 8 := by
  unfold UnchunkedSendCt2BySizesEnv
  exact ((((sendCt2Seg23_nonFreeBound es).concat
    (sendCt2Reserve128_nonFreeBound ct1Len)).concat
    (sendCt2ConcatHmac_nonFreeBound ct1Len)).concat NonFreeBound.freeOnly).mono (by decide)

theorem recvHdrChunkTail_nonFreeBound (optHdr : Option Bytes) :
    NonFreeBound (RecvHdrChunkTailEnv optHdr) 7 := by
  cases optHdr with
  | none => exact NonFreeBound.nil.mono (by decide)
  | some hdrFull =>
    by_cases hlt : hdrFull.length < 64
    · have heq : RecvHdrChunkTailEnv (some hdrFull) = (· = []) := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      exact NonFreeBound.nil.mono (by decide)
    · have heq :
          RecvHdrChunkTailEnv (some hdrFull) =
            SeqEnv
              (· = recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents)
              FreeOnlyEvs := by
        funext evs; simp [RecvHdrChunkTailEnv, hlt]
      rw [heq]
      have h_mac : NonFreeBound (· = recvHdrChunkAllocMacHdrEvents hdrFull.length) 2 := by
        unfold recvHdrChunkAllocMacHdrEvents
        have ha :
            NonFreeBound
              (· = if hdrFull.length = 64 then [] else rustAllocEvents (hdrFull.length - 64) 1) 1 := by
          split
          · exact NonFreeBound.nil.mono (by decide)
          · exact NonFreeBound.rustAlloc (hdrFull.length - 64) 1
        exact (NonFreeBound.append_eq ha (NonFreeBound.rustAlloc 64 1)).mono (by decide)
      have h_hmac : NonFreeBound (· = recvHdrChunkHmacEvents) 5 := by
        unfold recvHdrChunkHmacEvents
        exact (NonFreeBound.append_eq (NonFreeBound.rustAlloc 105 1)
          libcruxHmacSha256_nonFreeBound).mono (by decide)
      exact ((NonFreeBound.append_eq h_mac h_hmac).seq NonFreeBound.freeOnly).mono (by decide)

theorem recvCt2ChunkTail_nonFreeBound (rootKeyLen ct1Len : Nat) (optCt2 : Option Bytes) :
    NonFreeBound (RecvCt2ChunkTailEnv rootKeyLen ct1Len optCt2) 16 := by
  cases optCt2 with
  | none => exact NonFreeBound.freeOnly.mono (by decide)
  | some ct2Full =>
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      exact NonFreeBound.freeOnly.mono (by decide)
    · have heq :
          RecvCt2ChunkTailEnv rootKeyLen ct1Len (some ct2Full) =
            SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
              (SeqEnv (· = rustAllocEvents 32 1)
                (SeqEnv (· = sliceConcat2Events 41)
                  (SeqEnv (· = rustAllocEvents 32 1)
                    (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                      (SeqEnv (SendCt2Reserve128Env ct1Len)
                        (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len) FreeOnlyEvs)))))) := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      have h1 : NonFreeBound (· = recvCt2AllocMacCt2Events ct2Full.length) 2 := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            NonFreeBound
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1) 1 := by
          split
          · exact NonFreeBound.nil.mono (by decide)
          · exact NonFreeBound.rustAlloc (ct2Full.length - 128) 1
        exact (NonFreeBound.append_eq ha (NonFreeBound.rustAlloc 128 1)).mono (by decide)
      exact (h1.seq
        ((NonFreeBound.rustAlloc 32 1).seq
          ((sliceConcat2Events_nonFreeBound 41).seq
            ((NonFreeBound.rustAlloc 32 1).seq
              ((authUpdate_nonFreeBound rootKeyLen 32).seq
                ((sendCt2Reserve128_nonFreeBound ct1Len).seq
                  ((sendCt2ConcatHmac_nonFreeBound ct1Len).seq NonFreeBound.freeOnly))))))).mono
        (by decide)

theorem recvEkChunkSendCt2Tail_nonFreeBound
    (sendCt2OnDone : Bool) (es : Bytes) (ct1Len : Nat) (optEk : Option Bytes) :
    NonFreeBound (RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len optEk) 26 := by
  cases optEk with
  | none => exact NonFreeBound.freeOnly.mono (by decide)
  | some ekBytes =>
    by_cases hcond : (sendCt2OnDone && (ekBytes.length == 1184)) = true
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) =
            SeqEnv (UnchunkedSendCt2BySizesEnv es ct1Len)
              (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs) := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact ((unchunkedSendCt2BySizes_nonFreeBound es ct1Len).seq
        ((sendCt2Encoder_nonFreeBound 128 32).seq NonFreeBound.freeOnly)).mono (by decide)
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es ct1Len (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact NonFreeBound.freeOnly.mono (by decide)

/-- `1,244`-operation `NonFreeBound` across all 12 arms of `StatesRecvEnv st msg`. -/
theorem statesRecv_tight_nonFreeBound {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    NonFreeBound (StatesRecvEnv st msg) 1244 := by
  have hFree : NonFreeBound FreeOnlyEvs 1244 := NonFreeBound.freeOnly.mono (by decide)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      have h1 : NonFreeBound (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) 16 := by
        simpa using addChunkSlots_nonFreeBound (List.replicate 16 SortedSetPt.new)
      exact (h1.seq ((encodeBytes_nonFreeBound s.uc.ek.length).seq NonFreeBound.freeOnly)).mono
        (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ct1.pts) 16 :=
          hproto ▸ addChunkSlots_nonFreeBound s.receiving_ct1.pts
        have hr_pts : (addChunkTotal s.receiving_ct1 chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ct1 chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        exact (h1.seq (h2.seq NonFreeBound.freeOnly)).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      have h1 : NonFreeBound (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) 16 := by
        simpa using addChunkSlots_nonFreeBound (List.replicate 16 SortedSetPt.new)
      exact (h1.seq NonFreeBound.freeOnly).mono (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : NonFreeBound (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk) 1244 := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact NonFreeBound.nil.mono (by decide)
          · dsimp only
            have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ct2.pts) 16 :=
              hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ct2.pts
            have hr_pts : (addChunkTotal s.receiving_ct2 chunk).ptsNeeded ≤ 576 := by
              have := addChunkTotal_ptsNeeded_uncond s.receiving_ct2 chunk; omega
            have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
            have h3 := recvCt2ChunkTail_nonFreeBound s.uc.auth.rootKey.length s.uc.ct1.length
              (decodedMessageTotal (addChunkTotal s.receiving_ct2 chunk))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact (hbody.seq NonFreeBound.freeOnly).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : NonFreeBound (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) 1244 := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact NonFreeBound.nil.mono (by decide)
          · dsimp only
            have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_hdr.pts) 16 :=
              hproto ▸ addChunkSlots_nonFreeBound s.receiving_hdr.pts
            have hr_pts : (addChunkTotal s.receiving_hdr chunk).ptsNeeded ≤ 576 := by
              have := addChunkTotal_ptsNeeded_uncond s.receiving_hdr chunk; omega
            have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
            have h3 := recvHdrChunkTail_nonFreeBound
              (decodedMessageTotal (addChunkTotal s.receiving_hdr chunk))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact (hbody.seq NonFreeBound.freeOnly).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          NonFreeBound
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            1244 := fun chunk ack => by
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ek.pts) 16 :=
          hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ek.pts
        have hr_pts : (addChunkTotal s.receiving_ek chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ek chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        have h3 := recvEkChunkSendCt2Tail_nonFreeBound ack s.uc.es s.uc.ct1.length
          (decodedMessageTotal (addChunkTotal s.receiving_ek chunk))
        exact (h1.seq (h2.seq h3)).mono (by decide)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        exact ((unchunkedSendCt2BySizes_nonFreeBound s.uc.es s.uc.ct1.length).seq
          ((sendCt2Encoder_nonFreeBound 128 32).seq NonFreeBound.freeOnly)).mono (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        have h1 : NonFreeBound (AddChunkSlotsEnv s.receiving_ek.pts) 16 :=
          hproto.1 ▸ addChunkSlots_nonFreeBound s.receiving_ek.pts
        have hr_pts : (addChunkTotal s.receiving_ek chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ek chunk; omega
        have h2 := decodedMessage_ptsNeeded_le_576_nonFreeBound hr_pts
        have h3 := recvEkChunkSendCt2Tail_nonFreeBound true s.uc.es s.uc.ct1.length
          (decodedMessageTotal (addChunkTotal s.receiving_ek chunk))
        exact (h1.seq (h2.seq h3)).mono (by decide)
    · exact hFree
  | ct2Sampled _ => exact hFree

/-- `PhaseGroupSpec` (`3,732` groups) for `StatesRecvEnv st msg` on `fineCostModel`. -/
theorem statesRecv_tight_phaseGroupSpec {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseGroupSpec fineCostModel (StatesRecvEnv st msg) statesRecvTightGroupS :=
  PhaseGroupSpec.of_nonFreeBound fineCostModel (statesRecv_tight_nonFreeBound st msg hproto hpts)

theorem statesRecv_tight_of_from_pb_phaseGroupSpec {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    PhaseGroupSpec fineCostModel (StatesRecvEnv st msg) statesRecvTightGroupS :=
  statesRecv_tight_phaseGroupSpec st msg
    (StatesProtocolSizes.of_from_pb hfrom)
    (StatesDecPtsNeededBound.of_from_pb hfrom)

/-! ### Protocol-Guarded Envelope Bridges (`StatesRecvProtoEnv`) -/

/-- Decidable `Bool` mirror of `StatesProtocolSizes`. -/
def isStatesProtoSized {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Bool
  | .keysUnsampled _ => true
  | .keysSampled s => s.uc.ek.length == 1152
  | .headerSent s => s.receiving_ct1.pts.length == 16
  | .ct1Received _ => true
  | .ekSentCt1Received s =>
    (s.receiving_ct2.pts.length == 16) && (s.uc.ct1.length == 960)
  | .noHeaderReceived s => s.receiving_hdr.pts.length == 16
  | .headerReceived _ => true
  | .ct1Sampled s =>
    (s.receiving_ek.pts.length == 16) && (s.uc.ct1.length == 960)
  | .ekReceivedCt1Sampled s => s.uc.ct1.length == 960
  | .ct1Acknowledged s =>
    (s.receiving_ek.pts.length == 16) && (s.uc.ct1.length == 960)
  | .ct2Sampled _ => true

theorem isStatesProtoSized_eq_true_iff {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    isStatesProtoSized st = true ↔ StatesProtocolSizes st := by
  cases st <;>
    simp [isStatesProtoSized, StatesProtocolSizes, Bool.and_eq_true, beq_iff_eq]

/-- Protocol-sized wrapper around `StatesRecvEnv` (coinciding with `StatesRecvEnv` on every `States.from_pb` output).
-/
def StatesRecvProtoEnv {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  if isStatesProtoSized st then StatesRecvEnv st msg else FreeOnlyEvs

theorem statesRecvProtoEnv_nonempty {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    ∃ evs : List AllocEvent, StatesRecvProtoEnv st msg evs := by
  unfold StatesRecvProtoEnv
  split
  · exact statesRecvEnv_nonempty st msg
  · exact ⟨[], FreeOnlyEvs.nil⟩

theorem statesRecvProtoEnv_eq_of_protocolSizes {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} (hproto : StatesProtocolSizes st)
    (msg : Message spqrPolyApi) :
    StatesRecvProtoEnv st msg = StatesRecvEnv st msg := by
  unfold StatesRecvProtoEnv
  rw [(isStatesProtoSized_eq_true_iff st).mpr hproto]
  simp only [↓reduceIte]

theorem statesRecvProtoEnv_eq_of_from_pb {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    StatesRecvProtoEnv st msg = StatesRecvEnv st msg :=
  statesRecvProtoEnv_eq_of_protocolSizes (StatesProtocolSizes.of_from_pb hfrom) msg

/-- Tight `PhaseCreditSpec` (`1,647,247 / 0 / 0 / 93,776`) for `StatesRecvProtoEnv`. -/
theorem statesRecvProtoEnv_tight_creditSpec {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (StatesRecvProtoEnv st0 msg)
      statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv_eq_of_protocolSizes hproto msg]
    exact statesRecv_tight_of_protocolSizes_46880_phaseCreditSpec st0 msg hproto hpts hraw46
  · have heq : StatesRecvProtoEnv st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv; simp [hb]
    rw [heq]
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)

/-- Tight `PhaseGroupSpec` (`statesRecvTightGroupS`) for `StatesRecvProtoEnv`. -/
theorem statesRecvProtoEnv_tight_groupSpec {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (_hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseGroupSpec fineCostModel (StatesRecvProtoEnv st0 msg) statesRecvTightGroupS := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv_eq_of_protocolSizes hproto msg]
    exact statesRecv_tight_phaseGroupSpec st0 msg hproto hpts
  · have heq : StatesRecvProtoEnv st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv; simp [hb]
    rw [heq]
    exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

/-! ### `FitsEnv fineCostModel` Corollaries -/

/-- `250 MiB` (`262,144,000` bytes) physical RAM limit paired with `nonVacLimits` static image allowances.
-/
def nonVacLimits250MiB : BudgetLimits :=
  { nonVacLimits with physCap := 250 * 1024 * 1024 }

/-- `FitsEnv fineCostModel` bound for `StatesRecvEnv` under `nonVacLimits250MiB` and `StatesDecSlotCap 576`.
-/
theorem statesRecv_tight_fitsEnv_groups_250mb {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hbound : StatesPtsBoundedAt 640 st ∧ StatesDecPtsNeededBound st)
    (hproto : StatesProtocolSizes st)
    (hslot : StatesDecSlotCap 576 st) :
    FitsEnv fineCostModel nonVacLimits250MiB fineCostModel.init (StatesRecvEnv st msg) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 3732)
    (statesRecv_tight_phaseCreditSpec st msg hbound hproto hslot)
    (statesRecv_tight_phaseGroupSpec st msg hproto hbound.2)
    (Nat.le_refl 0) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

/-- Slot-cap-free `States.from_pb` `FitsEnv fineCostModel` bound under `nonVacLimits250MiB`. -/
theorem statesRecv_tight_from_pb_46880_fitsEnv_groups_250mb {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (hraw46 : rawV1State st.into_pb ≤ 46880)
    (msg : Message spqrPolyApi) :
    FitsEnv fineCostModel nonVacLimits250MiB fineCostModel.init (StatesRecvEnv st msg) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 3732)
    (statesRecv_tight_of_from_pb_46880_phaseCreditSpec hfrom hraw46 msg)
    (statesRecv_tight_of_from_pb_phaseGroupSpec hfrom msg)
    (Nat.le_refl 0) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

theorem statesRecv_tight_fitsEnv_groups {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hbound : StatesPtsBoundedAt 640 st ∧ StatesDecPtsNeededBound st)
    (hproto : StatesProtocolSizes st)
    (hslot : StatesDecSlotCap 576 st) :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init (StatesRecvEnv st msg) :=
  fitsEnv_fineCostModel_of_phaseCredit_groups (grpB := 3732)
    (statesRecv_tight_phaseCreditSpec st msg hbound hproto hslot)
    (statesRecv_tight_phaseGroupSpec st msg hproto hbound.2)
    (Nat.le_refl 0) (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

end LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
