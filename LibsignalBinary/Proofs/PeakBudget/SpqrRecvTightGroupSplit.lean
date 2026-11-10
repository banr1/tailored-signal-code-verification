/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec

/-!
# Size-Class Split `PhaseGroupSpec` Bounds for SPQR `spqr::recv` and `try_decrypt`

Refines coarse `3 * FineScale = 196,608`/op slot-group bounds across `SpqrTightEvs` codecs and the
12 dispatch arms of `<States>::recv` using `align ≤ 16` (`≤ 140,011`/op) and size-class-specific
`fineGroupsScaled` weights, yielding `spqrRecvTightGroupS_split = 470,785,855` (`7,184` groups) for
`spqr::recv` and `509,326,673` (`7,772` groups) for `W2TryDecryptTightEnv` at `caps.length ≤ 12`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk Epoch GF16 Message MlKem Poly PolyDecoder PqRatchetState Pt
   SortedSetPt States V1Recv V1State VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (collectPointsVecsTotal collectPointsVecsTotal_of_fst_false collectedSlices
   collectedSlices_getElem collectedSlices_length decodedMessageTotal lagrangeInterpolateTotal
   lagrangeInterpolateTotal_length)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight)
open VerifiedLibraries.Mallocng.Proofs (nominalSlotCap sizeToClassUnits sizeToClass_spec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale MmapThresholdReq coarseGrpWtS fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (W2TryDecryptTightEnv w2Seg4CmkFineGrpS w2Seg4CmkStepEnv_groupSpec
   w2TryDecryptEnv_of_seg4_groupSpec w2TryDecryptFailEnv_of_seg4_groupSpec
   w2TryDecryptTightEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit PhaseGroupSpec fineGroupsScaled fineSmallAllocGroupS fineSmallReallocGroupS)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrTightEvs StatesIntoPbTightEnv spqrAllocTightCost spqrEventTightCost spqrTraceTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (spqrRecvC07TightEnv_proto_eq spqrRecvEqualC07TightEnv_proto_eq)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
  (C07TightGroupSpec StatesRecvTightGroupSpec spqrRecvOrderingEqual_phaseGroupSpec_tight
   spqrRecvParts_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvEqualC07TightEnv SpqrRecvTightDomain)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
  (PolyCacheDegBound PolyCacheRangeBound collectedSlices_getD_length_le polyCacheDegBound_getD_some
   polyCacheDegBound_replicate_none polyCacheDegBound_set_some polyNoneCount
   polyNoneCount_replicate_none polyNoneCount_set_some_eq)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
  (AuthUpdateEnv EkSentCt1ReceivedRecvCt2ChunkEnv NoHeaderReceivedRecvHdrChunkBodyEnv
   RecvCt2ChunkTailEnv RecvEkChunkSendCt2TailEnv SendCt2EncoderEnv SendCt2EncoderGrowEnv
   StatesProtocolSizes StatesRecvEnv StatesRecvProtoEnv UnchunkedSendCt2BySizesEnv
   addChunkTotal_ptsNeeded_uncond isEkReceivedCt1AckMsg isStatesProtoSized
   isStatesProtoSized_eq_true_iff recvCt2AllocMacCt2Events recvHdrChunkTail_nonFreeBound
   statesRecvProtoEnv_eq_of_protocolSizes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidChainParamsPB)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (W2Seg4CmkStepEnv W2TryDecryptEnv W2TryDecryptFailEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotEnv AddChunkSlotsEnv growOnePtEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv DecodedMessageEnv DecodedMessageLoopEnv LagrangeInterpolateMissEnv
   computeAtAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
   sendCt2Reserve128Events sendCt2Seg23Events)

/-! ## Atomic `align ≤ 16` and Small-Class `fineCostModel` Group Lemmas -/

private theorem append_eq_groupSpec {M : AllocCostModel} [HasFineGroupCredit M]
    {a b : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = a) g₁) (h₂ : PhaseGroupSpec M (· = b) g₂) :
    PhaseGroupSpec M (· = a ++ b) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨a, b, h, rfl, rfl⟩

private theorem seq_freeOnly_right {E : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel E g) :
    PhaseGroupSpec fineCostModel (SeqEnv E FreeOnlyEvs) g :=
  (h.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero g))

private def tightMinReq (sc : Nat) : Nat :=
  if sc = 0 then 0 else nominalSlotCap (sc - 1) + 1

private def checkFineGroupBuckets : Bool :=
  (List.range 48).all fun sc =>
    let rMin := tightMinReq sc
    let gAlloc := coarseGrpWtS sc
    let gRealloc := max (coarseGrpWtS sc) FineScale
    decide (
      gAlloc ≤ 140011 ∧
      gRealloc ≤ 140011 ∧
      (rMin ≤ 12 → gAlloc ≤ 4737) ∧
      (rMin ≤ 44 → gAlloc ≤ 16659) ∧
      (rMin ≤ 92 → gAlloc ≤ 34877) ∧
      (rMin ≤ 108 → gAlloc ≤ 43464))

private theorem checkFineGroupBuckets_true : checkFineGroupBuckets = true := by
  decide

private theorem tightMinReq_le_of_le {req : Nat} (hle : req ≤ MmapThresholdReq) :
    sizeToClassUnits ((req + 3) / 16) < 48 ∧
      tightMinReq (sizeToClassUnits ((req + 3) / 16)) ≤ req := by
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  refine ⟨hspec.1, ?_⟩
  unfold tightMinReq
  rcases hspec.2.2 with h0 | hprev
  · simp [h0]
  · split <;> omega

private theorem smallAllocGroupS_le_140011 {req : Nat} (hle : req ≤ MmapThresholdReq) :
    fineSmallAllocGroupS req ≤ 140011 := by
  obtain ⟨hsc, _⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).1

private theorem smallReallocGroupS_le_140011 {newSz : Nat} (hle : newSz ≤ MmapThresholdReq) :
    fineSmallReallocGroupS newSz ≤ 140011 := by
  obtain ⟨hsc, _⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.1

private theorem smallAllocGroupS_le_4737_of_le_12 {req : Nat} (h : req ≤ 12) :
    fineSmallAllocGroupS req ≤ 4737 := by
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  obtain ⟨hsc, hrmin⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.1 (Nat.le_trans hrmin h)

private theorem smallAllocGroupS_le_16659_of_le_44 {req : Nat} (h : req ≤ 44) :
    fineSmallAllocGroupS req ≤ 16659 := by
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  obtain ⟨hsc, hrmin⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.2.1 (Nat.le_trans hrmin h)

private theorem smallAllocGroupS_le_34877_of_le_92 {req : Nat} (h : req ≤ 92) :
    fineSmallAllocGroupS req ≤ 34877 := by
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  obtain ⟨hsc, hrmin⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.2.2.1 (Nat.le_trans hrmin h)

private theorem smallAllocGroupS_le_43464_of_le_108 {req : Nat} (h : req ≤ 108) :
    fineSmallAllocGroupS req ≤ 43464 := by
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  obtain ⟨hsc, hrmin⟩ := tightMinReq_le_of_le hle
  have hcell := List.all_eq_true.mp checkFineGroupBuckets_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.2.2.2 (Nat.le_trans hrmin h)

/-- Every `align ≤ 16` `__rust_alloc` increases `fineGroupsScaled` by at most `140,011` (`coarseGrpWtS 8`).
-/
theorem rustAlloc_align16_fine_groupSpec {sz al : Nat} (hal : al ≤ 16) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 140011 := by
  by_cases hle : sz ≤ MmapThresholdReq
  · exact (PhaseGroupSpec.rustAlloc_small fineCostModel hal hle).mono
      (smallAllocGroupS_le_140011 hle)
  · exact (PhaseGroupSpec.rustAlloc_large fineCostModel hal (Nat.lt_of_not_ge hle)).mono
      (by decide : FineScale ≤ 140011)

/-- Every `align ≤ 16` `__rust_realloc` increases `fineGroupsScaled` by at most `140,011`. -/
theorem rustRealloc_align16_fine_groupSpec {oldSz newSz al : Nat} (hal : al ≤ 16) :
    PhaseGroupSpec fineCostModel (· = rustReallocEvents oldSz newSz al) 140011 := by
  by_cases hle : newSz ≤ MmapThresholdReq
  · exact (PhaseGroupSpec.rustRealloc_small fineCostModel hal hle).mono
      (smallReallocGroupS_le_140011 hle)
  · exact (PhaseGroupSpec.rustRealloc_large fineCostModel hal (Nat.lt_of_not_ge hle)).mono
      (by decide : FineScale ≤ 140011)

private theorem rustAlloc_le_12_fine_groupSpec {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 12) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 4737 := by
  have hle : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  exact (PhaseGroupSpec.rustAlloc_small fineCostModel hal hle).mono
    (smallAllocGroupS_le_4737_of_le_12 hsz)

private theorem rustAlloc_le_44_fine_groupSpec {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 44) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 16659 := by
  have hle : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  exact (PhaseGroupSpec.rustAlloc_small fineCostModel hal hle).mono
    (smallAllocGroupS_le_16659_of_le_44 hsz)

private theorem rustAlloc_le_92_fine_groupSpec {sz al : Nat} (hal : al ≤ 16) (hsz : sz ≤ 92) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents sz al) 34877 := by
  have hle : sz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  exact (PhaseGroupSpec.rustAlloc_small fineCostModel hal hle).mono
    (smallAllocGroupS_le_34877_of_le_92 hsz)

/-! ## Linear Secant Group Bounds for `SpqrTightEvs` -/

private def nonFreeStep : AllocEvent → Nat
  | .free _ _ => 0
  | _ => 1

private theorem mul_step_le {m g0 g1 d rhs : Nat}
    (hstep : g1 ≤ g0 + d) (hd : m * d ≤ rhs) :
    m * g1 ≤ m * g0 + rhs := by
  have h1 : m * g1 ≤ m * (g0 + d) := Nat.mul_le_mul_left m hstep
  rw [Nat.mul_add] at h1
  exact Nat.le_trans h1 (Nat.add_le_add_left hd (m * g0))

private theorem chain_linear_step {m g0 g1 g2 c1 c2 e1 e2 n1 n2 : Nat}
    (h1 : m * g1 ≤ m * g0 + (c1 * e1 + c2 * n1))
    (h2 : m * g2 ≤ m * g1 + (c1 * e2 + c2 * n2)) :
    m * g2 ≤ m * g0 + (c1 * (e1 + e2) + c2 * (n2 + n1)) := by
  rw [Nat.mul_add c1, Nat.mul_add c2]
  omega

private theorem le_add_div_of_mul_le {m g0 g1 X : Nat} (hm : 0 < m)
    (h : m * g1 ≤ m * g0 + X) :
    g1 ≤ g0 + X / m := by
  have hlt : m * g1 < m * (g0 + X / m + 1) := by
    have hmod := Nat.div_add_mod X m
    have hrem : X % m < m := Nat.mod_lt X hm
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  have hlt' : g1 < g0 + X / m + 1 := Nat.lt_of_mul_lt_mul_left hlt
  omega

private theorem step_align16_groupsScaled_le_140011 {ev : AllocEvent} (b : fineCostModel.σ)
    (hal : eventStepAlign ev ≤ 16) :
    fineGroupsScaled (fineCostModel.step ev b) ≤
      fineGroupsScaled b + 140011 * nonFreeStep ev := by
  cases ev with
  | free al sz =>
    have hf : fineGroupsScaled (fineCostModel.step (.free al sz) b) ≤ fineGroupsScaled b :=
      HasFineGroupCredit.step_free_le (M := fineCostModel) al sz b
    simp only [nonFreeStep, Nat.mul_zero, Nat.add_zero]
    exact hf
  | alloc req =>
    simp only [nonFreeStep, Nat.mul_one]
    by_cases hle : req ≤ MmapThresholdReq
    · exact Nat.le_trans (HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) b hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_140011 hle) _)
    · exact Nat.le_trans
        (HasFineGroupCredit.step_large_le (M := fineCostModel) (ev := .alloc req) b
          (by simp [eventStepAlign]) (by simpa [eventStepReq] using Nat.lt_of_not_ge hle))
        (Nat.add_le_add_left (by decide : FineScale ≤ 140011) _)
  | aligned al req =>
    simp only [nonFreeStep, Nat.mul_one]
    have hal' : al ≤ 16 := by simpa [eventStepAlign] using hal
    by_cases hle : req ≤ MmapThresholdReq
    · exact Nat.le_trans
        (HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) b hal' hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_140011 hle) _)
    · exact Nat.le_trans
        (HasFineGroupCredit.step_large_le (M := fineCostModel) (ev := .aligned al req) b
          hal (by simpa [eventStepReq] using Nat.lt_of_not_ge hle))
        (Nat.add_le_add_left (by decide : FineScale ≤ 140011) _)
  | realloc al old newSz =>
    simp only [nonFreeStep, Nat.mul_one]
    have hal' : al ≤ 16 := by simpa [eventStepAlign] using hal
    by_cases hle : newSz ≤ MmapThresholdReq
    · exact Nat.le_trans
        (HasFineGroupCredit.step_realloc_small_le (M := fineCostModel) b hal' hle)
        (Nat.add_le_add_left (smallReallocGroupS_le_140011 hle) _)
    · exact Nat.le_trans
        (HasFineGroupCredit.step_large_le (M := fineCostModel) (ev := .realloc al old newSz) b
          hal (by simpa [eventStepReq] using Nat.lt_of_not_ge hle))
        (Nat.add_le_add_left (by decide : FineScale ≤ 140011) _)

private theorem alloc_groupsScaled_linear_le {req : Nat} {g0 g1 : Nat}
    (h12 : req ≤ 12 → g1 ≤ g0 + 4737)
    (h44 : req ≤ 44 → g1 ≤ g0 + 16659)
    (h108 : req ≤ 108 → g1 ≤ g0 + 43464)
    (hany : g1 ≤ g0 + 140011) :
    7792 * g1 ≤ 7792 * g0 + (96547 * spqrAllocTightCost req + 145867129 * 1) := by
  unfold spqrAllocTightCost
  by_cases c12 : req ≤ 12
  · simp only [c12, ↓reduceIte]
    exact mul_step_le (h12 c12) (by decide)
  · simp only [c12, ↓reduceIte]
    by_cases c44 : req ≤ 44
    · simp only [c44, ↓reduceIte]
      exact mul_step_le (h44 c44) (by decide)
    · simp only [c44, ↓reduceIte]
      by_cases c108 : req ≤ 108
      · simp only [c108, ↓reduceIte]
        exact mul_step_le (h108 c108) (by decide)
      · simp only [c108, ↓reduceIte]
        by_cases c2560 : req ≤ 2560
        · simp only [c2560, ↓reduceIte]
          exact mul_step_le hany (by decide)
        · simp only [c2560, ↓reduceIte]
          exact mul_step_le hany (by decide)

private theorem step_groupsScaled_linear_le {ev : AllocEvent} (b : fineCostModel.σ)
    (hal : eventStepAlign ev ≤ 16) :
    7792 * fineGroupsScaled (fineCostModel.step ev b) ≤
      7792 * fineGroupsScaled b +
        (96547 * spqrEventTightCost ev + 145867129 * nonFreeStep ev) := by
  have hany := step_align16_groupsScaled_le_140011 b hal
  cases ev with
  | free al sz =>
    have hf : fineGroupsScaled (fineCostModel.step (.free al sz) b) ≤ fineGroupsScaled b :=
      HasFineGroupCredit.step_free_le (M := fineCostModel) al sz b
    simp only [spqrEventTightCost, nonFreeStep, Nat.mul_zero, Nat.add_zero]
    exact Nat.mul_le_mul_left 7792 hf
  | alloc req =>
    simp only [spqrEventTightCost, nonFreeStep] at hany ⊢
    rw [Nat.mul_one] at hany
    refine alloc_groupsScaled_linear_le
      (fun h12 => ?_) (fun h44 => ?_) (fun h108 => ?_) hany
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans (HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) b hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_4737_of_le_12 h12) _)
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans (HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) b hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_16659_of_le_44 h44) _)
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans (HasFineGroupCredit.step_alloc_small_le (M := fineCostModel) b hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_43464_of_le_108 h108) _)
  | aligned al req =>
    simp only [spqrEventTightCost, nonFreeStep] at hany ⊢
    rw [Nat.mul_one] at hany
    have hal' : al ≤ 16 := by simpa [eventStepAlign] using hal
    refine alloc_groupsScaled_linear_le
      (fun h12 => ?_) (fun h44 => ?_) (fun h108 => ?_) hany
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans
        (HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) b hal' hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_4737_of_le_12 h12) _)
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans
        (HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) b hal' hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_16659_of_le_44 h44) _)
    · have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
      exact Nat.le_trans
        (HasFineGroupCredit.step_aligned_small_le (M := fineCostModel) b hal' hle)
        (Nat.add_le_add_left (smallAllocGroupS_le_43464_of_le_108 h108) _)
  | realloc al old newSz =>
    simp only [spqrEventTightCost, nonFreeStep] at hany ⊢
    rw [Nat.mul_one] at hany
    exact mul_step_le hany (by decide)

private theorem stepEvents_align16_groupsScaled_le :
    ∀ (evs : List AllocEvent) (b : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepAlign ev ≤ 16) →
      fineGroupsScaled (fineCostModel.stepEvents evs b) ≤
        fineGroupsScaled b + 140011 * nonFreeCount evs
  | [], b, _ => by simp [nonFreeCount]
  | ev :: tl, b, hall => by
    rw [AllocCostModel.stepEvents_cons]
    have h1 := step_align16_groupsScaled_le_140011 b (hall ev List.mem_cons_self)
    have h2 := stepEvents_align16_groupsScaled_le tl (fineCostModel.step ev b)
      (fun e he => hall e (List.mem_cons_of_mem _ he))
    have hcnt : nonFreeCount (ev :: tl) = nonFreeCount tl + nonFreeStep ev := by
      cases ev <;> rfl
    rw [hcnt, Nat.mul_add]
    exact Nat.le_trans h2
      (by have := Nat.add_le_add_right h1 (140011 * nonFreeCount tl); omega)

private theorem stepEvents_groupsScaled_linear_le :
    ∀ (evs : List AllocEvent) (b : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepAlign ev ≤ 16) →
      7792 * fineGroupsScaled (fineCostModel.stepEvents evs b) ≤
        7792 * fineGroupsScaled b +
          (96547 * spqrTraceTightCost evs + 145867129 * nonFreeCount evs)
  | [], b, _ => by simp [spqrTraceTightCost, nonFreeCount]
  | ev :: tl, b, hall => by
    rw [AllocCostModel.stepEvents_cons]
    have h1 := step_groupsScaled_linear_le b (hall ev List.mem_cons_self)
    have h2 := stepEvents_groupsScaled_linear_le tl (fineCostModel.step ev b)
      (fun e he => hall e (List.mem_cons_of_mem _ he))
    have hcnt : nonFreeCount (ev :: tl) = nonFreeCount tl + nonFreeStep ev := by
      cases ev <;> rfl
    rw [hcnt]
    exact chain_linear_step h1 h2

/-- `align ≤ 16` `PhaseGroupSpec` (`140,011 * maxOps`) for `SpqrTightEvs maxOps cumCap maxReq`. -/
theorem spqrTightEvs_fine_phaseGroupSpec_align16 (maxOps cumCap maxReq : Nat) :
    PhaseGroupSpec fineCostModel (SpqrTightEvs maxOps cumCap maxReq) (140011 * maxOps) where
  groups_le b {evs} h := by
    have hstep := stepEvents_align16_groupsScaled_le evs b (fun ev hev => (h.2.2.2 ev hev).2)
    exact Nat.le_trans hstep (Nat.add_le_add_left (Nat.mul_le_mul_left 140011 h.1) _)

/-- Secant `PhaseGroupSpec` `ΔgrpS ≤ (96547 * cumCap + 145867129 * maxOps) / 7792` for `SpqrTightEvs`.
-/
theorem spqrTightEvs_fine_phaseGroupSpec_linear (maxOps cumCap maxReq : Nat) :
    PhaseGroupSpec fineCostModel (SpqrTightEvs maxOps cumCap maxReq)
      ((96547 * cumCap + 145867129 * maxOps) / 7792) where
  groups_le b {evs} h := by
    have hlin := stepEvents_groupsScaled_linear_le evs b (fun ev hev => (h.2.2.2 ev hev).2)
    have hcap :
        96547 * spqrTraceTightCost evs + 145867129 * nonFreeCount evs ≤
          96547 * cumCap + 145867129 * maxOps :=
      Nat.add_le_add (Nat.mul_le_mul_left 96547 h.2.1) (Nat.mul_le_mul_left 145867129 h.1)
    have hmul :
        7792 * fineGroupsScaled (fineCostModel.stepEvents evs b) ≤
          7792 * fineGroupsScaled b + (96547 * cumCap + 145867129 * maxOps) :=
      Nat.le_trans hlin (Nat.add_le_add_left hcap _)
    exact le_add_div_of_mul_le (by decide : 0 < 7792) hmul

def decodeStateTightGroupS_split : Nat := 11620913

def statesFromPbTightGroupS_split : Nat := 5504245

def statesIntoPbTightGroupS_split : Nat := 5447474

theorem decodeStateTight_fine_phaseGroupSpec_split :
    PhaseGroupSpec fineCostModel DecodeStateTightEnv decodeStateTightGroupS_split :=
  (spqrTightEvs_fine_phaseGroupSpec_align16 83 1307216 79236).mono (by decide)

theorem statesFromPbTight_fine_phaseGroupSpec_split :
    PhaseGroupSpec fineCostModel StatesFromPbTightEnv statesFromPbTightGroupS_split :=
  (spqrTightEvs_fine_phaseGroupSpec_linear 56 359623 2560).mono (by decide)

theorem statesIntoPbTight_fine_phaseGroupSpec_split :
    PhaseGroupSpec fineCostModel StatesIntoPbTightEnv statesIntoPbTightGroupS_split :=
  (spqrTightEvs_fine_phaseGroupSpec_linear 42 376193 2400).mono (by decide)

/-- Refined `C07TightGroupSpec` (`11,620,913 / 5,504,245 / 5,447,474`) using `align ≤ 16` and secant bounds.
-/
theorem c07TightGroupSpec_split_inst (F : ShaCompress) :
    C07TightGroupSpec F
      (fun _ : Bytes => DecodeStateTightEnv)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      decodeStateTightGroupS_split
      statesFromPbTightGroupS_split
      statesIntoPbTightGroupS_split :=
  ⟨fun _ _ _ _ => decodeStateTight_fine_phaseGroupSpec_split,
   fun _ _ _ => statesFromPbTight_fine_phaseGroupSpec_split,
   fun _ _ _ _ => statesIntoPbTight_fine_phaseGroupSpec_split⟩

/-! ## 12-Arm `<States>::recv` Split Group Bound (`27,105,719`) -/

private theorem addChunkSlot_fine_phaseGroupSpec (s : SortedSetPt) :
    PhaseGroupSpec fineCostModel (AddChunkSlotEnv s) 140011 := by
  unfold AddChunkSlotEnv
  have hgrow : PhaseGroupSpec fineCostModel (· = growOnePtEvents s.vec.length) 140011 := by
    unfold growOnePtEvents
    split
    · exact rustAlloc_align16_fine_groupSpec (by decide)
    · exact rustRealloc_align16_fine_groupSpec (by decide)
  exact ((PhaseGroupSpec.nil fineCostModel).or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 140011, Nat.le_refl 140011⟩)

private theorem addChunkSlots_fine_phaseGroupSpec :
    ∀ (pts : List SortedSetPt),
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) (140011 * pts.length)
  | [] => (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | s :: rest => by
    dsimp only [AddChunkSlotsEnv]
    have h1 := addChunkSlot_fine_phaseGroupSpec s
    have h2 := addChunkSlots_fine_phaseGroupSpec rest
    refine (h1.seq h2).mono ?_
    rw [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem computeAtCall_fine_ge2_le36_phaseGroupSpec {len : Nat}
    (hlo : 2 ≤ len) (hhi : len ≤ 36) :
    PhaseGroupSpec fineCostModel (ComputeAtCallEnv len) 34877 := by
  unfold ComputeAtCallEnv
  have h0 : len ≠ 0 := by omega
  have h1 : len ≠ 1 := by omega
  have halloc : PhaseGroupSpec fineCostModel (· = computeAtAllocEvents len) 34877 := by
    unfold computeAtAllocEvents
    simp only [h0, h1, ↓reduceIte]
    exact rustAlloc_le_92_fine_groupSpec (by decide) (by omega)
  exact seq_freeOnly_right halloc

private theorem computeAtCall_fine_le2_phaseGroupSpec {len : Nat} (hhi : len ≤ 2) :
    PhaseGroupSpec fineCostModel (ComputeAtCallEnv len) 70273 := by
  unfold ComputeAtCallEnv
  have halloc : PhaseGroupSpec fineCostModel (· = computeAtAllocEvents len) 70273 := by
    unfold computeAtAllocEvents
    split
    · exact (rustAlloc_le_12_fine_groupSpec (by decide) (by decide)).mono (by decide)
    · split
      · have ha := rustAlloc_le_12_fine_groupSpec (sz := 2) (al := 2) (by decide) (by decide)
        have hr : PhaseGroupSpec fineCostModel (· = rustReallocEvents 2 8 2) 65536 :=
          (PhaseGroupSpec.rustRealloc_small fineCostModel (oldSz := 2) (newSz := 8) (align := 2)
            (by decide) (by decide)).mono (by decide)
        exact (append_eq_groupSpec ha hr).mono (by decide)
      · exact (rustAlloc_le_12_fine_groupSpec (by decide) (by omega)).mono (by decide)
  exact seq_freeOnly_right halloc

private theorem lagrangeInterpolateMiss_fine_le36_phaseGroupSpec {k : Nat} (hk : k ≤ 36) :
    PhaseGroupSpec fineCostModel (LagrangeInterpolateMissEnv k) 104631 := by
  unfold LagrangeInterpolateMissEnv
  have h1 := rustAlloc_le_92_fine_groupSpec (sz := 2 * k) (al := 2) (by decide) (by omega)
  have h2 := rustAlloc_le_92_fine_groupSpec (sz := 2 * (k + 1)) (al := 2) (by decide) (by omega)
  exact seq_freeOnly_right ((append_eq_groupSpec (append_eq_groupSpec h1 h2) h2).mono (by decide))

private theorem decodedMessageLoopEnv_succ (self : PolyDecoder) (pointsVecs : List (List Pt))
    (i rem : Nat) (polys : List (Option Poly)) :
    DecodedMessageLoopEnv self pointsVecs i (rem + 1) polys =
      match (self.pts[i % 16]?.getD SortedSetPt.new).binarySearch
          { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO } with
      | .ok _ => DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys
      | .error _ =>
        match polys[i % 16]?.getD none with
        | some p =>
          SeqEnv (ComputeAtCallEnv p.coefficients.length)
            (DecodedMessageLoopEnv self pointsVecs (i + 1) rem polys)
        | none =>
          let ptsSlice := pointsVecs[i % 16]?.getD []
          let interp := lagrangeInterpolateTotal ptsSlice
          SeqEnv (LagrangeInterpolateMissEnv ptsSlice.length)
            (SeqEnv (ComputeAtCallEnv interp.coefficients.length)
              (DecodedMessageLoopEnv self pointsVecs (i + 1) rem
                (polys.set (i % 16) (some interp)))) := by
  funext evs
  simp only [DecodedMessageLoopEnv]
  cases (self.pts[i % 16]?.getD SortedSetPt.new).binarySearch
      { x := GF16.new (BitVec.ofNat 16 (i / 16)), y := GF16.ZERO }
  · cases polys[i % 16]?.getD none <;> rfl
  · rfl

private theorem polyCacheRangeBound_replicate_none (lo hi : Nat) :
    ∀ n : Nat, PolyCacheRangeBound lo hi (List.replicate n none)
  | 0 => trivial
  | n + 1 => polyCacheRangeBound_replicate_none lo hi n

private theorem polyCacheRangeBound_getD_some {lo hi : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheRangeBound lo hi polys →
      polys[idx]?.getD none = some p →
      lo ≤ p.coefficients.length ∧ p.coefficients.length ≤ hi
  | [], _, _, _, hget => by simp at hget
  | none :: _, 0, _, _, hget => by simp at hget
  | some _ :: _, 0, p, hdeg, hget => by
    simp only [List.getElem?_cons_zero, Option.getD_some, Option.some.injEq] at hget
    subst hget
    exact hdeg.1
  | none :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheRangeBound_getD_some tl idx p hdeg hget
  | some _ :: tl, idx + 1, p, hdeg, hget => by
    simp only [List.getElem?_cons_succ] at hget
    exact polyCacheRangeBound_getD_some tl idx p hdeg.2 hget

private theorem polyCacheRangeBound_set_some {lo hi : Nat} :
    ∀ (polys : List (Option Poly)) (idx : Nat) (p : Poly),
      PolyCacheRangeBound lo hi polys →
      lo ≤ p.coefficients.length ∧ p.coefficients.length ≤ hi →
      PolyCacheRangeBound lo hi (polys.set idx (some p))
  | [], _, _, _, _ => trivial
  | none :: _, 0, _, hdeg, hp => ⟨hp, hdeg⟩
  | some _ :: _, 0, _, hdeg, hp => ⟨hp, hdeg.2⟩
  | none :: tl, idx + 1, p, hdeg, hp =>
    polyCacheRangeBound_set_some tl idx p hdeg hp
  | some _ :: tl, idx + 1, p, hdeg, hp =>
    ⟨hdeg.1, polyCacheRangeBound_set_some tl idx p hdeg.2 hp⟩

private theorem collectedSlices_getD_range_ge32_le576 {dec : PolyDecoder}
    (hfst : (collectPointsVecsTotal dec 0 16 false []).1 = false)
    (hge32 : 32 ≤ dec.ptsNeeded) (hle576 : dec.ptsNeeded ≤ 576)
    {poly : Nat} (hpoly : poly < 16) :
    2 ≤ ((collectedSlices dec 0 16)[poly]?.getD []).length ∧
      ((collectedSlices dec 0 16)[poly]?.getD []).length ≤ 36 := by
  have hlen : (collectedSlices dec 0 16).length = 16 := collectedSlices_length dec 16 0
  have hpoly' : poly < (collectedSlices dec 0 16).length := hlen ▸ hpoly
  rw [List.getElem?_eq_getElem hpoly', Option.getD_some, collectedSlices_getElem dec 16 0 poly hpoly,
    Nat.zero_add, List.length_take]
  have hnec_le : dec.necessaryPoints poly ≤ (dec.pts[poly]?.getD SortedSetPt.new).len :=
    (collectPointsVecsTotal_of_fst_false dec 16 0 false [] hfst).2.2 poly (by omega) (by omega)
  have hnec_lo : 2 ≤ dec.necessaryPoints poly := by
    unfold PolyDecoder.necessaryPoints
    dsimp only
    split <;> omega
  have hnec_hi : dec.necessaryPoints poly ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    dsimp only
    split <;> omega
  dsimp only [SortedSetPt.asSlice, SortedSetPt.len] at hnec_le ⊢
  omega

private theorem loop_step_mono_none {cHit cMiss rem m' : Nat} :
    cMiss + (cHit + (cHit * rem + cMiss * m')) ≤ cHit * (rem + 1) + cMiss * (m' + 1) := by
  rw [Nat.mul_add cHit, Nat.mul_one, Nat.mul_add cMiss, Nat.mul_one]
  omega

private theorem loop_step_mono_hit {cHit cMiss rem m : Nat} :
    cHit + (cHit * rem + cMiss * m) ≤ cHit * (rem + 1) + cMiss * m := by
  rw [Nat.mul_add cHit, Nat.mul_one]
  omega

private theorem loop_step_mono_ok {cHit cMiss rem m : Nat} :
    cHit * rem + cMiss * m ≤ cHit * (rem + 1) + cMiss * m := by
  rw [Nat.mul_add cHit, Nat.mul_one]
  omega

private theorem decodedMessageLoop_fine_ge2_le36_phaseGroupSpec
    (self : PolyDecoder) (pointsVecs : List (List Pt))
    (hSlices : ∀ poly < 16,
      2 ≤ (pointsVecs[poly]?.getD []).length ∧ (pointsVecs[poly]?.getD []).length ≤ 36) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheRangeBound 2 36 polys →
      PhaseGroupSpec fineCostModel (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (34877 * rem + 104631 * m)
  | 0, _, _, _, _, _, _ => (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ]
    split
    · exact (decodedMessageLoop_fine_ge2_le36_phaseGroupSpec self pointsVecs hSlices
        rem (i + 1) m polys hlen hcnt hdeg).mono loop_step_mono_ok
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        obtain ⟨hp_lo, hp_hi⟩ := polyCacheRangeBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_fine_ge2_le36_phaseGroupSpec hp_lo hp_hi
        have hTail := decodedMessageLoop_fine_ge2_le36_phaseGroupSpec self pointsVecs hSlices
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono loop_step_mono_hit
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        obtain ⟨hsl_lo, hsl_hi⟩ := hSlices (i % 16) hpoly
        have hint_eq := lagrangeInterpolateTotal_length ptsSlice
        have hint_lo : 2 ≤ interp.coefficients.length := hint_eq ▸ hsl_lo
        have hint_hi : interp.coefficients.length ≤ 36 := hint_eq ▸ hsl_hi
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheRangeBound 2 36 (polys.set (i % 16) (some interp)) :=
            polyCacheRangeBound_set_some polys (i % 16) interp hdeg ⟨hint_lo, hint_hi⟩
          have hMiss := lagrangeInterpolateMiss_fine_le36_phaseGroupSpec hsl_hi
          have hComp := computeAtCall_fine_ge2_le36_phaseGroupSpec hint_lo hint_hi
          have hTail := decodedMessageLoop_fine_ge2_le36_phaseGroupSpec self pointsVecs hSlices
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono loop_step_mono_none

private theorem decodedMessageLoop_fine_le2_phaseGroupSpec
    (self : PolyDecoder) (pointsVecs : List (List Pt))
    (hSlices : ∀ poly < 16, (pointsVecs[poly]?.getD []).length ≤ 2) :
    ∀ (rem i m : Nat) (polys : List (Option Poly)),
      polys.length = 16 →
      polyNoneCount polys ≤ m →
      PolyCacheDegBound 2 polys →
      PhaseGroupSpec fineCostModel (DecodedMessageLoopEnv self pointsVecs i rem polys)
        (70273 * rem + 104631 * m)
  | 0, _, _, _, _, _, _ => (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | rem + 1, i, m, polys, hlen, hcnt, hdeg => by
    rw [decodedMessageLoopEnv_succ]
    split
    · exact (decodedMessageLoop_fine_le2_phaseGroupSpec self pointsVecs hSlices
        rem (i + 1) m polys hlen hcnt hdeg).mono loop_step_mono_ok
    · cases hopt : polys[i % 16]?.getD none with
      | some p =>
        dsimp only
        have hp_hi : p.coefficients.length ≤ 2 :=
          polyCacheDegBound_getD_some polys (i % 16) p hdeg hopt
        have hComp := computeAtCall_fine_le2_phaseGroupSpec hp_hi
        have hTail := decodedMessageLoop_fine_le2_phaseGroupSpec self pointsVecs hSlices
          rem (i + 1) m polys hlen hcnt hdeg
        exact (hComp.seq hTail).mono loop_step_mono_hit
      | none =>
        dsimp only
        have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
        have hpoly_lt : i % 16 < polys.length := hlen ▸ hpoly
        let ptsSlice := pointsVecs[i % 16]?.getD []
        let interp := lagrangeInterpolateTotal ptsSlice
        have hsl_hi : ptsSlice.length ≤ 2 := hSlices (i % 16) hpoly
        have hint_hi : interp.coefficients.length ≤ 2 :=
          (lagrangeInterpolateTotal_length ptsSlice) ▸ hsl_hi
        have hcnt_eq := polyNoneCount_set_some_eq polys (i % 16) interp hpoly_lt hopt
        cases m with
        | zero => omega
        | succ m' =>
          have hlen' : (polys.set (i % 16) (some interp)).length = 16 := by simp [hlen]
          have hcnt' : polyNoneCount (polys.set (i % 16) (some interp)) ≤ m' := by omega
          have hdeg' : PolyCacheDegBound 2 (polys.set (i % 16) (some interp)) :=
            polyCacheDegBound_set_some polys (i % 16) interp hdeg hint_hi
          have hMiss := lagrangeInterpolateMiss_fine_le36_phaseGroupSpec
            (Nat.le_trans hsl_hi (by decide))
          have hComp := computeAtCall_fine_le2_phaseGroupSpec hint_hi
          have hTail := decodedMessageLoop_fine_le2_phaseGroupSpec self pointsVecs hSlices
            rem (i + 1) m' (polys.set (i % 16) (some interp)) hlen' hcnt' hdeg'
          exact (hMiss.seq (hComp.seq hTail)).mono loop_step_mono_none

/-- `PhaseGroupSpec` (`22,002,657` scaled units = `336` groups) for `<PolyDecoder as Decoder>::decoded_message` when `dec.ptsNeeded ≤ 576`.
-/
theorem decodedMessage_fine_phaseGroupSpec_split {dec : PolyDecoder}
    (hpts : dec.ptsNeeded ≤ 576) :
    PhaseGroupSpec fineCostModel (DecodedMessageEnv dec) 22002657 := by
  unfold DecodedMessageEnv
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · split
    · have h256 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 256 8) 99398 :=
        (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 256) (align := 8)
          (by decide) (by decide)).mono (by decide)
      exact (seq_freeOnly_right h256).mono (by decide)
    · rename_i _ hnot_or
      have hor_false :
          ((collectPointsVecsTotal dec 0 16 false []).1 || decide (dec.ptsNeeded = 0)) = false :=
        Bool.eq_false_iff.mpr hnot_or
      obtain ⟨hfst, _⟩ := Bool.or_eq_false_iff.mp hor_false
      have h256 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 256 8) 99398 :=
        (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 256) (align := 8)
          (by decide) (by decide)).mono (by decide)
      have hout := rustAlloc_align16_fine_groupSpec (sz := 2 * dec.ptsNeeded) (al := 1) (by decide)
      have hHead := append_eq_groupSpec h256 hout
      by_cases hge32 : 32 ≤ dec.ptsNeeded
      · have hLoop := (decodedMessageLoop_fine_ge2_le36_phaseGroupSpec dec
          (collectedSlices dec 0 16)
          (fun poly hpoly => collectedSlices_getD_range_ge32_le576 hfst hge32 hpts hpoly)
          dec.ptsNeeded 0 16 (List.replicate 16 none)
          (by simp) (by rw [polyNoneCount_replicate_none])
          (polyCacheRangeBound_replicate_none 2 36 16)).mono
          (Nat.le_trans
            (Nat.add_le_add_right (Nat.mul_le_mul_left 34877 hpts) (104631 * 16))
            (by decide : 34877 * 576 + 104631 * 16 ≤ 21763248))
        exact (hHead.seq (seq_freeOnly_right hLoop)).mono (by decide)
      · have hle31 : dec.ptsNeeded ≤ 31 := by omega
        have hSlices2 : ∀ poly < 16, ((collectedSlices dec 0 16)[poly]?.getD []).length ≤ 2 := by
          intro poly hpoly
          have hle := collectedSlices_getD_length_le dec hpoly
          omega
        have hLoop := (decodedMessageLoop_fine_le2_phaseGroupSpec dec
          (collectedSlices dec 0 16) hSlices2
          dec.ptsNeeded 0 16 (List.replicate 16 none)
          (by simp) (by rw [polyNoneCount_replicate_none])
          (polyCacheDegBound_replicate_none 2 16)).mono
          (Nat.le_trans
            (Nat.add_le_add_right (Nat.mul_le_mul_left 70273 hle31) (104631 * 16))
            (by decide : 70273 * 31 + 104631 * 16 ≤ 21763248))
        exact (hHead.seq (seq_freeOnly_right hLoop)).mono (by decide)

private theorem replicate_flatten_groupSpec {evs0 : List AllocEvent} {g : Nat}
    (h : PhaseGroupSpec fineCostModel (· = evs0) g) :
    ∀ n : Nat, PhaseGroupSpec fineCostModel (· = (List.replicate n evs0).flatten) (n * g)
  | 0 => by simpa using PhaseGroupSpec.nil fineCostModel
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons, Nat.succ_mul]
    exact (append_eq_groupSpec h (replicate_flatten_groupSpec h n)).mono
      (Nat.le_of_eq (Nat.add_comm g (n * g)))

private theorem encodeBytes_160_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 160) 2083248 := by
  have hcond : 160 ≤ 1048576 ∧ 160 % 2 = 0 ∧ 0 < 160 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h160 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 160 2) 130203 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 160) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h160 16).mono (by decide)

private theorem encodeBytes_1152_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 1152) 524288 := by
  have hcond : 1152 ≤ 1048576 ∧ 1152 % 2 = 0 ∧ 0 < 1152 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h1152 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 1152 2) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 1152) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h1152 16).mono (by decide)

private theorem sliceConcat2Events_align16_phaseGroupSpec (n : Nat) :
    PhaseGroupSpec fineCostModel (· = sliceConcat2Events n) 140011 := by
  unfold sliceConcat2Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 140011)
  · exact rustAlloc_align16_fine_groupSpec (by decide)

private theorem libcruxHmacSha256_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = libcruxHmacSha256Events) 121290 := by
  unfold libcruxHmacSha256Events
  have ha64 := rustAlloc_le_92_fine_groupSpec (sz := 64) (al := 1) (by decide) (by decide)
  have hd64 := PhaseGroupSpec.rustDealloc fineCostModel 64 1
  have ha32 := rustAlloc_le_44_fine_groupSpec (sz := 32) (al := 1) (by decide) (by decide)
  exact (append_eq_groupSpec
    (append_eq_groupSpec
      (append_eq_groupSpec
        (append_eq_groupSpec
          (append_eq_groupSpec
            (append_eq_groupSpec ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono (by decide)

private theorem sendCt2Seg23_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (· = sendCt2Seg23Events es) 205547 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
  split
  · have h2080 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 2080 1) 65536 :=
      (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 2080) (align := 1)
        (by decide) (by decide)).mono (by decide)
    have hd2080 := PhaseGroupSpec.rustDealloc fineCostModel 2080 1
    exact (append_eq_groupSpec (append_eq_groupSpec h2080 h128) hd2080).mono (by decide)
  · simpa only [List.nil_append, List.append_nil] using h128.mono (by decide)

private theorem sendCt2Reserve128_fine_phaseGroupSpec (ct1Len : Nat) :
    PhaseGroupSpec fineCostModel (SendCt2Reserve128Env ct1Len) 140011 where
  groups_le b {evs} := by
    rintro (rfl | ⟨cap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2ConcatHmac_960_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = sendCt2ConcatHmacEvents 960) 154058 := by
  unfold sendCt2ConcatHmacEvents
  have hc : PhaseGroupSpec fineCostModel (· = rustAllocEvents (35 + 8 + (960 + 128)) 1) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 35 + 8 + (960 + 128)) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact (append_eq_groupSpec hc libcruxHmacSha256_fine_phaseGroupSpec).mono (by decide)

private theorem unchunkedSendCt2BySizes_960_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (UnchunkedSendCt2BySizesEnv es 960) 499616 := by
  unfold UnchunkedSendCt2BySizesEnv
  have h1 := sendCt2Seg23_fine_phaseGroupSpec es
  have h2 := sendCt2Reserve128_fine_phaseGroupSpec 960
  have h3 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (((h1.concat h2).concat h3).concat h4).mono (by decide)

private theorem sendCt2EncoderGrow_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderGrowEnv 128 32) 140011 where
  groups_le b {evs} := by
    rintro (⟨_, rfl⟩ | ⟨newCap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2Encoder_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderEnv 128 32) 2363270 := by
  unfold SendCt2EncoderEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec 128
  have h2 := sendCt2EncoderGrow_128_32_fine_phaseGroupSpec
  have h3 := encodeBytes_160_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by decide)

private theorem recvEkChunkSendCt2Tail_960_fine_phaseGroupSpec
    (sendCt2OnDone : Bool) (es : Bytes) (optEk : Option Bytes) :
    PhaseGroupSpec fineCostModel (RecvEkChunkSendCt2TailEnv sendCt2OnDone es 960 optEk) 2862886 := by
  cases optEk with
  | none => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  | some ekBytes =>
    by_cases hcond : (sendCt2OnDone && (ekBytes.length == 1184)) = true
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es 960 (some ekBytes) =
            SeqEnv (UnchunkedSendCt2BySizesEnv es 960)
              (SeqEnv (SendCt2EncoderEnv 128 32) FreeOnlyEvs) := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact ((unchunkedSendCt2BySizes_960_fine_phaseGroupSpec es).seq
        (seq_freeOnly_right sendCt2Encoder_128_32_fine_phaseGroupSpec)).mono (by decide)
    · have heq :
          RecvEkChunkSendCt2TailEnv sendCt2OnDone es 960 (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [RecvEkChunkSendCt2TailEnv, hcond]
      rw [heq]
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

private theorem authUpdate_fine_phaseGroupSpec (rootKeyLen kLen : Nat) :
    PhaseGroupSpec fineCostModel (AuthUpdateEnv rootKeyLen kLen) 700055 := by
  unfold AuthUpdateEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec (rootKeyLen + kLen)
  have h2 := sliceConcat2Events_align16_phaseGroupSpec (Authenticator.updateLabel.length + 8)
  have h3 := rustAlloc_align16_fine_groupSpec (sz := 64) (al := 1) (by decide)
  have h4 := rustAlloc_align16_fine_groupSpec (sz := 32) (al := 1) (by decide)
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq (h4.seq (hf.seq (h4.seq hf)))))).mono (by decide)

private theorem recvCt2ChunkTail_960_fine_phaseGroupSpec (rootKeyLen : Nat) (optCt2 : Option Bytes) :
    PhaseGroupSpec fineCostModel (RecvCt2ChunkTailEnv rootKeyLen 960 optCt2) 1574156 := by
  cases optCt2 with
  | none => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  | some ct2Full =>
    by_cases hlt : ct2Full.length < 128
    · have heq : RecvCt2ChunkTailEnv rootKeyLen 960 (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    · have heq :
          RecvCt2ChunkTailEnv rootKeyLen 960 (some ct2Full) =
            SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
              (SeqEnv (· = rustAllocEvents 32 1)
                (SeqEnv (· = sliceConcat2Events 41)
                  (SeqEnv (· = rustAllocEvents 32 1)
                    (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                      (SeqEnv (SendCt2Reserve128Env 960)
                        (SeqEnv (· = sendCt2ConcatHmacEvents 960) FreeOnlyEvs)))))) := by
        funext evs; simp [RecvCt2ChunkTailEnv, hlt]
      rw [heq]
      have h1 : PhaseGroupSpec fineCostModel (· = recvCt2AllocMacCt2Events ct2Full.length) 280022 := by
        unfold recvCt2AllocMacCt2Events
        have ha : PhaseGroupSpec fineCostModel
            (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
            140011 := by
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact rustAlloc_align16_fine_groupSpec (by decide)
        have hb := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
        exact append_eq_groupSpec ha hb
      have h32 := rustAlloc_le_44_fine_groupSpec (sz := 32) (al := 1) (by decide) (by decide)
      have h41 := sliceConcat2Events_align16_phaseGroupSpec 41
      have h5 := authUpdate_fine_phaseGroupSpec rootKeyLen 32
      have h6 := sendCt2Reserve128_fine_phaseGroupSpec 960
      have h7 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
      have h8 := PhaseGroupSpec.freeOnly fineCostModel
      exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq (h7.seq h8))))))).mono (by decide)

/-- Scaled slot-group bound for `<States>::recv` (`27,105,719` = `414` groups). -/
def statesRecvTightGroupS_split : Nat := 27105719

/-- `PhaseGroupSpec` (`27,105,719`) for `StatesRecvEnv st msg` across all 12 dispatch arms under `StatesProtocolSizes` and `StatesDecPtsNeededBound`.
-/
theorem statesRecv_tight_phaseGroupSpec_split {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseGroupSpec fineCostModel (StatesRecvEnv st msg) statesRecvTightGroupS_split := by
  have hFree : PhaseGroupSpec fineCostModel FreeOnlyEvs statesRecvTightGroupS_split :=
    (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  have hSlots16 : ∀ (pts : List SortedSetPt), pts.length = 16 →
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) 2240176 := fun pts hlen => by
    have h := addChunkSlots_fine_phaseGroupSpec pts
    rw [hlen] at h
    exact h.mono (by decide)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := hSlots16 (List.replicate 16 SortedSetPt.new) (by simp)
      have h2 : PhaseGroupSpec fineCostModel (SeqEnv (EncodeBytesEnv s.uc.ek.length) FreeOnlyEvs)
          524288 := by
        rw [hproto]
        exact seq_freeOnly_right encodeBytes_1152_fine_phaseGroupSpec
      exact (h1.seq h2).mono (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hr_pts : (addChunkTotal s.receiving_ct1 chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ct1 chunk; omega
        have h1 := hSlots16 s.receiving_ct1.pts hproto
        have h2 := seq_freeOnly_right (decodedMessage_fine_phaseGroupSpec_split hr_pts)
        exact (h1.seq h2).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly_right (hSlots16 (List.replicate 16 SortedSetPt.new) (by simp))).mono
        (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hbody : PhaseGroupSpec fineCostModel
            (EkSentCt1ReceivedRecvCt2ChunkEnv s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold EkSentCt1ReceivedRecvCt2ChunkEnv
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_ct2 chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_ct2.pts hlen16
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 : PhaseGroupSpec fineCostModel
                (RecvCt2ChunkTailEnv s.uc.auth.rootKey.length s.uc.ct1.length
                  (decodedMessageTotal rCt2)) 1574156 := by
              rw [hct1]
              exact recvCt2ChunkTail_960_fine_phaseGroupSpec s.uc.auth.rootKey.length
                (decodedMessageTotal rCt2)
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [StatesRecvEnv]
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : PhaseGroupSpec fineCostModel
            (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_hdr chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_hdr.pts hproto
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 := PhaseGroupSpec.of_nonFreeBound fineCostModel
              (recvHdrChunkTail_nonFreeBound (decodedMessageTotal rHdr))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseGroupSpec fineCostModel
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            statesRecvTightGroupS_split := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 : PhaseGroupSpec fineCostModel
            (RecvEkChunkSendCt2TailEnv ack s.uc.es s.uc.ct1.length (decodedMessageTotal rEk))
            2862886 := by
          rw [hct1]
          exact recvEkChunkSendCt2Tail_960_fine_phaseGroupSpec ack s.uc.es (decodedMessageTotal rEk)
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
        dsimp only [StatesProtocolSizes] at hproto
        have h1 : PhaseGroupSpec fineCostModel
            (UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length) 499616 := by
          rw [hproto]
          exact unchunkedSendCt2BySizes_960_fine_phaseGroupSpec s.uc.es
        have h2 := seq_freeOnly_right sendCt2Encoder_128_32_fine_phaseGroupSpec
        exact (h1.seq h2).mono (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv]
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk),
          PhaseGroupSpec fineCostModel
            (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
              (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                (RecvEkChunkSendCt2TailEnv true s.uc.es s.uc.ct1.length
                  (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
            statesRecvTightGroupS_split := fun chunk => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 : PhaseGroupSpec fineCostModel
            (RecvEkChunkSendCt2TailEnv true s.uc.es s.uc.ct1.length (decodedMessageTotal rEk))
            2862886 := by
          rw [hct1]
          exact recvEkChunkSendCt2Tail_960_fine_phaseGroupSpec true s.uc.es (decodedMessageTotal rEk)
        exact (h1.seq (h2.seq h3)).mono (by decide)
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _
    · exact hFree
  | ct2Sampled _ => exact hFree

theorem statesRecv_tight_of_from_pb_phaseGroupSpec_split {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    PhaseGroupSpec fineCostModel (StatesRecvEnv st msg) statesRecvTightGroupS_split :=
  statesRecv_tight_phaseGroupSpec_split st msg
    (StatesProtocolSizes.of_from_pb hfrom)
    (StatesDecPtsNeededBound.of_from_pb hfrom)

theorem statesRecvProtoEnv_tight_groupSpec_split {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (_hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseGroupSpec fineCostModel (StatesRecvProtoEnv st0 msg) statesRecvTightGroupS_split := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [statesRecvProtoEnv_eq_of_protocolSizes hproto msg]
    exact statesRecv_tight_phaseGroupSpec_split st0 msg hproto hpts
  · have heq : StatesRecvProtoEnv st0 msg = FreeOnlyEvs := by
      unfold StatesRecvProtoEnv; simp [hb]
    rw [heq]
    exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

/-- `StatesRecvTightGroupSpec` instance for `StatesRecvProtoEnv` (`27,105,719` = `414` groups). -/
theorem c09aStatesRecvTightGroupSpec_split_inst (F : ShaCompress) :
    StatesRecvTightGroupSpec F StatesRecvProtoEnv statesRecvTightGroupS_split :=
  ⟨fun st0 msg hpts hpts640 hraw46 =>
    statesRecvProtoEnv_tight_groupSpec_split st0 msg hpts hpts640 hraw46⟩

/-! ## Split `spqr::recv` and `try_decrypt` `PhaseGroupSpec` Bounds -/

/-- Scaled slot-group bound for the `Ordering::Equal` branch of `spqr::recv` (`459,164,942` = `7,007` groups).
-/
def spqrRecvEqualTightGroupS_split : Nat := 459164942

/-- Scaled slot-group bound for `spqr::recv` (`470,785,855` = `7,184` groups). -/
def spqrRecvTightGroupS_split : Nat := 470785855

/-- Scaled slot-group bound for `W2TryDecryptTightEnv` parametric in `maxSteps`. -/
def w2TryDecryptTightGroupS_split (maxSteps : Nat) : Nat :=
  42 * FineScale + 6 * 16659 + 11056 + w2Seg4CmkFineGrpS maxSteps + spqrRecvTightGroupS_split

/-- Closed scaled slot-group bound for `W2TryDecryptTightEnv` when `maxSteps ≤ 12` (`509,326,673` = `7,772` groups).
-/
def w2TryDecryptTightGroupS_split_12 : Nat := 509326673

def w2TryDecryptTightGroupS_split_10 : Nat := 508933457

/-- Split `Ordering::Equal` `PhaseGroupSpec` (`459,164,942`) on `StatesRecvProtoEnv`. -/
theorem spqrRecvOrderingEqual_c07_c09a_phaseGroupSpec_tight_split
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
      spqrRecvEqualTightGroupS_split := by
  unfold SpqrRecvEqualC07TightEnv
  exact (spqrRecvOrderingEqual_phaseGroupSpec_tight F K
    (c07TightGroupSpec_split_inst F) (c09aStatesRecvTightGroupSpec_split_inst F)
    hv1Pts hv1Raw hParams hPrev).mono (by decide)

theorem spqrRecvOrderingEqual_c07_c09a_phaseGroupSpec_tight_split_rawEnv
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
      (SpqrRecvEqualC07TightEnv F K StatesRecvEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      spqrRecvEqualTightGroupS_split := by
  rw [← spqrRecvEqualC07TightEnv_proto_eq]
  exact spqrRecvOrderingEqual_c07_c09a_phaseGroupSpec_tight_split F K
    hv1Pts hv1Raw hParams hPrev

/-- Split `spqr::recv` `PhaseGroupSpec` (`470,785,855`, independent of `xRk.G`) on `SpqrRecvC07TightEnv`.
-/
theorem spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split
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
      spqrRecvTightGroupS_split := by
  unfold SpqrRecvC07TightEnv
  exact (spqrRecvParts_phaseGroupSpec_tight F K
    (c07TightGroupSpec_split_inst F) (c09aStatesRecvTightGroupSpec_split_inst F)
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono (by decide)

theorem spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split_rawEnv
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
      spqrRecvTightGroupS_split := by
  rw [← spqrRecvC07TightEnv_proto_eq]
  exact spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split F K
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom

/-- `maxSteps`-parametric `PhaseGroupSpec` for `W2TryDecryptTightEnv` at `StatesRecvProtoEnv`. -/
theorem w2TryDecryptTightEnv_fine_groupSpec_split
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightGroupS_split maxSteps) :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

theorem w2TryDecryptTightEnv_fine_groupSpec_split_rawEnv
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightGroupS_split maxSteps) :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

/-- Closed `509,326,673` `PhaseGroupSpec` for `W2TryDecryptTightEnv` when `caps.length ≤ 12`. -/
theorem w2TryDecryptTightEnv_fine_groupSpec_split_12
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_12 :=
  (w2TryDecryptTightEnv_fine_groupSpec_split F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hDom).mono
    (by decide)

theorem w2TryDecryptTightEnv_fine_groupSpec_split_rawEnv_12
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_12 :=
  (w2TryDecryptTightEnv_fine_groupSpec_split_rawEnv F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hDom).mono
    (by decide)

theorem w2TryDecryptTightEnv_fine_groupSpec_split_10
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_10 :=
  (w2TryDecryptTightEnv_fine_groupSpec_split F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hDom).mono
    (by decide)

theorem w2TryDecryptTightEnv_fine_groupSpec_split_rawEnv_10
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTightGroupS_split_10 :=
  (w2TryDecryptTightEnv_fine_groupSpec_split_rawEnv F K dhCap needGrow withAddr errAlloc ctLen
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hDom).mono
    (by decide)

theorem w2TryDecryptEnv_fine_groupSpec_split
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (63 * FineScale + (3 * FineScale * 2000 + maxSteps * (3 * FineScale)) +
        spqrRecvTightGroupS_split) :=
  w2TryDecryptEnv_of_seg4_groupSpec fineCostModel dhCap needGrow caps withAddr errAlloc ctLen
    (w2Seg4CmkStepEnv_groupSpec fineCostModel hcaps)
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

theorem w2TryDecryptFailEnv_fine_groupSpec_split
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
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (45 * FineScale + (3 * FineScale * 2000 + maxSteps * (3 * FineScale)) +
        spqrRecvTightGroupS_split) :=
  w2TryDecryptFailEnv_of_seg4_groupSpec fineCostModel dhCap needGrow caps withAddr errAlloc ctLen
    (w2Seg4CmkStepEnv_groupSpec fineCostModel hcaps)
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_split F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
