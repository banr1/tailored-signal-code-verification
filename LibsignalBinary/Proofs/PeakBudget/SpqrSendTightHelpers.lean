/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget

/-!
# Tight `fineCostModel` Sub-Phase Credit Helpers for `spqr::send`

Proves closed `fineCostModel` `PhaseCreditSpec` and `nonFreeCount` bounds in binary call order for
`.rodata`-sized `<PolyEncoder>::next_chunk` (`0x6a384`), all 11 arms of `<States>::send`
(`Δcum = 2,124,238`, `Δlive = Δpeak = 0`, `nonFreeCount ≤ 1,233`), `spqr::chain_from`,
`<Chain>::add_epoch`, `<Chain>::send_key`, `<Chain>::into_pb`, and `<Message>::serialize`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator ChainPB HkdfFn Point Poly PolyEncoder PqRatchetState States VersionNegotiationPB
   chainNextInfo spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainEpochGhost ChainIntoPbCall ChainSendKeyGhost chainEpochAlign
   chainEpochSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents
   rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost fineSmallReallocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq
   fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12 smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv FreeOnlyAlign16Evs IterSeqEnv PhaseCreditSpec iterPeak)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (smallAllocCost_le_9789_of_le_2560
   smallAllocCost_le_90234_of_le_79236 smallReallocCost_le_9789_of_le_384)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendCreditHelpers
  (AuthMacHdrEnv AuthUpdateEnv MessageSerializeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (ComputeAtOptEnv FineSmallEvs authMacHdr_fine_phaseCreditSpec authMacHdr_nonFreeCount_le
   authUpdate_fine_32_phaseCreditSpec authUpdate_nonFreeCount_le
   boundedCount_fine_cap_phaseCreditSpec
   computeAtCall_fine_rodata_phaseCreditSpec computeAtCall_nonFreeCount_le computeAtOps
   computeAtOpt_fine_rodata_phaseCreditSpec computeAtOpt_nonFreeCount_exact_le computeAtRodataCum
   encodeBytes_fine_96_phaseCreditSpec encodeBytes_fine_960_phaseCreditSpec
   encodeBytes_nonFreeCount_le fineSmallAlloc_72 fineSmallAlloc_96 fineSmallAlloc_112
   fineSmallAlloc_120 fineSmallAlloc_136 fineSmallAlloc_144 fineSmallAlloc_224 fineSmallAlloc_336
   fineSmallAlloc_384 fineSmallAlloc_448 fineSmallAlloc_720 fineSmallAlloc_816 fineSmallAlloc_864
   fineSmallEvs_phaseCreditSpec fineSmallRealloc_448 fineSmallRealloc_672
   fineSmallRealloc_896 nonFreeCount_iterSeqEnv_const_le nonFreeCount_iterSeqEnv_le
   nonFreeCount_rustAlloc nonFreeCount_rustDealloc nonFreeCount_rustRealloc_le nonFreeCount_seqEnv_le
   nonFreeCount_sliceConcat2_le rustAlloc_fine_phaseCreditSpec sliceConcat2_fine_phaseCreditSpec
   smallAllocCost_le_1607_of_le_72)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
  (growOrReallocEvents growOrReallocStepCum phaseCreditSpec_growOrRealloc)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
  (allocLargeLive_of_le allocStepCum reallocStepCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (NextKeyInternalEnv nextKeyInternalEvents sliceConcat2Events vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
  (ChainSendKeyEnv chainEpochPopEvents chainSendKeyEvents chainSendKeyPopEvents)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (HkdfToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (ComputeAtCallEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (EncodeBytesEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromEnv ChainFromVersionNegotiationEnv chainNewEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)

/-! ## `.rodata` `<PolyEncoder>::next_chunk` and `<States>::send` Envelopes -/

/-- Precomputed `.rodata` Lagrange point counts in libsignal's SPQR V1 parameters (`n ∈ {0, 1, 3, 5, 30, 34, 36}`).
-/
def isRodataPtLen (n : Nat) : Bool :=
  n == 0 || n == 1 || n == 3 || n == 5 || n == 30 || n == 34 || n == 36

/-- Validity of a `PolyEncoder` under `.rodata` Lagrange sizes (`≤ 16` slots, `isRodataPtLen` point counts, polynomial lengths `≤ 36`).
-/
def EncRodataValid (enc : PolyEncoder) : Prop :=
  match enc.s with
  | .points pts => pts.length ≤ 16 ∧ ∀ pt ∈ pts, isRodataPtLen pt.value.length = true
  | .polys polys => polys.length ≤ 16 ∧ ∀ p ∈ polys, p.coefficients.length ≤ 36

/-- Lifts `EncRodataValid` and 32-byte authenticator root-key bounds across all `States` variants.
-/
def StatesRodataValid {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => EncRodataValid s.sending_hdr
  | .headerSent s => EncRodataValid s.sending_ek
  | .ct1Received s => EncRodataValid s.sending_ek
  | .ekSentCt1Received _ => True
  | .noHeaderReceived _ => True
  | .headerReceived s => (Authenticator.intoPb s.uc.auth).rootKey.length ≤ 32
  | .ct1Sampled s => EncRodataValid s.sending_ct1
  | .ekReceivedCt1Sampled s => EncRodataValid s.sending_ct1
  | .ct1Acknowledged _ => True
  | .ct2Sampled s => EncRodataValid s.sending_ct2

/-- Single-slot `points_to_polys` allocator trace envelope (`Poly::zero` at `n = 0`, or `enumeratePts`, `const_polys_to_polys`, and `Poly::lagrange_sum` at `n > 0`).
-/
def PolyNextChunkRodataConvStepEnv (n : Nat) : List AllocEvent → Prop :=
  if n = 0 then
    SeqEnv (fun evs => evs = [] ∨ evs = rustAllocEvents 2 2) FreeOnlyEvs
  else
    SeqEnv (· = rustAllocEvents (4 * n) 2)
      (SeqEnv (· = rustAllocEvents (24 * n) 8)
        (SeqEnv (IterSeqEnv (fun _ => SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs) (List.range n))
          (SeqEnv (· = rustAllocEvents (2 * n) 2)
            (SeqEnv (IterSeqEnv (fun _ => SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs) (List.range n))
              FreeOnlyEvs))))

/-- Binary-order allocator trace envelope of `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`) on `.points pts`.
-/
def PolyNextChunkRodataPointsEnv (pts : List Point) : List AllocEvent → Prop :=
  fun evs =>
    evs = [] ∨
      SeqEnv (· = rustAllocEvents 384 8)
        (SeqEnv (IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16))
          (SeqEnv (IterSeqEnv (fun pt => PolyNextChunkRodataConvStepEnv pt.value.length) pts)
            (SeqEnv FreeOnlyEvs
              (SeqEnv (IterSeqEnv (fun pt => ComputeAtOptEnv pt.value.length) pts)
                FreeOnlyEvs)))) evs

def PolyNextChunkRodataPointsFixedEnv (numSlots slotLen : Nat) : List AllocEvent → Prop :=
  fun evs =>
    evs = [] ∨
      SeqEnv (· = rustAllocEvents 384 8)
        (SeqEnv (IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16))
          (SeqEnv (IterSeqEnv (fun _ => PolyNextChunkRodataConvStepEnv slotLen) (List.range numSlots))
            (SeqEnv FreeOnlyEvs
              (SeqEnv (IterSeqEnv (fun _ => ComputeAtOptEnv slotLen) (List.range numSlots))
                FreeOnlyEvs)))) evs

/-- Binary-order `.rodata` allocator trace envelope of `<PolyEncoder as Encoder>::next_chunk` on `enc`.
-/
def PolyNextChunkRodataEnv (enc : PolyEncoder) : List AllocEvent → Prop :=
  match enc.s with
  | .points pts => PolyNextChunkRodataPointsEnv pts
  | .polys polys =>
    SeqEnv (IterSeqEnv (fun p => ComputeAtCallEnv p.coefficients.length) polys) FreeOnlyEvs

/-- Binary-order allocator trace envelope of `<States>::send` across all 11 chunked variants under `.rodata` Lagrange sizes.
-/
def StatesSendRodataEnv (F : ShaCompress) :
    States spqrPolyApi (spqrAuthApi F) → List AllocEvent → Prop
  | .keysUnsampled _ =>
    SeqEnv (FineSmallEvs 8 85736 2400)
      (SeqEnv AuthMacHdrEnv
        (SeqEnv (· = sliceConcat2Events 96)
          (SeqEnv (EncodeBytesEnv 96)
            (SeqEnv (PolyNextChunkRodataPointsFixedEnv 16 3) FreeOnlyEvs))))
  | .keysSampled s => PolyNextChunkRodataEnv s.sending_hdr
  | .headerSent s => PolyNextChunkRodataEnv s.sending_ek
  | .ct1Received s => PolyNextChunkRodataEnv s.sending_ek
  | .ekSentCt1Received _ => (· = [])
  | .noHeaderReceived _ => (· = [])
  | .headerReceived s =>
    SeqEnv (FineSmallEvs 8 83176 2080)
      (SeqEnv (· = sliceConcat2Events 41)
        (SeqEnv (HkdfToVecEnv 32)
          (SeqEnv (AuthUpdateEnv (Authenticator.intoPb s.uc.auth).rootKey.length 32)
            (SeqEnv (EncodeBytesEnv 960)
              (SeqEnv (PolyNextChunkRodataPointsFixedEnv 16 30) FreeOnlyEvs)))))
  | .ct1Sampled s => PolyNextChunkRodataEnv s.sending_ct1
  | .ekReceivedCt1Sampled s => PolyNextChunkRodataEnv s.sending_ct1
  | .ct1Acknowledged _ => (· = [])
  | .ct2Sampled s => PolyNextChunkRodataEnv s.sending_ct2

/-- `cumSmall` charge of `PolyNextChunkRodataConvStepEnv n` at `.rodata` point counts. -/
def rodataConvStepCum : Nat → Nat
  | 0 => 188
  | 1 => 1240
  | 3 => 3111
  | 5 => 12345
  | 30 => 111322
  | 34 => 124178
  | _ => 130606

def rodataConvOps (n : Nat) : Nat :=
  if n = 0 then 1 else 2 * n + 3

private theorem isRodataPtLen_cases {n : Nat} (h : isRodataPtLen n = true) :
    n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 30 ∨ n = 34 ∨ n = 36 := by
  unfold isRodataPtLen at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((h0 | h1) | h3) | h5) | h30) | h34) | h36
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h30))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h34)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h36)))))

theorem isRodataPtLen_le_36 {n : Nat} (h : isRodataPtLen n = true) : n ≤ 36 := by
  rcases isRodataPtLen_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem rodataConv_pos_phaseCreditSpec {n c4 c24 c2 : Nat}
    (hn_pos : 0 < n) (hn_le : n ≤ 36)
    (h4 : HasFineReallocCredit.smallAllocCost fineCostModel (4 * n) ≤ c4)
    (h24 : HasFineReallocCredit.smallAllocCost fineCostModel (24 * n) ≤ c24)
    (h2 : HasFineReallocCredit.smallAllocCost fineCostModel (2 * n) ≤ c2) :
    PhaseCreditSpec fineCostModel (PolyNextChunkRodataConvStepEnv n)
      (c4 + (c24 + (n * c2 + (c2 + (n * c2 + 0))))) 0 0 864 := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn_pos
  unfold PolyNextChunkRodataConvStepEnv
  simp only [hne, ↓reduceIte]
  have ha4 : PhaseCreditSpec fineCostModel (· = rustAllocEvents (4 * n) 2) c4 0 0 (4 * n) :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by omega) h4
  have ha24 : PhaseCreditSpec fineCostModel (· = rustAllocEvents (24 * n) 8) c24 0 0 (24 * n) :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by omega) h24
  have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents (2 * n) 2) c2 0 0 (2 * n) :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by omega) h2
  have hfree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hstep : PhaseCreditSpec fineCostModel
      (SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs) c2 0 0 (2 * n) :=
    (ha2.seq hfree).mono (Nat.le_of_eq (Nat.add_zero c2)) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
  have hloop : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun _ => SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs) (List.range n))
      (n * c2) 0 0 (2 * n) := by
    simpa [List.length_range] using PhaseCreditSpec.iter_zero_live (List.range n) (fun _ _ => hstep)
  have h := ha4.seq (ha24.seq (hloop.seq (ha2.seq (hloop.seq hfree))))
  exact h.mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)

private theorem fineSmallAlloc_20_le :
    HasFineReallocCredit.smallAllocCost fineCostModel 20 ≤ 488 := by decide +kernel

private theorem fineSmallAlloc_24_le :
    HasFineReallocCredit.smallAllocCost fineCostModel 24 ≤ 488 := by decide +kernel

theorem polyNextChunkRodataConvStep_fine_phaseCreditSpec {n : Nat}
    (hn : isRodataPtLen n = true) :
    PhaseCreditSpec fineCostModel (PolyNextChunkRodataConvStepEnv n)
      (rodataConvStepCum n) 0 0 864 := by
  rcases isRodataPtLen_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold PolyNextChunkRodataConvStepEnv rodataConvStepCum
    simp only [↓reduceIte]
    have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 2 2) 188 0 0 2 :=
      rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
        (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
    have hor := (PhaseCreditSpec.nil fineCostModel).or ha2
    exact (hor.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
      fineSmallAlloc_24_le
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
      (smallAllocCost_le_1607_of_le_72 (by decide))
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      fineSmallAlloc_20_le
      (Nat.le_of_eq fineSmallAlloc_120)
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq fineSmallAlloc_120)
      (Nat.le_of_eq fineSmallAlloc_720)
      (smallAllocCost_le_1607_of_le_72 (by decide))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq fineSmallAlloc_136)
      (Nat.le_of_eq fineSmallAlloc_816)
      (smallAllocCost_le_1607_of_le_72 (by decide))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)
  · exact (rodataConv_pos_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq fineSmallAlloc_144)
      (Nat.le_of_eq fineSmallAlloc_864)
      (Nat.le_of_eq fineSmallAlloc_72)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 864)

theorem polyNextChunkRodataConvStep_nonFreeCount_exact_le (n : Nat)
    {evs : List AllocEvent} (h : PolyNextChunkRodataConvStepEnv n evs) :
    nonFreeCount evs ≤ rodataConvOps n := by
  unfold PolyNextChunkRodataConvStepEnv rodataConvOps at *
  by_cases h0 : n = 0
  · simp only [h0, ↓reduceIte] at h ⊢
    have hstep0 : ∀ e, (e = [] ∨ e = rustAllocEvents 2 2) → nonFreeCount e ≤ 1 := by
      intro e he
      rcases he with rfl | rfl
      · exact Nat.zero_le 1
      · rw [nonFreeCount_rustAlloc]
    have hc : nonFreeCount evs ≤ 1 + 0 :=
      nonFreeCount_seqEnv_le hstep0
        (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h
    exact hc
  · simp only [h0, ↓reduceIte] at h ⊢
    have hstep : ∀ e, SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs e →
        nonFreeCount e ≤ 1 := by
      intro e hs
      have hc : nonFreeCount e ≤ 1 + 0 :=
        nonFreeCount_seqEnv_le
          (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
          (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) hs
      exact hc
    have hloop : ∀ e,
        IterSeqEnv (fun _ => SeqEnv (· = rustAllocEvents (2 * n) 2) FreeOnlyEvs) (List.range n) e →
        nonFreeCount e ≤ n := by
      intro e he
      have hc := nonFreeCount_iterSeqEnv_const_le (List.range n) (fun _ _ => hstep) he
      simpa [List.length_range] using hc
    have hc : nonFreeCount evs ≤ 1 + (1 + (n + (1 + (n + 0)))) :=
      nonFreeCount_seqEnv_le (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
        (fun _ h2 => nonFreeCount_seqEnv_le (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
          (fun _ h3 => nonFreeCount_seqEnv_le hloop
            (fun _ h4 => nonFreeCount_seqEnv_le (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
              (fun _ h5 => nonFreeCount_seqEnv_le hloop
                (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h5) h4) h3) h2) h
    omega

private theorem rodataSlotSum_le_132213 {n : Nat} (hn : isRodataPtLen n = true) :
    rodataConvStepCum n + computeAtRodataCum n ≤ 132213 := by
  rcases isRodataPtLen_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem rodataSlotOps_le_76 {n : Nat} (hn : n ≤ 36) :
    rodataConvOps n + computeAtOps n ≤ 76 := by
  unfold rodataConvOps computeAtOps
  split <;> split <;> omega

private theorem iterPeak_zero_zero {α : Type} (xs : List α) :
    iterPeak (fun _ : α => 0) (fun _ => 0) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => simp [iterPeak, ih]

private theorem foldr_max_le_of_forall {α : Type} (f : α → Nat) (cap : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≤ cap) → (xs.map f).foldr max 0 ≤ cap
  | [], _ => Nat.zero_le cap
  | x :: tl, h => by
    simp only [List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨h x List.mem_cons_self,
      foldr_max_le_of_forall f cap tl (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

private theorem sum_map_add_le_const {α : Type} (f g : α → Nat) (cap : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x + g x ≤ cap) →
      (xs.map f).sum + (xs.map g).sum ≤ xs.length * cap
  | [], _ => by simp
  | x :: tl, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hx := h x List.mem_cons_self
    have htl := sum_map_add_le_const f g cap tl (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hpair : (f x + (tl.map f).sum) + (g x + (tl.map g).sum) =
        ((tl.map f).sum + (tl.map g).sum) + (f x + g x) := by omega
    rw [hpair]
    exact Nat.add_le_add htl hx

/-- `PhaseCreditSpec` on `fineCostModel` for `PolyNextChunkRodataPointsEnv pts` (`Δcum = 2,124,238`, `Δlive = Δpeak = 0`, `maxReq = 864`).
-/
theorem polyNextChunkRodataPoints_fine_phaseCreditSpec {pts : List Point}
    (hlen : pts.length ≤ 16)
    (hpts : ∀ pt ∈ pts, isRodataPtLen pt.value.length = true) :
    PhaseCreditSpec fineCostModel (PolyNextChunkRodataPointsEnv pts)
      2124238 0 0 864 := by
  have ha384 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 384 8) 5822 0 0 384 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_384)
  have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 2 2) 188 0 0 2 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
  have hinit : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16)) 3008 0 0 2 :=
    (PhaseCreditSpec.iter_zero_live (List.range 16) (fun _ _ => ha2)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 2)
  have hconv_iter := PhaseCreditSpec.iter
    (fun pt : Point => rodataConvStepCum pt.value.length)
    (fun _ => 0) (fun _ => 0) (fun _ => 864) pts
    (fun pt hpt => polyNextChunkRodataConvStep_fine_phaseCreditSpec (hpts pt hpt))
  have hconv : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun pt => PolyNextChunkRodataConvStepEnv pt.value.length) pts)
      ((pts.map (fun pt => rodataConvStepCum pt.value.length)).sum) 0 0 864 :=
    hconv_iter.mono (Nat.le_refl _) (by simp) (Nat.le_of_eq (iterPeak_zero_zero pts))
      (foldr_max_le_of_forall (fun _ => 864) 864 pts (fun _ _ => Nat.le_refl 864))
  have hcomp_iter := PhaseCreditSpec.iter
    (fun pt : Point => computeAtRodataCum pt.value.length)
    (fun _ => 0) (fun _ => 0) (fun pt => max 8 (2 * pt.value.length)) pts
    (fun pt hpt => computeAtOpt_fine_rodata_phaseCreditSpec (isRodataPtLen_le_36 (hpts pt hpt)))
  have hcomp : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun pt => ComputeAtOptEnv pt.value.length) pts)
      ((pts.map (fun pt => computeAtRodataCum pt.value.length)).sum) 0 0 72 :=
    hcomp_iter.mono (Nat.le_refl _) (by simp) (Nat.le_of_eq (iterPeak_zero_zero pts))
      (foldr_max_le_of_forall (fun pt : Point => max 8 (2 * pt.value.length)) 72 pts
        (fun pt hpt => by have := isRodataPtLen_le_36 (hpts pt hpt); omega))
  have hfree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hslow := ha384.seq (hinit.seq (hconv.seq (hfree.seq (hcomp.seq hfree))))
  have hsum_pts :
      (pts.map (fun pt => rodataConvStepCum pt.value.length)).sum +
        (pts.map (fun pt => computeAtRodataCum pt.value.length)).sum ≤ 16 * 132213 :=
    Nat.le_trans
      (sum_map_add_le_const
        (fun pt : Point => rodataConvStepCum pt.value.length)
        (fun pt : Point => computeAtRodataCum pt.value.length)
        132213 pts (fun pt hpt => rodataSlotSum_le_132213 (hpts pt hpt)))
      (Nat.mul_le_mul_right 132213 hlen)
  have hslow_cum :
      5822 + (3008 + ((pts.map (fun pt => rodataConvStepCum pt.value.length)).sum +
        (0 + ((pts.map (fun pt => computeAtRodataCum pt.value.length)).sum + 0)))) ≤ 2124238 := by
    simp only [Nat.zero_add, Nat.add_zero]
    rw [← Nat.add_assoc 5822 3008]
    exact Nat.le_trans (Nat.add_le_add_left hsum_pts (5822 + 3008)) (by decide)
  have hslow' : PhaseCreditSpec fineCostModel _ 2124238 0 0 864 :=
    hslow.mono hslow_cum (by decide) (by decide) (by decide)
  exact ((PhaseCreditSpec.nil fineCostModel).or hslow').mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem polyNextChunkRodataPoints_nonFreeCount_le {pts : List Point}
    (hlen : pts.length ≤ 16)
    (hpts : ∀ pt ∈ pts, isRodataPtLen pt.value.length = true)
    {evs : List AllocEvent} (h : PolyNextChunkRodataPointsEnv pts evs) :
    nonFreeCount evs ≤ 1233 := by
  rcases h with rfl | hslow
  · exact Nat.zero_le 1233
  · have hinit : ∀ e,
        IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16) e →
        nonFreeCount e ≤ 16 := by
      intro e he
      have hc := nonFreeCount_iterSeqEnv_const_le (List.range 16)
        (fun _ _ _ ha => by subst ha; rw [nonFreeCount_rustAlloc]) he
      simpa [List.length_range] using hc
    have hconv : ∀ e,
        IterSeqEnv (fun pt => PolyNextChunkRodataConvStepEnv pt.value.length) pts e →
        nonFreeCount e ≤ (pts.map (fun pt => rodataConvOps pt.value.length)).sum :=
      fun _ he => nonFreeCount_iterSeqEnv_le
        (fun pt => rodataConvOps pt.value.length) pts
        (fun pt _ _ hs => polyNextChunkRodataConvStep_nonFreeCount_exact_le pt.value.length hs) he
    have hcomp : ∀ e,
        IterSeqEnv (fun pt => ComputeAtOptEnv pt.value.length) pts e →
        nonFreeCount e ≤ (pts.map (fun pt => computeAtOps pt.value.length)).sum :=
      fun _ he => nonFreeCount_iterSeqEnv_le
        (fun pt => computeAtOps pt.value.length) pts
        (fun pt _ _ hs => computeAtOpt_nonFreeCount_exact_le pt.value.length hs) he
    have hfree : ∀ e, FreeOnlyEvs e → nonFreeCount e ≤ 0 :=
      fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)
    have hc := nonFreeCount_seqEnv_le (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
      (fun _ h2 => nonFreeCount_seqEnv_le hinit
        (fun _ h3 => nonFreeCount_seqEnv_le hconv
          (fun _ h4 => nonFreeCount_seqEnv_le hfree
            (fun _ h5 => nonFreeCount_seqEnv_le hcomp hfree h5) h4) h3) h2) hslow
    have hsum := Nat.le_trans
      (sum_map_add_le_const
        (fun pt : Point => rodataConvOps pt.value.length)
        (fun pt : Point => computeAtOps pt.value.length)
        76 pts (fun pt hpt => rodataSlotOps_le_76 (isRodataPtLen_le_36 (hpts pt hpt))))
      (Nat.mul_le_mul_right 76 hlen)
    simp only [Nat.zero_add, Nat.add_zero] at hc
    rw [← Nat.add_assoc 1 16] at hc
    exact Nat.le_trans hc (Nat.le_trans (Nat.add_le_add_left hsum 17) (by decide))

theorem polyNextChunkRodataPointsFixed_fine_phaseCreditSpec (numSlots slotLen : Nat)
    (hsl : isRodataPtLen slotLen = true) :
    PhaseCreditSpec fineCostModel (PolyNextChunkRodataPointsFixedEnv numSlots slotLen)
      (5822 + 3008 + numSlots * (rodataConvStepCum slotLen + computeAtRodataCum slotLen))
      0 0 864 := by
  have ha384 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 384 8) 5822 0 0 384 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_384)
  have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 2 2) 188 0 0 2 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
      (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
  have hinit : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16)) 3008 0 0 2 :=
    (PhaseCreditSpec.iter_zero_live (List.range 16) (fun _ _ => ha2)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 2)
  have hconv : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun _ => PolyNextChunkRodataConvStepEnv slotLen) (List.range numSlots))
      (numSlots * rodataConvStepCum slotLen) 0 0 864 := by
    simpa [List.length_range] using PhaseCreditSpec.iter_zero_live (List.range numSlots)
      (fun _ _ => polyNextChunkRodataConvStep_fine_phaseCreditSpec hsl)
  have hcomp : PhaseCreditSpec fineCostModel
      (IterSeqEnv (fun _ => ComputeAtOptEnv slotLen) (List.range numSlots))
      (numSlots * computeAtRodataCum slotLen) 0 0 72 := by
    have hstep : PhaseCreditSpec fineCostModel (ComputeAtOptEnv slotLen)
        (computeAtRodataCum slotLen) 0 0 72 :=
      (computeAtOpt_fine_rodata_phaseCreditSpec (isRodataPtLen_le_36 hsl)).mono
        (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
        (by have := isRodataPtLen_le_36 hsl; omega)
    simpa [List.length_range] using
      PhaseCreditSpec.iter_zero_live (List.range numSlots) (fun _ _ => hstep)
  have hfree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hslow := ha384.seq (hinit.seq (hconv.seq (hfree.seq (hcomp.seq hfree))))
  have hcum_eq :
      5822 + (3008 + (numSlots * rodataConvStepCum slotLen +
        (0 + (numSlots * computeAtRodataCum slotLen + 0)))) =
        5822 + 3008 + numSlots * (rodataConvStepCum slotLen + computeAtRodataCum slotLen) := by
    simp only [Nat.zero_add, Nat.add_zero, Nat.left_distrib, Nat.add_assoc]
  have hslow' : PhaseCreditSpec fineCostModel _
      (5822 + 3008 + numSlots * (rodataConvStepCum slotLen + computeAtRodataCum slotLen))
      0 0 864 :=
    hslow.mono (Nat.le_of_eq hcum_eq) (by decide) (by decide) (by decide)
  exact ((PhaseCreditSpec.nil fineCostModel).or hslow').mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem polyNextChunkRodataPointsFixed_nonFreeCount_le (numSlots slotLen : Nat)
    {evs : List AllocEvent} (h : PolyNextChunkRodataPointsFixedEnv numSlots slotLen evs) :
    nonFreeCount evs ≤ 17 + numSlots * (rodataConvOps slotLen + computeAtOps slotLen) := by
  rcases h with rfl | hslow
  · exact Nat.zero_le _
  · have hinit : ∀ e,
        IterSeqEnv (fun _ => (· = rustAllocEvents 2 2)) (List.range 16) e →
        nonFreeCount e ≤ 16 := by
      intro e he
      have hc := nonFreeCount_iterSeqEnv_const_le (List.range 16)
        (fun _ _ _ ha => by subst ha; rw [nonFreeCount_rustAlloc]) he
      simpa [List.length_range] using hc
    have hconv : ∀ e,
        IterSeqEnv (fun _ => PolyNextChunkRodataConvStepEnv slotLen) (List.range numSlots) e →
        nonFreeCount e ≤ numSlots * rodataConvOps slotLen := by
      intro e he
      have hc := nonFreeCount_iterSeqEnv_const_le (List.range numSlots)
        (fun _ _ _ hs => polyNextChunkRodataConvStep_nonFreeCount_exact_le slotLen hs) he
      simpa [List.length_range] using hc
    have hcomp : ∀ e,
        IterSeqEnv (fun _ => ComputeAtOptEnv slotLen) (List.range numSlots) e →
        nonFreeCount e ≤ numSlots * computeAtOps slotLen := by
      intro e he
      have hc := nonFreeCount_iterSeqEnv_const_le (List.range numSlots)
        (fun _ _ _ hs => computeAtOpt_nonFreeCount_exact_le slotLen hs) he
      simpa [List.length_range] using hc
    have hfree : ∀ e, FreeOnlyEvs e → nonFreeCount e ≤ 0 :=
      fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)
    have hc := nonFreeCount_seqEnv_le (fun _ ha => by subst ha; rw [nonFreeCount_rustAlloc])
      (fun _ h2 => nonFreeCount_seqEnv_le hinit
        (fun _ h3 => nonFreeCount_seqEnv_le hconv
          (fun _ h4 => nonFreeCount_seqEnv_le hfree
            (fun _ h5 => nonFreeCount_seqEnv_le hcomp hfree h5) h4) h3) h2) hslow
    simp only [Nat.zero_add, Nat.add_zero] at hc
    have heq : 1 + (16 + (numSlots * rodataConvOps slotLen + numSlots * computeAtOps slotLen)) =
        17 + numSlots * (rodataConvOps slotLen + computeAtOps slotLen) := by
      rw [Nat.left_distrib]
      omega
    rw [heq] at hc
    exact hc

/-- `PhaseCreditSpec` on `fineCostModel` for `PolyNextChunkRodataEnv enc` under `EncRodataValid enc`.
-/
theorem polyNextChunkRodata_fine_phaseCreditSpec {enc : PolyEncoder}
    (hb : EncRodataValid enc) :
    PhaseCreditSpec fineCostModel (PolyNextChunkRodataEnv enc) 2124238 0 0 864 := by
  unfold PolyNextChunkRodataEnv EncRodataValid at *
  cases hs : enc.s with
  | points pts =>
    simp only [hs] at hb ⊢
    exact polyNextChunkRodataPoints_fine_phaseCreditSpec hb.1 hb.2
  | polys polys =>
    simp only [hs] at hb ⊢
    obtain ⟨hlen, hpolys⟩ := hb
    have hstep : ∀ p ∈ polys,
        PhaseCreditSpec fineCostModel (ComputeAtCallEnv p.coefficients.length) 8513 0 0 72 := by
      intro p hp
      have hp_le := hpolys p hp
      have hc_le : computeAtRodataCum p.coefficients.length ≤ 8513 := by
        unfold computeAtRodataCum
        by_cases h1 : p.coefficients.length = 1
        · simp [h1]
        · by_cases h6 : p.coefficients.length ≤ 6 <;> simp [h1, h6]
      exact (computeAtCall_fine_rodata_phaseCreditSpec hp_le).mono hc_le
        (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hiter := PhaseCreditSpec.iter_zero_live polys hstep
    have hseq := hiter.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)
    have hcum : polys.length * 8513 + 0 ≤ 2124238 := by omega
    exact hseq.mono hcum (by decide) (by decide) (by decide)

theorem polyNextChunkRodata_nonFreeCount_le {enc : PolyEncoder}
    (hb : EncRodataValid enc) {evs : List AllocEvent}
    (h : PolyNextChunkRodataEnv enc evs) :
    nonFreeCount evs ≤ 1233 := by
  unfold PolyNextChunkRodataEnv EncRodataValid at *
  cases hs : enc.s with
  | points pts =>
    rw [hs] at hb h
    exact polyNextChunkRodataPoints_nonFreeCount_le hb.1 hb.2 h
  | polys polys =>
    rw [hs] at hb h
    obtain ⟨hlen, _⟩ := hb
    have hc := nonFreeCount_seqEnv_le
      (fun _ hi => nonFreeCount_iterSeqEnv_const_le polys
        (fun p _ _ hp => computeAtCall_nonFreeCount_le p.coefficients.length hp) hi)
      (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h
    exact Nat.le_trans hc (Nat.le_trans (Nat.mul_le_mul_right 2 hlen) (by decide))

theorem statesSendRodata_keysUnsampled_fine_phaseCreditSpec (F : ShaCompress)
    (s : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    PhaseCreditSpec fineCostModel (StatesSendRodataEnv F (.keysUnsampled s))
      188855 0 0 2400 := by
  dsimp only [StatesSendRodataEnv]
  have h1 : PhaseCreditSpec fineCostModel (FineSmallEvs 8 85736 2400) 85736 0 0 2400 :=
    fineSmallEvs_phaseCreditSpec 8 85736 (by decide)
  have h2 := authMacHdr_fine_phaseCreditSpec
  have h3 : PhaseCreditSpec fineCostModel (· = sliceConcat2Events 96) 1997 0 0 96 :=
    sliceConcat2_fine_phaseCreditSpec (by decide) (Nat.le_of_eq fineSmallAlloc_96)
  have h4 := encodeBytes_fine_96_phaseCreditSpec
  have h5 := polyNextChunkRodataPointsFixed_fine_phaseCreditSpec 16 3 (by decide)
  have h6 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono
    (by decide) (by decide) (by decide) (by decide)

theorem statesSendRodata_headerReceived_fine_phaseCreditSpec (F : ShaCompress)
    (s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hrk : (Authenticator.intoPb s.uc.auth).rootKey.length ≤ 32) :
    PhaseCreditSpec fineCostModel (StatesSendRodataEnv F (.headerReceived s))
      1962258 0 0 2080 := by
  dsimp only [StatesSendRodataEnv]
  have h1 : PhaseCreditSpec fineCostModel (FineSmallEvs 8 83176 2080) 83176 0 0 2080 :=
    fineSmallEvs_phaseCreditSpec 8 83176 (by decide)
  have h2 : PhaseCreditSpec fineCostModel (· = sliceConcat2Events 41) 738 0 0 41 :=
    sliceConcat2_fine_phaseCreditSpec (by decide) (smallAllocCost_le_738_of_le_44 (by decide))
  have h3 : PhaseCreditSpec fineCostModel (HkdfToVecEnv 32) 738 0 0 32 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
      (smallAllocCost_le_738_of_le_44 (by decide))
  have h4 := authUpdate_fine_32_phaseCreditSpec hrk
  have h5 := encodeBytes_fine_960_phaseCreditSpec
  have h6 := polyNextChunkRodataPointsFixed_fine_phaseCreditSpec 16 30 (by decide)
  have h7 := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Unified `cumSmall` bound (`2,124,238` bytes) for `StatesSendRodataEnv` across all 11 arms. -/
def statesSendRodataDeltaCum : Nat := 2124238
def statesSendRodataMaxReq : Nat := 2400

theorem statesSendRodata_fine_phaseCreditSpec (F : ShaCompress)
    {st : States spqrPolyApi (spqrAuthApi F)} (hb : StatesRodataValid st) :
    PhaseCreditSpec fineCostModel (StatesSendRodataEnv F st)
      statesSendRodataDeltaCum 0 0 statesSendRodataMaxReq := by
  cases st with
  | keysUnsampled s =>
    exact (statesSendRodata_keysUnsampled_fine_phaseCreditSpec F s).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  | headerReceived s =>
    exact (statesSendRodata_headerReceived_fine_phaseCreditSpec F s hb).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  | ekSentCt1Received _ | noHeaderReceived _ | ct1Acknowledged _ =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | keysSampled _ | headerSent _ | ct1Received _ | ct1Sampled _ | ekReceivedCt1Sampled _
  | ct2Sampled _ =>
    exact (polyNextChunkRodata_fine_phaseCreditSpec hb).mono
      (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

theorem statesSendRodata_nonFreeCount_le (F : ShaCompress)
    {st : States spqrPolyApi (spqrAuthApi F)} (hb : StatesRodataValid st)
    {evs : List AllocEvent} (h : StatesSendRodataEnv F st evs) :
    nonFreeCount evs ≤ 1233 := by
  cases st with
  | keysUnsampled _ =>
    unfold StatesSendRodataEnv at h
    have hc := nonFreeCount_seqEnv_le (fun _ h1 => h1.1)
      (fun _ h2 => nonFreeCount_seqEnv_le (fun _ ha => authMacHdr_nonFreeCount_le ha)
        (fun _ h3 => nonFreeCount_seqEnv_le
          (fun _ hs => by subst hs; exact nonFreeCount_sliceConcat2_le 96)
          (fun _ h4 => nonFreeCount_seqEnv_le (fun _ he => encodeBytes_nonFreeCount_le 96 he)
            (fun _ h5 => nonFreeCount_seqEnv_le
              (fun _ hp => polyNextChunkRodataPointsFixed_nonFreeCount_le 16 3 hp)
              (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h5) h4) h3) h2) h
    exact Nat.le_trans hc (by decide)
  | headerReceived _ =>
    unfold StatesSendRodataEnv at h
    have hc := nonFreeCount_seqEnv_le (fun _ h1 => h1.1)
      (fun _ h2 => nonFreeCount_seqEnv_le
        (fun _ hs => by subst hs; exact nonFreeCount_sliceConcat2_le 41)
        (fun _ h3 => nonFreeCount_seqEnv_le
          (fun _ hk => by unfold HkdfToVecEnv at hk; subst hk; rw [nonFreeCount_rustAlloc])
          (fun _ h4 => nonFreeCount_seqEnv_le (fun _ ha => authUpdate_nonFreeCount_le ha)
            (fun _ h5 => nonFreeCount_seqEnv_le (fun _ he => encodeBytes_nonFreeCount_le 960 he)
              (fun _ h6 => nonFreeCount_seqEnv_le
                (fun _ hp => polyNextChunkRodataPointsFixed_nonFreeCount_le 16 30 hp)
                (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h6) h5) h4) h3) h2) h
    exact Nat.le_trans hc (by decide)
  | ekSentCt1Received _ | noHeaderReceived _ | ct1Acknowledged _ =>
    subst h
    exact Nat.zero_le 1233
  | keysSampled _ | headerSent _ | ct1Received _ | ct1Sampled _ | ekReceivedCt1Sampled _
  | ct2Sampled _ =>
    exact polyNextChunkRodata_nonFreeCount_le hb h

/-- Witness-free small-class envelope for `<States>::send` under `.rodata` sizes (`≤ 1,233` ops, `Δcum ≤ 2,124,238`, `maxReq = 2,400`).
-/
def StatesSendRodataTightEnv : List AllocEvent → Prop :=
  FineSmallEvs 1233 2124238 2400

theorem statesSendRodataTight_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel StatesSendRodataTightEnv 2124238 0 0 2400 :=
  fineSmallEvs_phaseCreditSpec 1233 2124238 (by decide)

/-! ## Tight Chain, `Message::serialize`, and `PqRatchetState::encode_to_vec` Envelopes -/

/-- Witness-free small-class envelope for `spqr::chain_from` (`≤ 6` ops, `Δcum ≤ 10,919`, `maxReq = 448`).
-/
def ChainFromTightEnv : List AllocEvent → Prop :=
  FineSmallEvs 6 10919 448

theorem chainFromTight_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainFromTightEnv 10919 0 0 448 :=
  fineSmallEvs_phaseCreditSpec 6 10919 (by decide)

theorem chainFromEnv_to_tight (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    {evs : List AllocEvent} (h : ChainFromEnv pb vn evs) :
    ChainFromTightEnv evs := by
  cases pb with
  | some _ => exact FineSmallEvs.of_freeOnly 6 10919 448 h
  | none =>
    cases vn with
    | none => subst h; exact FineSmallEvs.nil 6 10919 448
    | some _ =>
      dsimp only [ChainFromEnv] at h
      unfold ChainFromVersionNegotiationEnv at h
      split at h
      · subst h
        unfold chainNewEvents
        have ha72 : FineSmallEvs 1 1607 448 (rustAllocEvents 72 1) :=
          FineSmallEvs.rustAlloc (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_72)
        have ha32 : FineSmallEvs 1 738 448 (rustAllocEvents 32 1) :=
          FineSmallEvs.rustAlloc (by decide) (by decide)
            (smallAllocCost_le_738_of_le_44 (by decide))
        have ha448 : FineSmallEvs 1 5491 448 (rustAllocEvents 448 8) :=
          FineSmallEvs.rustAlloc (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_448)
        exact (((((ha72.append ha32).append ha72).append ha32).append ha448).append ha32).mono
          (by decide) (by decide) (by decide)
      · subst h; exact FineSmallEvs.nil 6 10919 448

/-- `PhaseCreditSpec` on `fineCostModel` for `ChainFromEnv pb vn` (`Δcum = 10,919`, `Δlive = Δpeak = 0`).
-/
theorem chainFrom_fine_phaseCreditSpec (pb : Option ChainPB)
    (vn : Option VersionNegotiationPB) :
    PhaseCreditSpec fineCostModel (ChainFromEnv pb vn) 10919 0 0 448 :=
  chainFromTight_fine_phaseCreditSpec.of_imp fun _ => chainFromEnv_to_tight pb vn

theorem chainFrom_nonFreeCount_le (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    {evs : List AllocEvent} (h : ChainFromEnv pb vn evs) :
    nonFreeCount evs ≤ 6 :=
  (chainFromEnv_to_tight pb vn h).1

private theorem growOrReallocStepCum_vecDeque_le_9213 {k : Nat} (hk : k ≤ 4) :
    growOrReallocStepCum fineCostModel (k * 112) (max (2 * k) 4 * 112) 8 ≤ 9213 := by
  unfold growOrReallocStepCum allocStepCum reallocStepCum
  rw [fineCostModel_smallMaxReq_eq]
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · change (if 448 ≤ 135167 then fineSmallAllocCost 448 else 122) ≤ 9213
    simp only [fineSmallAlloc_448]
    decide
  · change (if 448 ≤ 135167 then if 8 ≤ 448 then fineSmallReallocCost 448
      else fineSmallAllocCost 448 else 122) ≤ 9213
    simp only [fineSmallRealloc_448]
    decide
  · change (if 448 ≤ 135167 then if 8 ≤ 448 then fineSmallReallocCost 448
      else fineSmallAllocCost 448 else 122) ≤ 9213
    simp only [fineSmallRealloc_448]
    decide
  · change (if 672 ≤ 135167 then if 8 ≤ 672 then fineSmallReallocCost 672
      else fineSmallAllocCost 672 else 122) ≤ 9213
    simp only [fineSmallRealloc_672]
    decide
  · change (if 896 ≤ 135167 then if 8 ≤ 896 then fineSmallReallocCost 896
      else fineSmallAllocCost 896 else 122) ≤ 9213
    simp only [fineSmallRealloc_896]
    decide

private theorem vecDequeGrow_cond_fine_4_phaseCreditSpec
    {len : Nat} (hlen : len ≤ 4) (cap : BitVec 64) :
    PhaseCreditSpec fineCostModel
      (· = if len = cap.toNat then vecDequeGrowEvents cap else [])
      9213 0 0 896 := by
  by_cases heq : len = cap.toNat
  · simp only [heq, ↓reduceIte]
    have hcap : cap.toNat ≤ 4 := heq ▸ hlen
    have hnew_pos : 0 < max (2 * cap.toNat) 4 * 112 := by omega
    have hnew_le : max (2 * cap.toNat) 4 * 112 ≤ 896 := by omega
    have hev : vecDequeGrowEvents cap =
        growOrReallocEvents (cap.toNat * 112) (max (2 * cap.toNat) 4 * 112) 8 := by
      unfold vecDequeGrowEvents growOrReallocEvents
      dsimp only [chainEpochAlign, chainEpochSize]
      by_cases hc0 : cap = 0#64
      · subst hc0; rfl
      · have hne : cap.toNat * 112 ≠ 0 := by
          have hc_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun ht => hc0 (BitVec.eq_of_toNat_eq ht)
          omega
        simp [hc0, hne]
    rw [hev]
    have hgor := @phaseCreditSpec_growOrRealloc fineCostModel _
      (cap.toNat * 112) (max (2 * cap.toNat) 4 * 112) 8 (by decide) hnew_pos
    have hsm : max (2 * cap.toNat) 4 * 112 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      omega
    have hl0 := allocLargeLive_of_le fineCostModel hsm
    exact hgor.mono (growOrReallocStepCum_vecDeque_le_9213 hcap)
      (by rw [hl0]; exact Nat.sub_le _ _) (by rw [hl0]) hnew_le
  · simp only [heq, ↓reduceIte]
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

private theorem optDealloc_fine_phaseCreditSpec (c : BitVec 64) :
    PhaseCreditSpec fineCostModel
      (· = if c = 0#64 then [] else rustDeallocEvents c.toNat 1) 0 0 0 0 := by
  by_cases hc : c = 0#64
  · simp only [hc, ↓reduceIte]
    exact PhaseCreditSpec.nil fineCostModel
  · simp only [hc, ↓reduceIte]
    exact PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)

/-- Optional `<Chain>::add_epoch` envelope. -/
def OptChainAddEpochEnv (hkdf : HkdfFn) (x : ChainAddEpochGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ChainAddEpochEnv hkdf x evs

/-- Witness-free small-class envelope for `<Chain>::add_epoch` when `links ≤ 4` (`≤ 6` ops, `Δcum ≤ 14,641`, `maxReq = 896`).
-/
def ChainAddEpochTight4Env : List AllocEvent → Prop :=
  FineSmallEvs 6 14641 896

theorem chainAddEpochTight4_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainAddEpochTight4Env 14641 0 0 896 :=
  fineSmallEvs_phaseCreditSpec 6 14641 (by decide)

/-- `PhaseCreditSpec` on `fineCostModel` for `ChainAddEpochEnv` when `x.self.links.length ≤ 4` (`Δcum = 14,641`).
-/
theorem chainAddEpoch_fine_4_phaseCreditSpec (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    (hlinks : x.self.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (ChainAddEpochEnv hkdf x) 14641 0 0 896 := by
  unfold ChainAddEpochEnv
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have ha32 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 32 1) 738 0 0 32 :=
      rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
        (smallAllocCost_le_738_of_le_44 (by decide))
    have ha72 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 1) 1607 0 0 72 :=
      rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_72)
    have hd1 := optDealloc_fine_phaseCreditSpec x.G.nextRoot.cap
    have hd2 := optDealloc_fine_phaseCreditSpec x.esPin.cap
    have hvd := vecDequeGrow_cond_fine_4_phaseCreditSpec hlinks x.G.linksCap
    have hcat :=
      ha32.concat (hd1.concat (ha72.concat (ha32.concat (ha72.concat (ha32.concat (hvd.concat hd2))))))
    refine hcat.congr_mono ?_ (by decide) (by decide) (by decide) (by decide)
    intro evs hevs
    subst hevs
    simp only [chainAddEpochEvents, List.append_assoc, ConcatEnv]
    exact ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl,
      ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩⟩⟩⟩⟩⟩

theorem optChainAddEpoch_fine_4_phaseCreditSpec (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    (hlinks : x.self.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (OptChainAddEpochEnv hkdf x) 14641 0 0 896 :=
  ((PhaseCreditSpec.nil fineCostModel).or (chainAddEpoch_fine_4_phaseCreditSpec hkdf x hlinks)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem chainAddEpoch_nonFreeCount_le (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    {evs : List AllocEvent} (h : ChainAddEpochEnv hkdf x evs) :
    nonFreeCount evs ≤ 6 := by
  unfold ChainAddEpochEnv at h
  split at h
  · subst h; exact Nat.zero_le 6
  · subst h
    have hd : ∀ c : BitVec 64,
        nonFreeCount (if c = 0#64 then [] else rustDeallocEvents c.toNat 1) = 0 := by
      intro c
      split
      · rfl
      · exact nonFreeCount_rustDealloc _ _
    have hvd : nonFreeCount
        (if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap else []) ≤ 1 := by
      split
      · unfold vecDequeGrowEvents
        split
        · rw [nonFreeCount_rustAlloc]
        · exact nonFreeCount_rustRealloc_le _ _ _
      · exact Nat.zero_le 1
    simp only [chainAddEpochEvents, nonFreeCount_append, nonFreeCount_rustAlloc, hd]
    omega

theorem optChainAddEpoch_nonFreeCount_le (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    {evs : List AllocEvent} (h : OptChainAddEpochEnv hkdf x evs) :
    nonFreeCount evs ≤ 6 := by
  rcases h with rfl | hc
  · exact Nat.zero_le 6
  · exact chainAddEpoch_nonFreeCount_le hkdf x hc

private theorem freeOnlyAlign16_append {e₁ e₂ : List AllocEvent}
    (h₁ : FreeOnlyAlign16Evs e₁) (h₂ : FreeOnlyAlign16Evs e₂) :
    FreeOnlyAlign16Evs (e₁ ++ e₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with hm₁ | hm₂
  · exact h₁ ev hm₁
  · exact h₂ ev hm₂

private theorem freeOnlyAlign16_optDealloc1 (c : BitVec 64) :
    FreeOnlyAlign16Evs (if c = 0#64 then [] else rustDeallocEvents c.toNat 1) := by
  split
  · intro _ h; nomatch h
  · intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    subst hev
    exact ⟨1, by decide, c.toNat, rfl⟩

private theorem freeOnlyAlign16_chainEpochPopEvents (gce : ChainEpochGhost) :
    FreeOnlyAlign16Evs (chainEpochPopEvents gce) := by
  unfold chainEpochPopEvents
  exact freeOnlyAlign16_append
    (freeOnlyAlign16_append
      (freeOnlyAlign16_append
        (freeOnlyAlign16_optDealloc1 gce.send.next.cap)
        (freeOnlyAlign16_optDealloc1 gce.send.prev.cap))
      (freeOnlyAlign16_optDealloc1 gce.recv.next.cap))
    (freeOnlyAlign16_optDealloc1 gce.recv.prev.cap)

private theorem freeOnlyAlign16_flatMap_pop :
    ∀ (xs : List ChainEpochGhost), FreeOnlyAlign16Evs (xs.flatMap chainEpochPopEvents)
  | [] => fun _ h => nomatch h
  | x :: xs => by
    simp only [List.flatMap_cons]
    exact freeOnlyAlign16_append (freeOnlyAlign16_chainEpochPopEvents x)
      (freeOnlyAlign16_flatMap_pop xs)

private theorem freeOnlyAlign16_chainSendKeyPopEvents (x : ChainSendKeyGhost) :
    FreeOnlyAlign16Evs (chainSendKeyPopEvents x) := by
  unfold chainSendKeyPopEvents
  split
  · intro _ h; nomatch h
  · split
    · intro _ h; nomatch h
    · exact freeOnlyAlign16_flatMap_pop _

/-- Optional `<Chain>::send_key` envelope. -/
def OptChainSendKeyEnv (hkdf : HkdfFn) (x : ChainSendKeyGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ChainSendKeyEnv hkdf x evs

/-- Witness-free small-class envelope for `<Chain>::send_key` (`≤ 2` ops, `Δcum ≤ 1,476`, `maxReq = 35`).
-/
def ChainSendKeyTightEnv : List AllocEvent → Prop :=
  FineSmallEvs 2 1476 35

theorem chainSendKeyTight_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainSendKeyTightEnv 1476 0 0 35 :=
  fineSmallEvs_phaseCreditSpec 2 1476 (by decide)

theorem chainSendKeyEnv_to_tight (hkdf : HkdfFn) (x : ChainSendKeyGhost)
    {evs : List AllocEvent} (h : ChainSendKeyEnv hkdf x evs) :
    ChainSendKeyTightEnv evs := by
  have hpop : FreeOnlyEvs (chainSendKeyPopEvents x) := by
    intro ev hev
    obtain ⟨al, _, sz, rfl⟩ := freeOnlyAlign16_chainSendKeyPopEvents x ev hev
    exact ⟨al, sz, rfl⟩
  have hpopE : FineSmallEvs 0 0 35 (chainSendKeyPopEvents x) :=
    FineSmallEvs.of_freeOnly 0 0 35 hpop
  unfold ChainSendKeyEnv at h
  split at h
  · subst h
    have hnki : FineSmallEvs 1 738 35 nextKeyInternalEvents := by
      unfold nextKeyInternalEvents
      have ha : FineSmallEvs 1 738 35 (rustAllocEvents (4 + chainNextInfo.length) 1) :=
        FineSmallEvs.rustAlloc (by decide) (by decide)
          (smallAllocCost_le_738_of_le_44 (by decide))
      have hd : FineSmallEvs 0 0 35 (rustDeallocEvents (4 + chainNextInfo.length) 1) :=
        FineSmallEvs.of_freeOnly 0 0 35 fun ev hev => by
          simp only [rustDeallocEvents, List.mem_singleton] at hev
          subst hev
          exact ⟨1, 4 + chainNextInfo.length, rfl⟩
      exact (ha.append hd).mono (by decide) (by decide) (by decide)
    have ha32 : FineSmallEvs 1 738 35 (rustAllocEvents 32 1) :=
      FineSmallEvs.rustAlloc (by decide) (by decide)
        (smallAllocCost_le_738_of_le_44 (by decide))
    unfold chainSendKeyEvents
    exact ((hpopE.append hnki).append ha32).mono (by decide) (by decide) (by decide)
  · subst h; exact FineSmallEvs.nil 2 1476 35
  · subst h; exact hpopE.mono (by decide) (by decide) (by decide)

theorem optChainSendKeyEnv_to_tight (hkdf : HkdfFn) (x : ChainSendKeyGhost)
    {evs : List AllocEvent} (h : OptChainSendKeyEnv hkdf x evs) :
    ChainSendKeyTightEnv evs := by
  rcases h with rfl | hc
  · exact FineSmallEvs.nil 2 1476 35
  · exact chainSendKeyEnv_to_tight hkdf x hc

theorem chainSendKey_fine_phaseCreditSpec (hkdf : HkdfFn) (x : ChainSendKeyGhost) :
    PhaseCreditSpec fineCostModel (ChainSendKeyEnv hkdf x) 1476 0 0 35 :=
  chainSendKeyTight_fine_phaseCreditSpec.of_imp fun _ => chainSendKeyEnv_to_tight hkdf x

theorem optChainSendKey_fine_phaseCreditSpec (hkdf : HkdfFn) (x : ChainSendKeyGhost) :
    PhaseCreditSpec fineCostModel (OptChainSendKeyEnv hkdf x) 1476 0 0 35 :=
  chainSendKeyTight_fine_phaseCreditSpec.of_imp fun _ => optChainSendKeyEnv_to_tight hkdf x

theorem chainSendKey_nonFreeCount_le (hkdf : HkdfFn) (x : ChainSendKeyGhost)
    {evs : List AllocEvent} (h : ChainSendKeyEnv hkdf x evs) :
    nonFreeCount evs ≤ 2 :=
  (chainSendKeyEnv_to_tight hkdf x h).1

theorem optChainSendKey_nonFreeCount_le (hkdf : HkdfFn) (x : ChainSendKeyGhost)
    {evs : List AllocEvent} (h : OptChainSendKeyEnv hkdf x evs) :
    nonFreeCount evs ≤ 2 :=
  (optChainSendKeyEnv_to_tight hkdf x h).1

theorem messageSerializeEnv_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel MessageSerializeEnv 78312 0 0 128 := by
  have h := boundedCount_fine_cap_phaseCreditSpec 8 128 9789 (by decide)
    (fun r hr => smallAllocCost_le_9789_of_le_2560 (Nat.le_trans hr (by decide)))
    (fun _ hn => smallReallocCost_le_9789_of_le_384 (Nat.le_trans hn (by decide)))
  exact h.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)

/-- Tight `<Message>::serialize` envelope (`alloc(≤ 44)` + optional `realloc(old, 80)` + drops; `≤ 2` ops, `Δcum ≤ 9,135`, `maxReq = 80`).
-/
def MessageSerializeTightEnv : List AllocEvent → Prop :=
  FineSmallEvs 2 9135 80

theorem messageSerializeTight_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel MessageSerializeTightEnv 9135 0 0 80 :=
  fineSmallEvs_phaseCreditSpec 2 9135 (by decide)

theorem messageSerializeTight_nonFreeCount_le {evs : List AllocEvent}
    (h : MessageSerializeTightEnv evs) :
    nonFreeCount evs ≤ 2 :=
  h.1

/-- Tight `<Chain>::into_pb` envelope when `links.length ≤ 4` (`≤ 1` op, `Δcum ≤ 8,186`, `maxReq = 448`).
-/
def ChainIntoPbTight4Env : List AllocEvent → Prop :=
  FineSmallEvs 1 8186 448

/-- Tight `<Chain>::into_pb` envelope when `links.length ≤ 707` (`≤ 1` op, `Δcum ≤ 90,234`, `maxReq = 79,236`).
-/
def ChainIntoPbTight79236Env : List AllocEvent → Prop :=
  FineSmallEvs 1 90234 79236

theorem chainIntoPbTight4_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainIntoPbTight4Env 8186 0 0 448 :=
  fineSmallEvs_phaseCreditSpec 1 8186 (by decide)

theorem chainIntoPbTight79236_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainIntoPbTight79236Env 90234 0 0 79236 :=
  fineSmallEvs_phaseCreditSpec 1 90234 (by decide)

theorem chainIntoPbEnv_to_tight4 {x : ChainIntoPbCall} {evs : List AllocEvent}
    (hlinks : x.chain.links.length ≤ 4) (hEnv : ChainIntoPbEnv x evs) :
    ChainIntoPbTight4Env evs := by
  unfold ChainIntoPbEnv at hEnv
  split at hEnv
  · exact FineSmallEvs.of_freeOnly 1 8186 448 hEnv
  · obtain ⟨evs_f, hf, rfl⟩ := hEnv
    have hcost :
        HasFineReallocCredit.smallAllocCost fineCostModel (x.chain.links.length * 112) ≤ 8186 := by
      have hk : x.chain.links.length = 0 ∨ x.chain.links.length = 1 ∨
          x.chain.links.length = 2 ∨ x.chain.links.length = 3 ∨
          x.chain.links.length = 4 := by omega
      rcases hk with h0 | h1 | h2 | h3 | h4
      · rw [h0]
        exact Nat.le_trans (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide))) (by decide)
      · rw [h1]; change fineSmallAllocCost 112 ≤ 8186; rw [fineSmallAlloc_112]; decide
      · rw [h2]; change fineSmallAllocCost 224 ≤ 8186; rw [fineSmallAlloc_224]
      · rw [h3]; change fineSmallAllocCost 336 ≤ 8186; rw [fineSmallAlloc_336]; decide
      · rw [h4]; change fineSmallAllocCost 448 ≤ 8186; rw [fineSmallAlloc_448]; decide
    have ha : FineSmallEvs 1 8186 448 (rustAllocEvents (x.chain.links.length * 112) 8) :=
      FineSmallEvs.rustAlloc (by decide) (by omega) hcost
    exact (ha.append (FineSmallEvs.of_freeOnly 0 0 448 hf)).mono (by decide) (by decide) (by decide)

theorem chainIntoPbEnv_to_tight79236 {x : ChainIntoPbCall} {evs : List AllocEvent}
    (hlinks : x.chain.links.length ≤ 707) (hEnv : ChainIntoPbEnv x evs) :
    ChainIntoPbTight79236Env evs := by
  unfold ChainIntoPbEnv at hEnv
  split at hEnv
  · exact FineSmallEvs.of_freeOnly 1 90234 79236 hEnv
  · obtain ⟨evs_f, hf, rfl⟩ := hEnv
    have hreq : x.chain.links.length * 112 ≤ 79236 := by omega
    have ha : FineSmallEvs 1 90234 79236 (rustAllocEvents (x.chain.links.length * 112) 8) :=
      FineSmallEvs.rustAlloc (by decide) hreq (smallAllocCost_le_90234_of_le_79236 hreq)
    exact (ha.append (FineSmallEvs.of_freeOnly 0 0 79236 hf)).mono
      (by decide) (by decide) (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
