/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Encoder

/-!
# Tight Leaf Inclusions for `spqr::send::<Coins>`

**Checked by Lean.**

Proves `FineSmallEvs` inclusions for `<States>::send` (`StatesSendTightEnv → StatesSendRodataTightEnv`),
`<Message>::serialize` (`MessageSerializeEnv → MessageSerializeTightEnv`), and
`<Chain>::add_epoch` (`ChainAddEpochEnv → ChainAddEpochTight4Env`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendStage1AuxR2

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk HkdfFn MlKem Point Poly PolyEncoder States encaps1 spqrAuthApi
   spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs (ChainAddEpochGhost)
open CryptoVerification.SpqrV1.Drop (chunkedKeysSampledToCt1Received)
open CryptoVerification.SpqrV1.Poly (PolyNextChunkGhost)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (encodeBytesResult encodeBytes_eq_ok)
open CryptoVerification.SpqrV1.Top.MessageSerialize (MessageSerializeGhost)
open CryptoVerification.SpqrV1Sync.Erasure (msgPoints needed)
open CryptoVerification.SpqrV1Sync.Erasure.EncodeBytes (encodeBytes_spec_aux)
open LibsignalBinary.Heap
  (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (StatesSendEnvOfEnv StatesSendTightEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1Env HeaderReceived1aEnv headerReceived1aEvents headerReceived1bPreEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget
  (HeaderReceived2aCt1Env HeaderReceivedArmEnv headerReceived2bEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
  (headerReceived2aPreEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (keysUnsampledAllocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
  (KeysUnsampledMacReserveEnv keysUnsampledMacReserveEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget
  (KeysUnsampledArmEnv keysUnsampledHdr keysUnsampledMac)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs smallAllocCost_le_1607_of_le_72)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
  (ChainAddEpochTight4Env EncRodataValid MessageSerializeTightEnv StatesRodataValid
   StatesSendRodataTightEnv isRodataPtLen)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget (authMacHdrEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
  (AuthUpdateLenEnv AuthUpdatePreAlloc1Env)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv computeAtAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (LagrangeSumStepEnv NextChunkPolysLoopEnv NextChunkPolysTailByLenEnv
   PointsToPolysIterEnv PointsToPolysLoopEnv PolyNextChunkEnv RepeatSeqEnv
   isPrecomputedBasisLen nextChunkBlockAEvents nextChunkEpilogueEvents nextChunkFirstSlowIdx
   nextChunkPrologueEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv PolyEncoderNextChunkEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv messageSerializeEvents)

/-! ## `FineSmallEvs` Decidability and Sequential Combinators -/

instance ckx2_instDecidableFineSmallEvs (o c r : Nat) (evs : List AllocEvent) :
    Decidable (FineSmallEvs o c r evs) := by
  unfold FineSmallEvs
  infer_instance

private instance ckx2_instDecidableStatesSendRodataTightEnv (evs : List AllocEvent) :
    Decidable (StatesSendRodataTightEnv evs) :=
  ckx2_instDecidableFineSmallEvs 1233 2124238 2400 evs

private instance ckx2_instDecidableMessageSerializeTightEnv (evs : List AllocEvent) :
    Decidable (MessageSerializeTightEnv evs) :=
  ckx2_instDecidableFineSmallEvs 2 9135 80 evs

private instance ckx2_instDecidableChainAddEpochTight4Env (evs : List AllocEvent) :
    Decidable (ChainAddEpochTight4Env evs) :=
  ckx2_instDecidableFineSmallEvs 6 14641 896 evs

theorem ckx2_fineSmallEvs_seqEnv {E₁ E₂ : List AllocEvent → Prop}
    {o₁ o₂ c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (hE₁ : ∀ e, E₁ e → FineSmallEvs o₁ c₁ r₁ e)
    (hE₂ : ∀ e, E₂ e → FineSmallEvs o₂ c₂ r₂ e)
    (h : SeqEnv E₁ E₂ evs) :
    FineSmallEvs (o₁ + o₂) (c₁ + c₂) (max r₁ r₂) evs := by
  rcases h with h1 | ⟨x1, x2, rfl, h1, h2⟩
  · exact (hE₁ evs h1).mono
      (Nat.le_add_right o₁ o₂) (Nat.le_add_right c₁ c₂) (Nat.le_max_left r₁ r₂)
  · exact (hE₁ x1 h1).append (hE₂ x2 h2)

theorem ckx2_fineSmallEvs_repeatSeqEnv {E : List AllocEvent → Prop} {o c r : Nat}
    (hE : ∀ e, E e → FineSmallEvs o c r e) :
    ∀ (n : Nat) {evs : List AllocEvent}, RepeatSeqEnv n E evs →
      FineSmallEvs (n * o) (n * c) r evs
  | 0, _, h => by
    subst h
    simp only [Nat.zero_mul]
    exact FineSmallEvs.nil 0 0 r
  | n + 1, _, h => by
    have hstep := ckx2_fineSmallEvs_seqEnv hE (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv hE n hr) h
    exact hstep.mono (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega)
      (by rw [Nat.max_self])

/-! ## `<PolyEncoder>::next_chunk` (`PolyNextChunkEnv`) Inclusion -/

private def ckx2_ptTailOps (k : Nat) : Nat := if k = 1 then 2 else 1
private def ckx2_ptTailCum (k : Nat) : Nat := if k = 1 then 8513 else 1607
private def ckx2_ptIterOps (k : Nat) : Nat := if k = 1 then 5 else 75
private def ckx2_ptIterCum (k : Nat) : Nat := if k = 1 then 1490 else 130606

private def ckx2_natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + ckx2_natSum xs

private theorem ckx2_natSum_drop_le :
    ∀ (i : Nat) (xs : List Nat), ckx2_natSum (xs.drop i) ≤ ckx2_natSum xs
  | 0, _ => Nat.le_refl _
  | _ + 1, [] => Nat.le_refl 0
  | i + 1, x :: xs => Nat.le_trans (ckx2_natSum_drop_le i xs) (Nat.le_add_left _ x)

private theorem ckx2_computeAtCallEnv_sub_tail {k : Nat} (hk : k ≤ 36) {evs : List AllocEvent}
    (h : ComputeAtCallEnv k evs) :
    FineSmallEvs (ckx2_ptTailOps k) (ckx2_ptTailCum k) 72 evs := by
  have halloc : FineSmallEvs (ckx2_ptTailOps k) (ckx2_ptTailCum k) 72 (computeAtAllocEvents k) := by
    by_cases h0 : k = 0
    · subst h0; decide
    · by_cases h1 : k = 1
      · subst h1; decide
      · unfold computeAtAllocEvents ckx2_ptTailOps ckx2_ptTailCum
        simp only [h0, h1, ↓reduceIte]
        exact FineSmallEvs.rustAlloc (by decide) (by omega)
          (smallAllocCost_le_1607_of_le_72 (by omega))
  exact (ckx2_fineSmallEvs_seqEnv
    (fun _ he => by rw [he]; exact halloc)
    (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) h).mono
    (by omega) (by omega) (by decide)

private theorem ckx2_computeAtCallEnv_sub_2_8513 {k : Nat} (hk : k ≤ 36) {evs : List AllocEvent}
    (h : ComputeAtCallEnv k evs) :
    FineSmallEvs 2 8513 72 evs := by
  have ht := ckx2_computeAtCallEnv_sub_tail hk h
  unfold ckx2_ptTailOps ckx2_ptTailCum at ht
  split at ht <;> exact ht.mono (by decide) (by decide) (Nat.le_refl 72)

private theorem ckx2_nextChunkPolysLoopEnv_sub :
    ∀ (polys : List Poly),
      (∀ p ∈ polys, p.coefficients.length ≤ 36) →
      ∀ {evs : List AllocEvent}, NextChunkPolysLoopEnv polys evs →
        FineSmallEvs (2 * polys.length) (8513 * polys.length) 72 evs
  | [], _, _, h => by
    subst h
    exact FineSmallEvs.nil 0 0 72
  | p :: ps, hp, _, h => by
    have hp0 := hp p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.coefficients.length ≤ 36 :=
      fun q hq => hp q (List.mem_cons_of_mem p hq)
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ hc => ckx2_computeAtCallEnv_sub_2_8513 hp0 hc)
      (fun _ hl => ckx2_nextChunkPolysLoopEnv_sub ps hps hl) h).mono
      (by simp [List.length_cons]; omega)
      (by simp [List.length_cons]; omega)
      (by decide)

private theorem ckx2_lagrangeSumStepEnv_sub (k cap maxReq : Nat)
    (ha : FineSmallEvs 1 cap maxReq (rustAllocEvents (2 * k) 2))
    {evs : List AllocEvent} (h : LagrangeSumStepEnv k evs) :
    FineSmallEvs 1 cap maxReq evs :=
  (ckx2_fineSmallEvs_seqEnv
    (fun _ he => by rw [he]; exact ha)
    (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) h).mono
    (by omega) (by omega) (by simp)

private theorem ckx2_pointsToPolysIterEnv_rodata_sub {k : Nat} (hk : isRodataPtLen k = true)
    {evs : List AllocEvent} (h : PointsToPolysIterEnv k evs) :
    FineSmallEvs (ckx2_ptIterOps k) (ckx2_ptIterCum k) 864 evs := by
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 30 ∨ k = 34 ∨ k = 36 := by
    revert hk; unfold isRodataPtLen
    simp only [Bool.or_eq_true, beq_iff_eq]
    tauto
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold PointsToPolysIterEnv at h
    simp only [↓reduceIte] at h
    exact FineSmallEvs.of_freeOnly _ _ 864 h
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 1 = true := by decide
    simp only [Nat.one_ne_zero, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 4 1302 24
        (rustAllocEvents (4 * 1) 2 ++ rustAllocEvents (24 * 1) 8 ++
          (List.replicate (1 + 1) (rustAllocEvents (2 * 1) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 1 188 2 (by decide) hl) 1 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 3 = true := by decide
    simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 6 2547 72
        (rustAllocEvents (4 * 3) 2 ++ rustAllocEvents (24 * 3) 8 ++
          (List.replicate (3 + 1) (rustAllocEvents (2 * 3) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 3 188 6 (by decide) hl) 3 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 5 = true := by decide
    simp only [show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 8 4981 120
        (rustAllocEvents (4 * 5) 2 ++ rustAllocEvents (24 * 5) 8 ++
          (List.replicate (5 + 1) (rustAllocEvents (2 * 5) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 5 188 10 (by decide) hl) 5 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 30 = true := by decide
    simp only [show (30 : Nat) ≠ 0 by decide, show (30 : Nat) ≠ 1 by decide, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 33 63212 720
        (rustAllocEvents (4 * 30) 2 ++ rustAllocEvents (24 * 30) 8 ++
          (List.replicate (30 + 1) (rustAllocEvents (2 * 30) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 30 1607 60 (by decide) hl) 30 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 34 = true := by decide
    simp only [show (34 : Nat) ≠ 0 by decide, show (34 : Nat) ≠ 1 by decide, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 37 72356 816
        (rustAllocEvents (4 * 34) 2 ++ rustAllocEvents (24 * 34) 8 ++
          (List.replicate (34 + 1) (rustAllocEvents (2 * 34) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 34 1607 68 (by decide) hl) 34 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)
  · unfold PointsToPolysIterEnv at h
    unfold ckx2_ptIterOps ckx2_ptIterCum
    have hpb : isPrecomputedBasisLen 36 = true := by decide
    simp only [show (36 : Nat) ≠ 0 by decide, show (36 : Nat) ≠ 1 by decide, ↓reduceIte, hpb] at h ⊢
    have hpre : FineSmallEvs 39 72754 864
        (rustAllocEvents (4 * 36) 2 ++ rustAllocEvents (24 * 36) 8 ++
          (List.replicate (36 + 1) (rustAllocEvents (2 * 36) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 36 1607 72 (by decide) hl) 36 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) h).mono
      (by decide) (by decide) (by decide)

private theorem ckx2_pointsToPolysLoopEnv_rodata_sub :
    ∀ (pts : List Point),
      (∀ pt ∈ pts, isRodataPtLen pt.value.length = true) →
      ∀ {evs : List AllocEvent}, PointsToPolysLoopEnv pts evs →
        FineSmallEvs
          (ckx2_natSum (pts.map fun pt => ckx2_ptIterOps pt.value.length))
          (ckx2_natSum (pts.map fun pt => ckx2_ptIterCum pt.value.length))
          864 evs
  | [], _, _, h => by
    subst h
    exact FineSmallEvs.nil 0 0 864
  | pt :: pts, hpts, _, h => by
    have h0 := hpts pt List.mem_cons_self
    have htl : ∀ q ∈ pts, isRodataPtLen q.value.length = true :=
      fun q hq => hpts q (List.mem_cons_of_mem pt hq)
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ hi => ckx2_pointsToPolysIterEnv_rodata_sub h0 hi)
      (fun _ hl => ckx2_pointsToPolysLoopEnv_rodata_sub pts htl hl) h).mono
      (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem ckx2_nextChunkPolysTailByLenEnv_sub :
    ∀ (ks : List Nat),
      (∀ k ∈ ks, k ≤ 36) →
      ∀ {evs : List AllocEvent}, NextChunkPolysTailByLenEnv ks evs →
        FineSmallEvs (ckx2_natSum (ks.map ckx2_ptTailOps)) (ckx2_natSum (ks.map ckx2_ptTailCum)) 72 evs
  | [], _, _, h => by
    subst h
    exact FineSmallEvs.nil 0 0 72
  | k :: ks, hks, _, h => by
    have hk0 := hks k List.mem_cons_self
    have hktl : ∀ m ∈ ks, m ≤ 36 := fun m hm => hks m (List.mem_cons_of_mem k hm)
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ hc => ckx2_computeAtCallEnv_sub_tail hk0 hc)
      (fun _ hl => ckx2_nextChunkPolysTailByLenEnv_sub ks hktl hl) h).mono
      (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem ckx2_natSum_ptIter_add_ptTail_le :
    ∀ (pts : List Point),
      ckx2_natSum (pts.map fun pt => ckx2_ptIterOps pt.value.length) +
        ckx2_natSum (pts.map fun pt => ckx2_ptTailOps pt.value.length) ≤ 76 * pts.length ∧
      ckx2_natSum (pts.map fun pt => ckx2_ptIterCum pt.value.length) +
        ckx2_natSum (pts.map fun pt => ckx2_ptTailCum pt.value.length) ≤ 132213 * pts.length
  | [] => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | pt :: pts => by
    obtain ⟨ho, hc⟩ := ckx2_natSum_ptIter_add_ptTail_le pts
    have hpo : ckx2_ptIterOps pt.value.length + ckx2_ptTailOps pt.value.length ≤ 76 := by
      unfold ckx2_ptIterOps ckx2_ptTailOps
      split <;> decide
    have hpc : ckx2_ptIterCum pt.value.length + ckx2_ptTailCum pt.value.length ≤ 132213 := by
      unfold ckx2_ptIterCum ckx2_ptTailCum
      split <;> decide
    simp only [List.map_cons, ckx2_natSum, List.length_cons]
    exact ⟨by omega, by omega⟩

private theorem ckx2_isRodataPtLen_le_36 {k : Nat} (hk : isRodataPtLen k = true) : k ≤ 36 := by
  revert hk; unfold isRodataPtLen
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

theorem ckx2_polyNextChunkEnv_sub_rodataTight {x : PolyNextChunkGhost} {evs : List AllocEvent}
    (hb : EncRodataValid x.enc) (h : PolyNextChunkEnv x evs) :
    StatesSendRodataTightEnv evs := by
  unfold PolyNextChunkEnv at h
  unfold EncRodataValid at hb
  cases hs : x.enc.s with
  | polys polys =>
    rw [hs] at hb h
    obtain ⟨hlen, hpolys⟩ := hb
    have hpro : FineSmallEvs 1 738 32 nextChunkPrologueEvents := by decide
    have hepi : FineSmallEvs 0 0 0 nextChunkEpilogueEvents := by decide
    have hmain := ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpro)
      (fun _ h1 => ckx2_fineSmallEvs_seqEnv
        (fun _ hl => ckx2_nextChunkPolysLoopEnv_sub polys hpolys hl)
        (fun _ he => by rw [he]; exact hepi) h1) h
    exact hmain.mono (by omega) (by omega) (by decide)
  | points pts =>
    rw [hs] at hb h
    obtain ⟨hlen, hpts⟩ := hb
    dsimp only at h
    split at h
    · have hpro : FineSmallEvs 1 738 32 nextChunkPrologueEvents := by decide
      have hblkA : FineSmallEvs 16 3008 2 nextChunkBlockAEvents := by decide
      have hepi : FineSmallEvs 0 0 0 nextChunkEpilogueEvents := by decide
      let i0 := nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0
      have hks_le : ∀ k ∈ (pts.drop i0).map (·.value.length), k ≤ 36 := by
        intro k hk
        rcases List.mem_map.mp hk with ⟨pt, hpt_drop, rfl⟩
        exact ckx2_isRodataPtLen_le_36 (hpts pt (List.mem_of_mem_drop hpt_drop))
      have htail_sub : ∀ e, NextChunkPolysTailByLenEnv ((pts.drop i0).map (·.value.length)) e →
          FineSmallEvs
            (ckx2_natSum (pts.map fun pt => ckx2_ptTailOps pt.value.length))
            (ckx2_natSum (pts.map fun pt => ckx2_ptTailCum pt.value.length)) 72 e := by
        intro e he
        have ht := ckx2_nextChunkPolysTailByLenEnv_sub _ hks_le he
        simp only [List.map_map, Function.comp_def, List.map_drop] at ht
        exact ht.mono (ckx2_natSum_drop_le i0 _) (ckx2_natSum_drop_le i0 _) (Nat.le_refl 72)
      have hcomb := ckx2_fineSmallEvs_seqEnv
        (fun _ he => by rw [he]; exact hpro)
        (fun _ h1 => ckx2_fineSmallEvs_seqEnv
          (fun _ he => by rw [he]; exact hblkA)
          (fun _ h2 => ckx2_fineSmallEvs_seqEnv
            (fun _ hp => ckx2_pointsToPolysLoopEnv_rodata_sub pts hpts hp)
            (fun _ h3 => ckx2_fineSmallEvs_seqEnv
              (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf)
              (fun _ h4 => ckx2_fineSmallEvs_seqEnv htail_sub
                (fun _ he => by rw [he]; exact hepi) h4) h3) h2) h1) h
      obtain ⟨ho, hc⟩ := ckx2_natSum_ptIter_add_ptTail_le pts
      exact hcomb.mono (by omega) (by omega) (by decide)
    · subst h
      decide

/-! ## Fixed-Length `encodeBytesResult` (`96` B and `960` B) Specializations -/

private theorem ckx2_pointsToPolysLoopEnv_fixed_sub {slotLen iterO iterC iterR : Nat}
    (hIter : ∀ e, PointsToPolysIterEnv slotLen e → FineSmallEvs iterO iterC iterR e) :
    ∀ (pts : List Point),
      (∀ pt ∈ pts, pt.value.length = slotLen) →
      ∀ {evs : List AllocEvent}, PointsToPolysLoopEnv pts evs →
        FineSmallEvs (pts.length * iterO) (pts.length * iterC) iterR evs
  | [], _, _, h => by
    subst h
    simp only [List.length_nil, Nat.zero_mul]
    exact FineSmallEvs.nil 0 0 iterR
  | pt :: pts, hpts, _, h => by
    have h0 := hpts pt List.mem_cons_self
    have htl : ∀ q ∈ pts, q.value.length = slotLen :=
      fun q hq => hpts q (List.mem_cons_of_mem pt hq)
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ hi => hIter _ (h0 ▸ hi))
      (fun _ hl => ckx2_pointsToPolysLoopEnv_fixed_sub hIter pts htl hl) h).mono
      (by simp [List.length_cons, Nat.succ_mul]; omega)
      (by simp [List.length_cons, Nat.succ_mul]; omega)
      (by rw [Nat.max_self])

private theorem ckx2_nextChunkPolysTailByLenEnv_fixed_sub {slotLen tailO tailC tailR : Nat}
    (hTail : ∀ e, ComputeAtCallEnv slotLen e → FineSmallEvs tailO tailC tailR e) :
    ∀ (ks : List Nat),
      (∀ k ∈ ks, k = slotLen) →
      ∀ {evs : List AllocEvent}, NextChunkPolysTailByLenEnv ks evs →
        FineSmallEvs (ks.length * tailO) (ks.length * tailC) tailR evs
  | [], _, _, h => by
    subst h
    simp only [List.length_nil, Nat.zero_mul]
    exact FineSmallEvs.nil 0 0 tailR
  | k :: ks, hks, _, h => by
    have hk0 := hks k List.mem_cons_self
    have hktl : ∀ m ∈ ks, m = slotLen := fun m hm => hks m (List.mem_cons_of_mem k hm)
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ hc => hTail _ (hk0 ▸ hc))
      (fun _ hl => ckx2_nextChunkPolysTailByLenEnv_fixed_sub hTail ks hktl hl) h).mono
      (by simp [List.length_cons, Nat.succ_mul]; omega)
      (by simp [List.length_cons, Nat.succ_mul]; omega)
      (by rw [Nat.max_self])

private theorem ckx2_polyNextChunkEnv_points_fixed_sub
    {x : PolyNextChunkGhost} {pts : List Point} {slotLen iterO iterC tailO tailC rCap : Nat}
    (hs : x.enc.s = .points pts)
    (hlen : pts.length = 16)
    (hslot : ∀ pt ∈ pts, pt.value.length = slotLen)
    (hIter : ∀ e, PointsToPolysIterEnv slotLen e → FineSmallEvs iterO iterC rCap e)
    (hTail : ∀ e, ComputeAtCallEnv slotLen e → FineSmallEvs tailO tailC rCap e)
    (hr32 : 32 ≤ rCap)
    {evs : List AllocEvent} (h : PolyNextChunkEnv x evs) :
    FineSmallEvs (17 + 16 * (iterO + tailO)) (3746 + 16 * (iterC + tailC)) rCap evs := by
  unfold PolyNextChunkEnv at h
  rw [hs] at h
  dsimp only at h
  split at h
  · have hpro0 : FineSmallEvs 1 738 32 nextChunkPrologueEvents := by decide
    have hpro : FineSmallEvs 1 738 rCap nextChunkPrologueEvents :=
      hpro0.mono (Nat.le_refl 1) (Nat.le_refl 738) hr32
    have hblkA0 : FineSmallEvs 16 3008 2 nextChunkBlockAEvents := by decide
    have hblkA : FineSmallEvs 16 3008 rCap nextChunkBlockAEvents :=
      hblkA0.mono (Nat.le_refl 16) (Nat.le_refl 3008) (Nat.le_trans (by decide) hr32)
    have hepi0 : FineSmallEvs 0 0 0 nextChunkEpilogueEvents := by decide
    have hepi : FineSmallEvs 0 0 rCap nextChunkEpilogueEvents :=
      hepi0.mono (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le rCap)
    let i0 := nextChunkFirstSlowIdx (x.enc.idx.setWidth 16).toNat pts 16 0
    have hks : ∀ k ∈ (pts.drop i0).map (·.value.length), k = slotLen := by
      intro k hk
      rcases List.mem_map.mp hk with ⟨pt, hpt, rfl⟩
      exact hslot pt (List.mem_of_mem_drop hpt)
    have hdrop_le : ((pts.drop i0).map (·.value.length)).length ≤ 16 := by
      rw [List.length_map, List.length_drop]
      omega
    have hcomb := ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpro)
      (fun _ h1 => ckx2_fineSmallEvs_seqEnv
        (fun _ he => by rw [he]; exact hblkA)
        (fun _ h2 => ckx2_fineSmallEvs_seqEnv
          (fun _ hp => ckx2_pointsToPolysLoopEnv_fixed_sub hIter pts hslot hp)
          (fun _ h3 => ckx2_fineSmallEvs_seqEnv
            (fun _ hf => FineSmallEvs.of_freeOnly 0 0 rCap hf)
            (fun _ h4 => ckx2_fineSmallEvs_seqEnv
              (fun _ ht => (ckx2_nextChunkPolysTailByLenEnv_fixed_sub hTail _ hks ht).mono
                (Nat.mul_le_mul_right tailO hdrop_le)
                (Nat.mul_le_mul_right tailC hdrop_le)
                (Nat.le_refl rCap))
              (fun _ he => by rw [he]; exact hepi) h4) h3) h2) h1) h
    rw [hlen] at hcomb
    exact hcomb.mono (by omega) (by omega) (by simp)
  · subst h
    have hc : FineSmallEvs 1 738 32 (nextChunkPrologueEvents ++ nextChunkEpilogueEvents) := by
      decide
    exact hc.mono (by omega) (by omega) hr32

private theorem ckx2_encodeBytesResult_ok_points {msg : Bytes} {enc : PolyEncoder}
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 2 ^ 20)
    (henc : encodeBytesResult msg = .ok enc) :
    enc.s = .points (msgPoints msg) ∧
    (msgPoints msg).length = 16 ∧
    ∀ pt ∈ msgPoints msg, ∃ j < 16, pt.value.length = needed msg.length j := by
  have hspec := encodeBytes_spec_aux msg heven hle
  rw [encodeBytes_eq_ok, henc] at hspec
  injection hspec with h1
  injection h1 with h2
  subst h2
  refine ⟨rfl, by simp [msgPoints], fun pt hpt => ?_⟩
  unfold msgPoints at hpt
  rcases List.mem_map.mp hpt with ⟨j, hj, rfl⟩
  rw [List.mem_range] at hj
  exact ⟨j, hj, by simp⟩

/-! ## `StatesSendTightEnv` to `StatesSendRodataTightEnv` Inclusion -/

private theorem ckx2_keysUnsampledArmEnv_sub_rodataTight (F : ShaCompress) (K : MlKem)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (out_hdr : PolyEncoder) (chunk : Chunk) (tape : Bytes) {evs : List AllocEvent}
    (h : KeysUnsampledArmEnv F K st out_hdr chunk tape evs) :
    StatesSendRodataTightEnv evs := by
  unfold KeysUnsampledArmEnv at h
  have hhdr_len : (keysUnsampledHdr K tape).length = 64 :=
    List.Vector.toList_length _
  have hmac_len : (keysUnsampledMac F K st.uc.auth st.uc.epoch tape).length = 32 :=
    Authenticator.length_macHdrUnchecked F st.uc.auth st.uc.epoch (keysUnsampledHdr K tape)
  let msg := keysUnsampledHdr K tape ++ keysUnsampledMac F K st.uc.auth st.uc.epoch tape
  have hmsg_len : msg.length = 96 := by
    simp only [msg, List.length_append, hhdr_len, hmac_len]
  cases henc : encodeBytesResult msg with
  | error _ =>
    rw [henc] at h
    subst h
    exact FineSmallEvs.nil 1233 2124238 2400
  | ok sending_hdr =>
    rw [henc] at h
    obtain ⟨hs, hpts_len, hpts_mem⟩ :=
      ckx2_encodeBytesResult_ok_points (by rw [hmsg_len]) (by rw [hmsg_len]; decide) henc
    have hslot3 : ∀ pt ∈ msgPoints msg, pt.value.length = 3 := by
      intro pt hpt
      obtain ⟨j, _, hneed⟩ := hpts_mem pt hpt
      rw [hneed, hmsg_len]
      simp [needed]
    have halloc : FineSmallEvs 3 14902 2400 keysUnsampledAllocEvents := by decide
    have hmac_res : ∀ e, KeysUnsampledMacReserveEnv st.uc.auth (keysUnsampledHdr K tape) e →
        FineSmallEvs 20 50000 2400 e := by
      intro e he
      unfold KeysUnsampledMacReserveEnv keysUnsampledMacReserveEvents authMacHdrEvents at he
      rw [hhdr_len] at he
      subst he
      split <;> decide
    have henc96 : FineSmallEvs 16 31952 96 (encodeBytesAllocEvents 96) := by decide
    have hiter3 : ∀ e, PointsToPolysIterEnv 3 e → FineSmallEvs 9 3111 72 e := by
      intro e hi
      unfold PointsToPolysIterEnv at hi
      have hpb : isPrecomputedBasisLen 3 = true := by decide
      simp only [show (3 : Nat) ≠ 0 by decide, ↓reduceIte, hpb] at hi
      have hpre3 : FineSmallEvs 6 2547 72
          (rustAllocEvents (4 * 3) 2 ++ rustAllocEvents (24 * 3) 8 ++
            (List.replicate (3 + 1) (rustAllocEvents (2 * 3) 2)).flatten) := by decide
      exact (ckx2_fineSmallEvs_seqEnv
        (fun _ he => by rw [he]; exact hpre3)
        (fun _ hs => ckx2_fineSmallEvs_seqEnv
          (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
            (fun _ hl => ckx2_lagrangeSumStepEnv_sub 3 188 6 (by decide) hl) 3 hr)
          (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) hi).mono
        (by decide) (by decide) (by decide)
    have htail3 : ∀ e, ComputeAtCallEnv 3 e → FineSmallEvs 1 188 72 e := by
      intro e hc
      have hca3 : FineSmallEvs 1 188 6 (computeAtAllocEvents 3) := by decide
      exact (ckx2_fineSmallEvs_seqEnv
        (fun _ he => by rw [he]; exact hca3)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hc).mono
        (by decide) (by decide) (by decide)
    have hcomb := ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact halloc)
      (fun _ h1 => ckx2_fineSmallEvs_seqEnv
        hmac_res
        (fun _ h2 => ckx2_fineSmallEvs_seqEnv
          (fun _ he => by rw [he]; exact henc96)
          (fun _ h3 => ckx2_fineSmallEvs_seqEnv
            (fun _ hnc => ckx2_polyNextChunkEnv_points_fixed_sub hs hpts_len hslot3
              hiter3 htail3 (by decide) hnc)
            (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) h3) h2) h1) h
    exact hcomb.mono (by decide) (by decide) (by decide)

private theorem ckx2_authUpdateLenEnv_32_sub {rkLen : Nat} (hrk : rkLen ≤ 32) {evs : List AllocEvent}
    (h : AuthUpdateLenEnv rkLen 32 evs) :
    FineSmallEvs 5 5816 64 evs := by
  have hpre : ∀ e, AuthUpdatePreAlloc1Env rkLen 32 e → FineSmallEvs 4 5078 64 e := by
    intro e he
    rw [he]
    have hsc : FineSmallEvs 1 1607 64 (sliceConcat2Events (rkLen + 32)) := by
      unfold sliceConcat2Events
      have hne : rkLen + 32 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      exact FineSmallEvs.rustAlloc (by decide) (by omega)
        (smallAllocCost_le_1607_of_le_72 (by omega))
    have hrest : FineSmallEvs 3 3471 64
        (rustAllocEvents 53 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 32 1) := by decide
    have hassoc : sliceConcat2Events (rkLen + 32) ++
        rustAllocEvents 53 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 32 1 =
        sliceConcat2Events (rkLen + 32) ++
        (rustAllocEvents 53 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 32 1) := by
      simp only [List.append_assoc]
    rw [hassoc]
    exact (hsc.append hrest).mono (by decide) (by decide) (by decide)
  have ha2_32 : FineSmallEvs 1 738 32 (rustAllocEvents 32 1) := by decide
  exact (ckx2_fineSmallEvs_seqEnv
    (fun _ h1 => ckx2_fineSmallEvs_seqEnv
      (fun _ h2 => ckx2_fineSmallEvs_seqEnv hpre (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) h2)
      (fun _ ha2 => by rw [ha2]; exact ha2_32) h1)
    (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) h).mono
    (by decide) (by decide) (by decide)

private theorem ckx2_send_ct1_chunk_ct1_len (K : MlKem) {F : ShaCompress}
    {self : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi
      (spqrAuthApi F)}
    {tape : Bytes}
    {outSt : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled spqrPolyApi
      (spqrAuthApi F)}
    {chunk : Chunk} {es : CryptoVerification.LibsignalSpqrV1.EpochSecret} {tape' : Bytes}
    (h : self.send_ct1_chunk K tape = .ok (outSt, chunk, es, tape')) :
    outSt.uc.ct1.length = 960 := by
  unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.send_ct1_chunk at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i v huc
    rcases v with ⟨uc, ct1, es0, t1⟩
    split at h
    · contradiction
    · split at h
      · contradiction
      · injection h with hok
        injection hok with hst _
        subst hst
        unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.send_ct1 at huc
        simp only [Bind.bind, Except.bind] at huc
        split at huc
        · contradiction
        · rename_i w henc1
          rcases w with ⟨⟨ct1', es1, sec0⟩, t2⟩
          split at huc
          · contradiction
          · split at huc
            · contradiction
            · injection huc with huc_ok
              injection huc_ok with huc_eq _
              subst huc_eq
              unfold encaps1 at henc1
              split at henc1
              · contradiction
              · split at henc1
                · contradiction
                · injection henc1 with he1
                  injection he1 with he2 _
                  injection he2 with hct1 _
                  rw [← hct1]
                  exact List.Vector.toList_length _

private theorem ckx2_headerReceivedArmEnv_sub_rodataTight {rkLen : Nat} (hrk : rkLen ≤ 32)
    {ct1Bytes : Bytes} (hct1 : ct1Bytes.length = 960) (chunk : Chunk) {evs : List AllocEvent}
    (h : HeaderReceivedArmEnv rkLen ct1Bytes chunk evs) :
    StatesSendRodataTightEnv evs := by
  have h1a : FineSmallEvs 2 10527 2080 headerReceived1aEvents := by decide
  have h1bpre : FineSmallEvs 3 11265 960 headerReceived1bPreEvents := by decide
  have h1 : ∀ e, HeaderReceived1Env rkLen e → FineSmallEvs 10 27608 2080 e := by
    intro e he
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ ha => by rw [ha]; exact h1a)
      (fun _ hb => ckx2_fineSmallEvs_seqEnv
        (fun _ hp => by rw [hp]; exact h1bpre)
        (fun _ hu => ckx2_authUpdateLenEnv_32_sub hrk hu) hb) he).mono
      (by decide) (by decide) (by decide)
  have h2apre : FineSmallEvs 17 65885 960 headerReceived2aPreEvents := by decide
  have h2b : FineSmallEvs 0 0 0 headerReceived2bEvents := by decide
  have hiter30 : ∀ e, PointsToPolysIterEnv 30 e → FineSmallEvs 63 111422 720 e := by
    intro e hi
    unfold PointsToPolysIterEnv at hi
    have hpb : isPrecomputedBasisLen 30 = true := by decide
    simp only [show (30 : Nat) ≠ 0 by decide, ↓reduceIte, hpb] at hi
    have hpre30 : FineSmallEvs 33 63212 720
        (rustAllocEvents (4 * 30) 2 ++ rustAllocEvents (24 * 30) 8 ++
          (List.replicate (30 + 1) (rustAllocEvents (2 * 30) 2)).flatten) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hpre30)
      (fun _ hs => ckx2_fineSmallEvs_seqEnv
        (fun _ hr => ckx2_fineSmallEvs_repeatSeqEnv
          (fun _ hl => ckx2_lagrangeSumStepEnv_sub 30 1607 60 (by decide) hl) 30 hr)
        (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hs) hi).mono
      (by decide) (by decide) (by decide)
  have htail30 : ∀ e, ComputeAtCallEnv 30 e → FineSmallEvs 1 1607 720 e := by
    intro e hc
    have hca30 : FineSmallEvs 1 1607 60 (computeAtAllocEvents 30) := by decide
    exact (ckx2_fineSmallEvs_seqEnv
      (fun _ he => by rw [he]; exact hca30)
      (fun _ hf => FineSmallEvs.of_freeOnly 0 0 0 hf) hc).mono
      (by decide) (by decide) (by decide)
  have h2act1 : ∀ e, HeaderReceived2aCt1Env ct1Bytes chunk e → FineSmallEvs 1058 1878095 960 e := by
    intro e he
    unfold HeaderReceived2aCt1Env at he
    cases henc : encodeBytesResult ct1Bytes with
    | error _ =>
      rw [henc] at he
      exact (show FineSmallEvs 17 65885 960 e by rw [he]; exact h2apre).mono
        (by decide) (by decide) (Nat.le_refl 960)
    | ok enc =>
      rw [henc] at he
      obtain ⟨hs, hpts_len, hpts_mem⟩ :=
        ckx2_encodeBytesResult_ok_points (by rw [hct1]) (by rw [hct1]; decide) henc
      have hslot30 : ∀ pt ∈ msgPoints ct1Bytes, pt.value.length = 30 := by
        intro pt hpt
        obtain ⟨j, _, hneed⟩ := hpts_mem pt hpt
        rw [hneed, hct1]
        simp [needed]
      exact (ckx2_fineSmallEvs_seqEnv
        (fun _ hp => by rw [hp]; exact h2apre)
        (fun _ hnc => ckx2_polyNextChunkEnv_points_fixed_sub hs hpts_len hslot30
          hiter30 htail30 (by decide) hnc) he).mono
        (by decide) (by decide) (by decide)
  exact (ckx2_fineSmallEvs_seqEnv h1
    (fun _ h2 => ckx2_fineSmallEvs_seqEnv h2act1
      (fun _ hb => by rw [hb]; exact h2b) h2) h).mono
    (by decide) (by decide) (by decide)

theorem ckx2_headerReceived1aEnv_sub_rodataTight {evs : List AllocEvent}
    (h : HeaderReceived1aEnv evs) :
    StatesSendRodataTightEnv evs := by
  rw [h]
  decide

theorem ckx2_statesSendTightEnv_sub_rodataTight {F : ShaCompress} {K : MlKem}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {tape : Bytes} {evs : List AllocEvent}
    (hRod : StatesRodataValid st0)
    (hEnv : StatesSendTightEnv F K st0 tape evs) :
    StatesSendRodataTightEnv evs := by
  unfold StatesSendTightEnv StatesSendEnvOfEnv at hEnv
  cases st0 with
  | keysUnsampled st =>
    dsimp only at hEnv
    split at hEnv
    · exact ckx2_keysUnsampledArmEnv_sub_rodataTight F K st _ _ tape hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | keysSampled st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [Ct1ReceivedSendEkChunkEnv, PolyEncoderNextChunkEnv,
        chunkedKeysSampledToCt1Received] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | headerSent st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [HeaderSentSendEkChunkEnv, PolyEncoderNextChunkEnv] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ct1Received st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [Ct1ReceivedSendEkChunkEnv, PolyEncoderNextChunkEnv] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ekSentCt1Received _ =>
    subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | noHeaderReceived _ =>
    subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | headerReceived st =>
    dsimp only at hEnv
    split at hEnv
    · rename_i outSt chunk es tape' hsend
      exact ckx2_headerReceivedArmEnv_sub_rodataTight hRod
        (ckx2_send_ct1_chunk_ct1_len K hsend) chunk hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ct1Sampled st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [Ct1SampledSendCt1ChunkEnv, PolyEncoderNextChunkEnv] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ekReceivedCt1Sampled st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [EkReceivedCt1SampledSendCt1ChunkEnv, PolyEncoderNextChunkEnv] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ct1Acknowledged _ =>
    subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400
  | ct2Sampled st =>
    dsimp only [StatesRodataValid] at hRod
    dsimp only at hEnv
    split at hEnv
    · dsimp only [Ct2SampledSendCt2ChunkEnv, PolyEncoderNextChunkEnv] at hEnv
      exact ckx2_polyNextChunkEnv_sub_rodataTight hRod hEnv
    · subst hEnv; exact FineSmallEvs.nil 1233 2124238 2400

/-! ## `<Message>::serialize` and `<Chain>::add_epoch` Tight Leaf Inclusions -/

theorem ckx2_messageSerializeEnv_sub_tight (x : MessageSerializeGhost spqrPolyApi)
    {evs : List AllocEvent} (h : MessageSerializeEnv spqrPolyApi x evs) :
    MessageSerializeTightEnv evs := by
  rw [h]
  unfold messageSerializeEvents
  dsimp only
  split <;> first | decide | (split <;> decide)

theorem ckx2_chainAddEpochEnv_sub_tight4 (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    (hlinks : x.self.links.length ≤ 4) {evs : List AllocEvent}
    (h : ChainAddEpochEnv hkdf x evs) :
    ChainAddEpochTight4Env evs := by
  unfold ChainAddEpochEnv at h
  split at h
  · subst h; exact FineSmallEvs.nil 6 14641 896
  · subst h
    unfold chainAddEpochEvents
    have ha32 : FineSmallEvs 1 738 896 (rustAllocEvents 32 1) := by decide
    have ha72 : FineSmallEvs 1 1607 896 (rustAllocEvents 72 1) := by decide
    have hd : ∀ c : BitVec 64,
        FineSmallEvs 0 0 896 (if c = 0#64 then [] else rustDeallocEvents c.toNat 1) := by
      intro c
      split
      · exact FineSmallEvs.nil 0 0 896
      · exact FineSmallEvs.of_freeOnly 0 0 896 (FreeOnlyEvs.singleton 1 c.toNat)
    have hvd : FineSmallEvs 1 9213 896
        (if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap
         else []) := by
      split
      · rename_i heq
        have hcap : x.G.linksCap.toNat ≤ 4 := heq ▸ hlinks
        have hcases : x.G.linksCap = 0#64 ∨ x.G.linksCap = 1#64 ∨ x.G.linksCap = 2#64 ∨
            x.G.linksCap = 3#64 ∨ x.G.linksCap = 4#64 := by
          have hn : x.G.linksCap.toNat = 0 ∨ x.G.linksCap.toNat = 1 ∨
              x.G.linksCap.toNat = 2 ∨ x.G.linksCap.toNat = 3 ∨
              x.G.linksCap.toNat = 4 := by omega
          rcases hn with h0 | h1 | h2 | h3 | h4
          · exact Or.inl (BitVec.eq_of_toNat_eq h0)
          · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h1))
          · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h2)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h3))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h4))))
        rcases hcases with hc | hc | hc | hc | hc <;> (rw [hc]; decide)
      · exact FineSmallEvs.nil 1 9213 896
    exact (((((((ha32.append (hd x.G.nextRoot.cap)).append ha72).append ha32).append ha72).append
      ha32).append hvd).append (hd x.esPin.cap)).mono (by decide) (by decide) (by decide)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendStage1AuxR2
