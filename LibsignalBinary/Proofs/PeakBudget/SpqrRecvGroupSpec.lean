/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec

/-!
# Tight `PhaseGroupSpec` Bounds for SPQR `spqr::recv`

Bounds `FineScale`-scaled `mallocng` slot-group creation (`fineGroupsScaled`, `FineScale = 65,536`)
across `spqr::recv` (`Block 329`). Combines the `<Chain>::recv_key` group bound (`420,047,262`
scaled units = `6,410` groups across up to `25,001` `35`-byte HKDF info allocations and at most `18`
`KeyHistory` `Vec<u8>` doublings, independent of `x.G`) with parametric codec and `<States>::recv`
group hypotheses across all three version-ordering branches.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainEpochDirection ChainPB ChainParamsPB EpochSecret HkdfFn KeyHistory Message
   MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB chainFrom spqrAuthApi
   spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost chainEpochAlign
   chainEpochSize)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawChain rawV1State)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec fineGroupsScaled nonFreeCount
   nonFreeCount_rustAllocEvents nonFreeCount_rustReallocEvents smallAllocGroupS_fineCostModel_eq
   smallAllocGroupS_le_16659_of_le_44 smallAllocGroupS_le_43464_of_le_108
   stepEvents_groupsScaled_le_nonFreeCount)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv decodeStateTightEnv_nonFreeCount_le
   decodeStateTightEnv_nonFreeCount_le_128 statesFromPbTightEnv_nonFreeCount_le
   statesFromPbTightEnv_nonFreeCount_le_128 statesIntoPbTightEnv_nonFreeCount_le
   statesIntoPbTightEnv_nonFreeCount_le_128)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
  (keyAddBudget nextKeyInternalReq recvKeyCapMax virtCap)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
  (OptChainAddEpochEnv SpqrRecvGreaterCallEnv SpqrRecvLessCallEnv V0ChainInitEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvEqualTightEnv SpqrRecvTightDomain SpqrRecvTightEnv
   V1ChainAndEncodeTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw (states_recv_raw_le_2976)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidChainParams ValidChainParamsPB ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (StatesPtsBoundedAt ValidPqPtsAt ValidV1PtsAt statesPtsBoundedAt_of_from_pb
   statesPtsBoundedAt_of_recv validV1PtsAt_states_into_pb)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (ChainNewEnv NextKeyInternalEnv chainNewEvents nextKeyInternalEvents vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents doReserveStep keyAdvanceLoopEvents keyHistoryAddStep)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromEnv ChainFromVersionNegotiationEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs StatesIntoPbEnv)

/-! ## Group Constants and Combinators (`FineScale = 65,536`) -/

/-- Scaled group bound for `<Chain>::recv_key` (`25,001 * 16,659 + 16,659 + 18 * 196,608 = 420,047,262`, `6,410` groups).
-/
def chainRecvKeyTightGroupS : Nat := 420047262

def chainRecvKeyTightGroups : Nat := 6410

/-- Scaled group bound for `V1ChainAndEncodeTightEnv` excluding `StatesIntoPbEnv'` (`421,107,504`, `6,426` groups).
-/
def v1ChainAndEncodeTightGroupS : Nat := 421107504

theorem chainRecvKeyTightGroups_eq :
    (chainRecvKeyTightGroupS + FineScale - 1) / FineScale = chainRecvKeyTightGroups := by
  decide

theorem phaseGroupSpec_of_false {M : AllocCostModel} [HasFineGroupCredit M]
    {Env : List AllocEvent → Prop} (g : Nat) (hf : ∀ evs, ¬ Env evs) :
    PhaseGroupSpec M Env g :=
  ((PhaseGroupSpec.nil M).of_imp fun evs h => False.elim (hf evs h)).mono (Nat.zero_le g)

theorem phaseGroupSpec_or_freeOnly {M : AllocCostModel} [HasFineGroupCredit M]
    {E : List AllocEvent → Prop} {g : Nat} (h : PhaseGroupSpec M E g) :
    PhaseGroupSpec M (fun evs => FreeOnlyEvs evs ∨ E evs) g :=
  ((PhaseGroupSpec.freeOnly M).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le g, Nat.le_refl g⟩)

theorem phaseGroupSpec_seq_freeOnly_left {M : AllocCostModel} [HasFineGroupCredit M]
    {E : List AllocEvent → Prop} {g : Nat} (h : PhaseGroupSpec M E g) :
    PhaseGroupSpec M (SeqEnv FreeOnlyEvs E) g :=
  ((PhaseGroupSpec.freeOnly M).seq h).mono (by simp)

theorem phaseGroupSpec_seq_freeOnly_right {M : AllocCostModel} [HasFineGroupCredit M]
    {E : List AllocEvent → Prop} {g : Nat} (h : PhaseGroupSpec M E g) :
    PhaseGroupSpec M (SeqEnv E FreeOnlyEvs) g :=
  (h.seq (PhaseGroupSpec.freeOnly M)).mono (by simp)

private theorem group_add3_le {g0 g1 g2 g3 a b c bound : Nat}
    (h1 : g1 ≤ g0 + a) (h2 : g2 ≤ g1 + b) (h3 : g3 ≤ g2 + c)
    (habc : (a + b) + c ≤ bound) :
    g3 ≤ g0 + bound := by
  omega

/-! ## Leaf and Non-Loop Chain `PhaseGroupSpec` Lemmas -/

private theorem nonFreeCount_eq_defsPlaced :
    ∀ evs : List AllocEvent,
      nonFreeCount evs =
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.nonFreeCount evs
  | [] => rfl
  | .free _ _ :: tl => nonFreeCount_eq_defsPlaced tl
  | .alloc _ :: tl => congrArg (· + 1) (nonFreeCount_eq_defsPlaced tl)
  | .aligned _ _ :: tl => congrArg (· + 1) (nonFreeCount_eq_defsPlaced tl)
  | .realloc _ _ _ :: tl => congrArg (· + 1) (nonFreeCount_eq_defsPlaced tl)

theorem nonFreeBound_spqrBoundedEvs (maxAllocs maxReq : Nat) :
    NonFreeBound (SpqrBoundedEvs maxAllocs maxReq) maxAllocs := by
  intro evs hE
  rw [nonFreeCount_eq_defsPlaced]
  exact hE.1

theorem spqrBoundedEvs_phaseGroupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxAllocs maxReq : Nat) :
    PhaseGroupSpec M (SpqrBoundedEvs maxAllocs maxReq) (3 * FineScale * maxAllocs) :=
  PhaseGroupSpec.of_nonFreeBound M (nonFreeBound_spqrBoundedEvs maxAllocs maxReq)

/-- `InitInnerEnv F x` performs at most `96` non-`.free` operations (`18,874,368` scaled units, `288` groups).
-/
theorem initInner_fine_phaseGroupSpec (F : ShaCompress) (x : InitInnerGhost) :
    PhaseGroupSpec fineCostModel (InitInnerEnv F x) 18874368 := by
  unfold InitInnerEnv
  cases x.v with
  | v0 => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | v1 =>
    exact (spqrBoundedEvs_phaseGroupSpec fineCostModel 96
      (2 * x.authKey.length + 2048)).mono (by decide)

theorem statesIntoPb_fallback_fine_phaseGroupSpec {F : ShaCompress} (x : StatesIntoPbGhost F) :
    PhaseGroupSpec fineCostModel (StatesIntoPbEnv x) 12582912 :=
  (spqrBoundedEvs_phaseGroupSpec fineCostModel 64 _).mono (by decide)

/-- `PhaseGroupSpec` for `NextKeyInternalEnv` (`35`-byte HKDF info allocation + free, `≤ 16,659` scaled units).
-/
theorem nextKeyInternal_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel NextKeyInternalEnv 16659 := by
  have ha := PhaseGroupSpec.rustAlloc_small fineCostModel
    (size := nextKeyInternalReq) (align := 1) (by decide) (by decide)
  have hd := PhaseGroupSpec.rustDealloc fineCostModel nextKeyInternalReq 1
  have h16659 : HasFineGroupCredit.smallAllocGroupS fineCostModel nextKeyInternalReq ≤ 16659 := by
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_16659_of_le_44 (by decide)
  have hcat : PhaseGroupSpec fineCostModel NextKeyInternalEnv
      (HasFineGroupCredit.smallAllocGroupS fineCostModel nextKeyInternalReq + 0) :=
    (ha.concat hd).of_imp fun evs hE => by
      rw [hE]
      exact ConcatEnv.append rfl rfl
  exact hcat.mono (by omega)

/-- `PhaseGroupSpec` for `ChainNewEnv` (`2 * 43,464 + 3 * 16,659 + 196,608 = 333,513` scaled units).
-/
theorem chainNew_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel ChainNewEnv 333513 := by
  have ha72 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 72 1) 43464 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 72) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_43464_of_le_108 (by decide)
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_16659_of_le_44 (by decide)
  have ha448 : PhaseGroupSpec fineCostModel
      (· = rustAllocEvents (4 * chainEpochSize) chainEpochAlign) 196608 :=
    (PhaseGroupSpec.rustAlloc_any fineCostModel (4 * chainEpochSize) chainEpochAlign).mono
      (by decide)
  have h6 := ((((ha72.concat ha32).concat ha72).concat ha32).concat ha448).concat ha32
  have h6' := h6.of_imp (E₁ := ChainNewEnv) fun evs hE => by
    rw [hE]
    unfold chainNewEvents
    exact ConcatEnv.append
      (ConcatEnv.append
        (ConcatEnv.append
          (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl
  exact h6'.mono (by decide)

private theorem chainFromNewEvents_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel
      (· = LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents) 333513 := by
  have ha72 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 72 1) 43464 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 72) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_43464_of_le_108 (by decide)
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_16659_of_le_44 (by decide)
  have ha448 := (PhaseGroupSpec.rustAlloc_any fineCostModel 448 8).mono
    (by decide : 3 * FineScale ≤ 196608)
  have h6 := ((((ha72.concat ha32).concat ha72).concat ha32).concat ha448).concat ha32
  have h6' := h6.of_imp
    (E₁ := (· = LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents))
    fun evs hE => by
      rw [hE]
      unfold LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents
      exact ConcatEnv.append
        (ConcatEnv.append
          (ConcatEnv.append
            (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl
  exact h6'.mono (by decide)

theorem chainFrom_fine_phaseGroupSpec (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    PhaseGroupSpec fineCostModel (ChainFromEnv pb vn) 333513 := by
  cases pb with
  | some _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  | none =>
    cases vn with
    | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | some v =>
      change PhaseGroupSpec fineCostModel (ChainFromVersionNegotiationEnv v) 333513
      unfold ChainFromVersionNegotiationEnv
      split
      · exact chainFromNewEvents_fine_phaseGroupSpec
      · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)

private theorem vecDequeGrow_fine_phaseGroupSpec (cap : BitVec 64) :
    PhaseGroupSpec fineCostModel (· = vecDequeGrowEvents cap) 196608 := by
  have hnf : NonFreeBound (· = vecDequeGrowEvents cap) 1 := by
    rintro _ rfl
    unfold vecDequeGrowEvents
    split
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem chainAddEpoch_fine_phaseGroupSpec (hkdf : HkdfFn) (x : ChainAddEpochGhost) :
    PhaseGroupSpec fineCostModel (ChainAddEpochEnv hkdf x) 333513 := by
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_16659_of_le_44 (by decide)
  have ha72 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 72 1) 43464 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 72) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_43464_of_le_108 (by decide)
  have hd_nr : PhaseGroupSpec fineCostModel
      (· = if x.G.nextRoot.cap = 0#64 then [] else rustDeallocEvents x.G.nextRoot.cap.toNat 1) 0 := by
    split
    · exact PhaseGroupSpec.nil fineCostModel
    · exact PhaseGroupSpec.rustDealloc fineCostModel _ 1
  have hd_es : PhaseGroupSpec fineCostModel
      (· = if x.esPin.cap = 0#64 then [] else rustDeallocEvents x.esPin.cap.toNat 1) 0 := by
    split
    · exact PhaseGroupSpec.nil fineCostModel
    · exact PhaseGroupSpec.rustDealloc fineCostModel _ 1
  have hgrow : PhaseGroupSpec fineCostModel
      (· = if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap else [])
      196608 := by
    split
    · exact vecDequeGrow_fine_phaseGroupSpec x.G.linksCap
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  have hseq :=
    (((((((ha32.concat hd_nr).concat ha72).concat ha32).concat ha72).concat ha32).concat hgrow).concat hd_es)
  have hok : PhaseGroupSpec fineCostModel (· = chainAddEpochEvents x) 333513 :=
    (hseq.of_imp fun evs hE => by
      rw [hE]
      unfold chainAddEpochEvents
      exact ConcatEnv.append
        (ConcatEnv.append
          (ConcatEnv.append
            (ConcatEnv.append
              (ConcatEnv.append
                (ConcatEnv.append
                  (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl) rfl) rfl).mono (by decide)
  unfold ChainAddEpochEnv
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact hok

theorem chainIntoPb_fine_phaseGroupSpec (x : ChainIntoPbCall) :
    PhaseGroupSpec fineCostModel (ChainIntoPbEnv x) 196608 := by
  by_cases hempty : x.chain.links = []
  · exact ((PhaseGroupSpec.freeOnly fineCostModel).of_imp fun evs hE => by
      simp only [ChainIntoPbEnv, hempty, ↓reduceIte] at hE
      exact hE).mono (Nat.zero_le _)
  · have hcat := (PhaseGroupSpec.rustAlloc_any fineCostModel (x.chain.links.length * 112) 8).concat
      (PhaseGroupSpec.freeOnly fineCostModel)
    have hcat' := hcat.of_imp (E₁ := ChainIntoPbEnv x) fun evs hE => by
      simp only [ChainIntoPbEnv, hempty, ↓reduceIte] at hE
      obtain ⟨ef, hf, heq⟩ := hE
      exact ⟨rustAllocEvents (x.chain.links.length * 112) 8, ef, heq, rfl, hf⟩
    exact hcat'.mono (by decide)

theorem pqRatchetStateEncodeToVec_fine_phaseGroupSpec (st : PqRatchetState) :
    PhaseGroupSpec fineCostModel (PqRatchetStateEncodeToVecEnv st) 196608 := by
  have hnil : PhaseGroupSpec fineCostModel
      (fun evs => CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStatePBEncodedLen st = 0 ∧
        evs = []) 0 :=
    (PhaseGroupSpec.nil fineCostModel).of_imp fun _ h => h.2
  have halloc : PhaseGroupSpec fineCostModel
      (fun evs => 0 < CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStatePBEncodedLen st ∧
        evs = rustAllocEvents
          (CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStatePBEncodedLen st) 1) 196608 :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel _ 1).of_imp fun _ h => h.2).mono (by decide)
  exact (hnil.or halloc).mono (by decide)

/-! ## `<Chain>::recv_key` `PhaseGroupSpec` (`420,047,262` = `6,410` Groups) -/

private theorem doReserveStep_groupsScaled_spec
    {cap len additional maxLen d : Nat}
    (hlen : len + additional ≤ maxLen)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := doReserveStep cap len additional
    ∃ d', d' ≤ d ∧
      maxLen < virtCap res.1 * 2 ^ d' ∧
      (∀ st : fineCostModel.σ,
        HasFineGroupCredit.groupsScaled (fineCostModel.stepEvents res.2 st) ≤
          HasFineGroupCredit.groupsScaled st + (d - d') * (3 * FineScale)) := by
  dsimp only [doReserveStep]
  by_cases hfit : len + additional ≤ cap
  · rw [ite_eq_left hfit]
    dsimp only
    refine ⟨d, Nat.le_refl d, hinv, fun st => ?_⟩
    simp only [AllocCostModel.stepEvents_nil, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_refl _
  · rw [ite_eq_right hfit]
    have hlt : cap < len + additional := by omega
    cases d with
    | zero =>
      exfalso
      unfold virtCap at hinv
      split at hinv <;> simp only [Nat.pow_zero, Nat.mul_one] at hinv <;> omega
    | succ d' =>
      set cap' := reserveCap cap len additional
      dsimp only
      have hvirt : 2 * virtCap cap ≤ virtCap cap' := by
        unfold virtCap cap' reserveCap
        split
        · rw [ite_eq_right (by omega)]; omega
        · rw [ite_eq_right (by omega)]; omega
      have hinv' : maxLen < virtCap cap' * 2 ^ d' := by
        have hpow : virtCap cap * 2 ^ (d' + 1) = (2 * virtCap cap) * 2 ^ d' := by
          rw [Nat.pow_succ]; ring
        have hmul : (2 * virtCap cap) * 2 ^ d' ≤ virtCap cap' * 2 ^ d' :=
          Nat.mul_le_mul_right (2 ^ d') hvirt
        omega
      have hsub1 : d' + 1 - d' = 1 := by omega
      refine ⟨d', Nat.le_succ d', hinv', fun st => ?_⟩
      rw [hsub1, Nat.one_mul]
      have hcnt : nonFreeCount (if cap = 0 then rustAllocEvents cap' 1 else
          rustReallocEvents cap cap' 1) = 1 := by
        split
        · rw [nonFreeCount_rustAllocEvents]
        · rw [nonFreeCount_rustReallocEvents]
      have hle := stepEvents_groupsScaled_le_nonFreeCount fineCostModel
        (if cap = 0 then rustAllocEvents cap' 1 else rustReallocEvents cap cap' 1) st
      rw [hcnt, Nat.mul_one] at hle
      exact hle

private theorem keyHistoryAddStep_groupsScaled_spec
    {cap len maxLen d : Nat}
    (hlen : len + 36 ≤ maxLen)
    (hinv : maxLen < virtCap cap * 2 ^ d) :
    let res := keyHistoryAddStep cap len
    ∃ d2, d2 ≤ d ∧
      maxLen < virtCap res.1 * 2 ^ d2 ∧
      (∀ st : fineCostModel.σ,
        HasFineGroupCredit.groupsScaled (fineCostModel.stepEvents res.2 st) ≤
          HasFineGroupCredit.groupsScaled st + (d - d2) * (3 * FineScale)) := by
  dsimp only [keyHistoryAddStep]
  set r1 := doReserveStep cap len 4
  set r2 := doReserveStep r1.1 (len + 4) 32
  obtain ⟨d1, hd1_le, hinv1, hgr1⟩ :=
    doReserveStep_groupsScaled_spec (cap := cap) (len := len) (additional := 4) (by omega) hinv
  obtain ⟨d2, hd2_le, hinv2, hgr2⟩ :=
    doReserveStep_groupsScaled_spec (cap := r1.1) (len := len + 4) (additional := 32) hlen hinv1
  refine ⟨d2, Nat.le_trans hd2_le hd1_le, hinv2, fun st => ?_⟩
  rw [fineCostModel.stepEvents_append]
  have b1 := hgr1 st
  have b2 := hgr2 (fineCostModel.stepEvents r1.2 st)
  have hdist : (d - d1) * (3 * FineScale) + (d1 - d2) * (3 * FineScale) =
      (d - d2) * (3 * FineScale) := by
    rw [← Nat.add_mul]; congr 1; omega
  dsimp only [r1, r2] at *
  omega

private theorem nextKeyInternal_ctr_and_key_len_grp
    (hkdf : HkdfFn) {next : Bytes} {ctr : BitVec 32}
    {next1 : Bytes} {ctr1 cOut : BitVec 32} {key : Bytes}
    (h : ChainEpochDirection.nextKeyInternal hkdf next ctr = .ok (next1, ctr1, (cOut, key))) :
    ctr1.toNat = ctr.toNat + 1 ∧ key.length ≤ 32 := by
  unfold ChainEpochDirection.nextKeyInternal at h
  by_cases hlen : (next.length != 32) = true
  · simp [hlen] at h
  · by_cases hmax : (ctr == 0xffffffff#32) = true
    · simp [hlen, hmax] at h
    · simp only [hlen, hmax, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨_, hctr1, _, rfl⟩
      have hne : ctr.toNat ≠ 0xffffffff := by
        intro heq; apply hmax; apply beq_iff_eq.mpr; exact BitVec.eq_of_toNat_eq heq
      have hlt : ctr.toNat < 2 ^ 32 - 1 := by have := ctr.isLt; omega
      have hctr_nat : (ctr + 1#32).toNat = ctr.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨hctr1 ▸ hctr_nat, List.length_take_le 32 _⟩

private theorem keyAdvanceLoopEvents_groupsScaled_amortized
    (hkdf : HkdfFn) (params : ChainParamsPB) (atIdx : BitVec 32) :
    ∀ (rem : Nat) (ced : ChainEpochDirection) (cap maxLen d : Nat),
      ced.prev.data.length +
        36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ced.ctr.toNat ≤ maxLen →
      maxLen < virtCap cap * 2 ^ d →
      ∀ st : fineCostModel.σ,
        HasFineGroupCredit.groupsScaled
          (fineCostModel.stepEvents (keyAdvanceLoopEvents hkdf params atIdx rem ced cap) st) ≤
          HasFineGroupCredit.groupsScaled st + rem * 16659 + d * (3 * FineScale) := by
  intro rem
  induction rem with
  | zero =>
    intro ced cap maxLen d _ _ st
    dsimp only [keyAdvanceLoopEvents]
    simp only [AllocCostModel.stepEvents_nil, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_add_right _ _
  | succ rem ih =>
    intro ced cap maxLen d hlenB hinv st
    dsimp only [keyAdvanceLoopEvents]
    have hnki := nextKeyInternal_fine_phaseGroupSpec
    by_cases hlt_idx : ced.ctr.toNat + 1 < atIdx.toNat
    · rw [ite_eq_left hlt_idx]
      cases hnki_call : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr with
      | error _ =>
        simp only [AllocCostModel.stepEvents_nil]
        omega
      | ok res =>
        rcases res with ⟨next1, ctr1, cOut, key⟩
        dsimp only
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len_grp hkdf hnki_call
        set maxOoo := params.maxOooKeysOrDefault
        have hstep_r : (rem + 1) * 16659 = 16659 + rem * 16659 := by
          rw [Nat.succ_mul, Nat.add_comm]
        by_cases hovf : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          have b1 := hnki.groups_le st rfl
          rw [hstep_r]; omega
        · rw [ite_eq_right hovf]
          by_cases hwin : ctr1 + maxOoo ≥ atIdx
          · rw [ite_eq_left hwin]
            have hsum_nat : (ctr1 + maxOoo).toNat = ctr1.toNat + maxOoo.toNat := by
              rw [BitVec.toNat_add]; omega
            have hge_idx : ctr1.toNat + maxOoo.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin; omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_pos; omega
            obtain ⟨d2, hd2_le, hinv2, hgr_add⟩ :=
              keyHistoryAddStep_groupsScaled_spec hlen36 hinv
            set addRes := keyHistoryAddStep cap ced.prev.data.length
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len :=
                CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.add_length_le
                  ced.prev (ctr1, key) params hkey_len
              change (ced.prev.add (ctr1, key) params).data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              rw [hbud_next]; omega
            rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
            have b1 := hnki.groups_le st rfl
            have b2 := hgr_add (fineCostModel.stepEvents nextKeyInternalEvents st)
            have b3 := ih ced' addRes.1 maxLen d2 hlenB' hinv2
              (fineCostModel.stepEvents addRes.2
                (fineCostModel.stepEvents nextKeyInternalEvents st))
            have hmul_d : (d - d2) * (3 * FineScale) + d2 * (3 * FineScale) =
                d * (3 * FineScale) := by
              rw [← Nat.add_mul]; congr 1; omega
            rw [hstep_r]; omega
          · rw [ite_eq_right hwin]
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev }
            have hbud_le : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_le
              change ced.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              omega
            rw [fineCostModel.stepEvents_append]
            have b1 := hnki.groups_le st rfl
            have b2 := ih ced' cap maxLen d hlenB' hinv
              (fineCostModel.stepEvents nextKeyInternalEvents st)
            rw [hstep_r]; omega
    · rw [ite_eq_right hlt_idx]
      simp only [AllocCostModel.stepEvents_nil]
      omega

private theorem keyHistoryAddStep_eq_self_grp {cap len : Nat} (h : len + 36 ≤ cap) :
    keyHistoryAddStep cap len = (cap, []) := by
  have h1 : len + 4 ≤ cap := by omega
  have h2 : len + 4 + 32 ≤ cap := by omega
  simp only [keyHistoryAddStep, doReserveStep, h1, h2, ↓reduceIte, List.nil_append]

private theorem keyAdvanceLoopEvents_groupsScaled_ge
    (hkdf : HkdfFn) (params : ChainParamsPB) (atIdx : BitVec 32) :
    ∀ (rem : Nat) (ced : ChainEpochDirection) (cap maxLen : Nat),
      ced.prev.data.length +
        36 * keyAddBudget atIdx.toNat params.maxOooKeysOrDefault.toNat ced.ctr.toNat ≤ maxLen →
      maxLen ≤ cap →
      ∀ st : fineCostModel.σ,
        HasFineGroupCredit.groupsScaled
          (fineCostModel.stepEvents (keyAdvanceLoopEvents hkdf params atIdx rem ced cap) st) ≤
          HasFineGroupCredit.groupsScaled st + rem * 16659 := by
  intro rem
  induction rem with
  | zero =>
    intro ced cap maxLen _ _ st
    dsimp only [keyAdvanceLoopEvents]
    simp only [AllocCostModel.stepEvents_nil, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_refl _
  | succ rem ih =>
    intro ced cap maxLen hlenB hcap_ge st
    dsimp only [keyAdvanceLoopEvents]
    have hnki := nextKeyInternal_fine_phaseGroupSpec
    by_cases hlt_idx : ced.ctr.toNat + 1 < atIdx.toNat
    · rw [ite_eq_left hlt_idx]
      cases hnki_call : ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr with
      | error _ =>
        simp only [AllocCostModel.stepEvents_nil]
        omega
      | ok res =>
        rcases res with ⟨next1, ctr1, cOut, key⟩
        dsimp only
        obtain ⟨hctr1_nat, hkey_len⟩ := nextKeyInternal_ctr_and_key_len_grp hkdf hnki_call
        set maxOoo := params.maxOooKeysOrDefault
        have hstep_r : (rem + 1) * 16659 = 16659 + rem * 16659 := by
          rw [Nat.succ_mul, Nat.add_comm]
        by_cases hovf : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          have b1 := hnki.groups_le st rfl
          rw [hstep_r]; omega
        · rw [ite_eq_right hovf]
          by_cases hwin : ctr1 + maxOoo ≥ atIdx
          · rw [ite_eq_left hwin]
            have hsum_nat : (ctr1 + maxOoo).toNat = ctr1.toNat + maxOoo.toNat := by
              rw [BitVec.toNat_add]; omega
            have hge_idx : ctr1.toNat + maxOoo.toNat ≥ atIdx.toNat := by
              have : atIdx.toNat ≤ (ctr1 + maxOoo).toNat := hwin; omega
            have hbud_pos : 1 ≤ keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            have hbud_next : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat =
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1 := by
              unfold keyAddBudget; omega
            have hlen36 : ced.prev.data.length + 36 ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_pos; omega
            rw [keyHistoryAddStep_eq_self_grp (Nat.le_trans hlen36 hcap_ge)]
            dsimp only
            rw [List.append_nil]
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have hadd_len :=
                CryptoVerification.SpqrV1.Top.StateSize.KeyHistory.add_length_le
                  ced.prev (ctr1, key) params hkey_len
              have hmul :
                  36 * (keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat - 1) + 36 =
                  36 * keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
                have := Nat.mul_sub_left_distrib 36
                  (keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat) 1
                omega
              change (ced.prev.add (ctr1, key) params).data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              rw [hbud_next]; omega
            rw [fineCostModel.stepEvents_append]
            have b1 := hnki.groups_le st rfl
            have b2 := ih ced' cap maxLen hlenB' hcap_ge
              (fineCostModel.stepEvents nextKeyInternalEvents st)
            rw [hstep_r]; omega
          · rw [ite_eq_right hwin]
            have hbud_le : keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤
                keyAddBudget atIdx.toNat maxOoo.toNat ced.ctr.toNat := by
              unfold keyAddBudget; omega
            set ced' : ChainEpochDirection :=
              { ctr := ctr1, next := next1, prev := ced.prev }
            have hlenB' : ced'.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ced'.ctr.toNat ≤ maxLen := by
              have := Nat.mul_le_mul_left 36 hbud_le
              change ced.prev.data.length +
                36 * keyAddBudget atIdx.toNat maxOoo.toNat ctr1.toNat ≤ maxLen
              omega
            rw [fineCostModel.stepEvents_append]
            have b1 := hnki.groups_le st rfl
            have b2 := ih ced' cap maxLen hlenB' hcap_ge
              (fineCostModel.stepEvents nextKeyInternalEvents st)
            rw [hstep_r]; omega
    · rw [ite_eq_right hlt_idx]
      simp only [AllocCostModel.stepEvents_nil]
      omega

/-- Tight `PhaseGroupSpec` for `<spqr::chain::Chain>::recv_key` (`420,047,262` scaled units = `6,410`
groups) across up to `25,001` `nextKeyInternal` calls, one `32`-byte output allocation, and at most
`18` `KeyHistory` doublings, independent of `x.G`. -/
theorem chainRecvKey_fine_phaseGroupSpec_tight
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost)
    (hJump : x.self.params.maxJumpOrDefault.toNat ≤ 25000)
    (hOoo : x.self.params.maxOooKeysOrDefault.toNat ≤ 2000)
    (hPrevLen : ∀ link ∈ x.self.links, link.recv.prev.data.length ≤ 79236) :
    PhaseGroupSpec fineCostModel (ChainRecvKeyEnv hkdf x) chainRecvKeyTightGroupS := by
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 := by
    refine (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono ?_
    rw [smallAllocGroupS_fineCostModel_eq]
    exact smallAllocGroupS_le_16659_of_le_44 (by decide)
  have hnki := nextKeyInternal_fine_phaseGroupSpec
  have hnil : PhaseGroupSpec fineCostModel (· = []) chainRecvKeyTightGroupS :=
    (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  unfold ChainRecvKeyEnv chainRecvKeyEvents
  split
  · exact hnil
  · cases heidx : x.self.epochIdx x.epoch with
    | error _ => exact hnil
    | ok epochIndex =>
      dsimp only
      split
      · next hlt_links =>
        set link := x.self.links[epochIndex]'hlt_links
        set gCap := if hg : epochIndex < x.G.epochs.length then
            (x.G.epochs[epochIndex]'hg).recv.prev.cap.toNat else 0
        split
        · cases link.recv.prev.get x.index link.recv.ctr x.self.params with
          | error _ => exact hnil
          | ok _ => exact ha32.mono (by decide)
        · next hnot_lt =>
          split
          · exact hnil
          · split
            · exact hnil
            · next hjump_le =>
              split
              · exact hnil
              · set maxOoo := x.self.params.maxOooKeysOrDefault
                set self0 : ChainEpochDirection := if x.index > link.recv.ctr + maxOoo then
                    { link.recv with prev := link.recv.prev.clear } else link.recv
                set rem := x.index.toNat - self0.ctr.toNat
                have hctr_le : link.recv.ctr.toNat ≤ x.index.toNat := by
                  have : ¬ (x.index.toNat < link.recv.ctr.toNat) := hnot_lt; omega
                have hsub_nat : (x.index - link.recv.ctr).toNat =
                    x.index.toNat - link.recv.ctr.toNat := BitVec.toNat_sub_of_le hctr_le
                have hself0_ctr : self0.ctr = link.recv.ctr := by dsimp only [self0]; split <;> rfl
                have hrem_le : rem ≤ 25000 := by
                  have hj : (x.index - link.recv.ctr).toNat ≤ x.self.params.maxJumpOrDefault.toNat :=
                    Nat.not_lt.mp hjump_le
                  dsimp only [rem]; rw [hself0_ctr]; omega
                have hlink_mem : link ∈ x.self.links := List.getElem_mem hlt_links
                have hself0_len : self0.prev.data.length ≤ 79236 := by
                  dsimp only [self0]; split
                  · simp [KeyHistory.clear]
                  · exact hPrevLen link hlink_mem
                set maxLen : Nat := 79236 + 36 * 2000
                have hbud_le : keyAddBudget x.index.toNat maxOoo.toNat self0.ctr.toNat ≤ 2000 :=
                  Nat.le_trans (Nat.min_le_right _ _) hOoo
                have hlenB0 : self0.prev.data.length +
                    36 * keyAddBudget x.index.toNat maxOoo.toNat self0.ctr.toNat ≤ maxLen := by
                  have hmul := Nat.mul_le_mul_left 36 hbud_le; omega
                have hrem_mul : rem * 16659 ≤ 25000 * 16659 :=
                  Nat.mul_le_mul_right 16659 hrem_le
                by_cases hg_le : gCap ≤ maxLen
                · have hvirt_pos : 1 ≤ virtCap gCap := by unfold virtCap; split <;> omega
                  have hd18 : maxLen < 1 * 2 ^ 18 := by decide
                  have hinv0 : maxLen < virtCap gCap * 2 ^ 18 :=
                    Nat.lt_of_lt_of_le hd18 (Nat.mul_le_mul_right (2 ^ 18) hvirt_pos)
                  refine { groups_le := ?_ }
                  rintro st0 _ rfl
                  rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
                  set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                  have b1 := keyAdvanceLoopEvents_groupsScaled_amortized
                    hkdf x.self.params x.index rem self0 gCap maxLen 18 hlenB0 hinv0 st0
                  have b2 := hnki.groups_le (fineCostModel.stepEvents evLoop st0) rfl
                  have b3 := ha32.groups_le
                    (fineCostModel.stepEvents nextKeyInternalEvents
                      (fineCostModel.stepEvents evLoop st0)) rfl
                  have htot :
                      ((rem * 16659 + 18 * (3 * FineScale)) + 16659) + 16659 ≤
                        chainRecvKeyTightGroupS := by
                    have h1 : rem * 16659 + 18 * (3 * FineScale) ≤
                        25000 * 16659 + 18 * (3 * FineScale) :=
                      Nat.add_le_add_right hrem_mul _
                    exact Nat.le_trans
                      (Nat.add_le_add_right (Nat.add_le_add_right h1 16659) 16659)
                      (by decide)
                  exact group_add3_le (Nat.add_assoc _ _ _ ▸ b1) b2 b3 htot
                · have hg_ge : maxLen ≤ gCap := by omega
                  refine { groups_le := ?_ }
                  rintro st0 _ rfl
                  rw [fineCostModel.stepEvents_append, fineCostModel.stepEvents_append]
                  set evLoop := keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap
                  have b1 := keyAdvanceLoopEvents_groupsScaled_ge
                    hkdf x.self.params x.index rem self0 gCap maxLen hlenB0 hg_ge st0
                  have b2 := hnki.groups_le (fineCostModel.stepEvents evLoop st0) rfl
                  have b3 := ha32.groups_le
                    (fineCostModel.stepEvents nextKeyInternalEvents
                      (fineCostModel.stepEvents evLoop st0)) rfl
                  have htot : (rem * 16659 + 16659) + 16659 ≤ chainRecvKeyTightGroupS :=
                    Nat.le_trans
                      (Nat.add_le_add_right (Nat.add_le_add_right hrem_mul 16659) 16659)
                      (by decide)
                  exact group_add3_le b1 b2 b3 htot
      · exact hnil

/-! ## Codec / `<States>::recv` Group Bundles and `spqr::recv` Branch Specs -/

/-- `PhaseGroupSpec` hypothesis bundle for `spqr::decode_state`, `<States>::from_pb`, and `<States>::into_pb`.
-/
structure C07TightGroupSpec (F : ShaCompress)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (gDecS gFromS gIntoS : Nat) : Prop where
  decode_group :
    ∀ stBytes : Bytes,
      stBytes.length ≤ spqrStateTightCapBytes →
      ValidEncoderPts640 stBytes →
      ValidChainParams stBytes →
      PhaseGroupSpec fineCostModel (DecodeStateEnv stBytes) gDecS
  fromPb_group :
    ∀ pb : V1State,
      ValidV1PtsAt 640 pb →
      rawV1State pb ≤ 46880 →
      PhaseGroupSpec fineCostModel (StatesFromPbEnv pb) gFromS
  intoPb_group :
    ∀ xSInto : StatesIntoPbGhost F,
      StatesPtsBoundedAt 640 xSInto.st →
      ValidV1PtsAt 640 xSInto.st.into_pb →
      rawV1State xSInto.st.into_pb ≤ 49856 →
      PhaseGroupSpec fineCostModel (StatesIntoPbEnv' xSInto) gIntoS

/-- `PhaseGroupSpec` hypothesis bundle for `<States>::recv`. -/
structure StatesRecvTightGroupSpec (F : ShaCompress)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (gRecvS : Nat) : Prop where
  recv_group :
    ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      StatesDecPtsNeededBound st0 →
      StatesPtsBoundedAt 640 st0 →
      rawV1State st0.into_pb ≤ 46880 →
      PhaseGroupSpec fineCostModel (StatesRecvEnv st0 msg) gRecvS

/-- `Ordering::Less` branch `PhaseGroupSpec` (`19,404,489` scaled units, `297` groups). -/
theorem spqrRecvOrderingLess_phaseGroupSpec_tight
    (F : ShaCompress)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB)
    (xInit : InitInnerGhost) (xInto : ChainIntoPbCall) :
    PhaseGroupSpec fineCostModel (SpqrRecvLessCallEnv F pre_pb vn xInit xInto) 19404489 := by
  have hInit := initInner_fine_phaseGroupSpec F xInit
  have hCf := chainFrom_fine_phaseGroupSpec pre_pb.chain (some vn)
  have hTailOk : PhaseGroupSpec fineCostModel
      (fun evsTail =>
        chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain ∧
          SeqEnv (ChainIntoPbEnv xInto) FreeOnlyEvs evsTail) 196608 :=
    (phaseGroupSpec_seq_freeOnly_right (chainIntoPb_fine_phaseGroupSpec xInto)).of_imp
      fun _ h => h.2
  have hActive := hInit.seq (hCf.seq (phaseGroupSpec_or_freeOnly hTailOk))
  unfold SpqrRecvLessCallEnv
  exact (phaseGroupSpec_or_freeOnly hActive).mono (by decide)

private theorem v0ChainInit_fine_phaseGroupSpec
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (xNew : ChainNewGhost) :
    PhaseGroupSpec fineCostModel (V0ChainInitEnv pre_pb vn xNew) 333513 := by
  unfold V0ChainInitEnv
  exact phaseGroupSpec_or_freeOnly
    ((chainNew_fine_phaseGroupSpec.or
      (chainFrom_fine_phaseGroupSpec pre_pb.chain (some vn))).mono (by decide))

/-- `Ordering::Greater` branch `PhaseGroupSpec` (`420,773,991` scaled units, `6,421` groups). -/
theorem spqrRecvOrderingGreater_phaseGroupSpec_tight
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {xNew : ChainNewGhost} {xRk : ChainRecvKeyGhost} {xInto : ChainIntoPbCall}
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self) :
    PhaseGroupSpec fineCostModel (SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xInto)
      420773991 := by
  have hInit := v0ChainInit_fine_phaseGroupSpec pre_pb vn xNew
  have hRk := chainRecvKey_fine_phaseGroupSpec_tight (spqrHkdfWith F) xRk
    hParams.1 hParams.2 hPrev
  have hInto := chainIntoPb_fine_phaseGroupSpec xInto
  have hEnc := phaseGroupSpec_seq_freeOnly_right
    (pqRatchetStateEncodeToVec_fine_phaseGroupSpec
      { versionNegotiation := some vn, chain := some xInto.chain.intoPb, inner := some (.v1 pb) })
  have hTailOk : PhaseGroupSpec fineCostModel
      (fun evsTail =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xInto.chain, rawKey)) ∧
          SeqEnv (ChainIntoPbEnv xInto)
            (SeqEnv
              (PqRatchetStateEncodeToVecEnv
                { versionNegotiation := some vn
                  chain := some xInto.chain.intoPb
                  inner := some (.v1 pb) })
              FreeOnlyEvs) evsTail) 393216 :=
    ((hInto.seq hEnc).of_imp fun _ h => h.2).mono (by decide)
  have hSeq := (hInit.seq (hRk.seq (phaseGroupSpec_or_freeOnly hTailOk))).of_imp
    (E₁ := fun evs => rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      SeqEnv (V0ChainInitEnv pre_pb vn xNew)
        (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk) _) evs)
    fun _ h => h.2
  unfold SpqrRecvGreaterCallEnv
  exact (phaseGroupSpec_or_freeOnly hSeq).mono (by decide)

private theorem optChainAddEpoch_fine_phaseGroupSpec
    (F : ShaCompress) (esOpt : Option EpochSecret) (xAdd : ChainAddEpochGhost) :
    PhaseGroupSpec fineCostModel (OptChainAddEpochEnv F esOpt xAdd) 333513 := by
  unfold OptChainAddEpochEnv
  cases esOpt with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some _ => exact chainAddEpoch_fine_phaseGroupSpec (spqrHkdfWith F) xAdd

theorem v1ChainAndEncode_phaseGroupSpec_tight
    (F : ShaCompress)
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {gIntoS : Nat}
    (hSIntoGrp : PhaseGroupSpec fineCostModel (StatesIntoPbEnv' xSInto) gIntoS)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self) :
    PhaseGroupSpec fineCostModel
      (V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb esOpt xAdd xRk xSInto xCInto)
      (v1ChainAndEncodeTightGroupS + gIntoS) := by
  have hCf := chainFrom_fine_phaseGroupSpec pre_pb.chain pre_pb.versionNegotiation
  have hAdd := optChainAddEpoch_fine_phaseGroupSpec F esOpt xAdd
  have hRk := chainRecvKey_fine_phaseGroupSpec_tight (spqrHkdfWith F) xRk
    hParams.1 hParams.2 hPrev
  have hC := chainIntoPb_fine_phaseGroupSpec xCInto
  have hE := phaseGroupSpec_seq_freeOnly_right
    (pqRatchetStateEncodeToVec_fine_phaseGroupSpec
      { versionNegotiation := none
        chain := some xCInto.chain.intoPb
        inner := some (.v1 xSInto.st.into_pb) })
  have hCE : PhaseGroupSpec fineCostModel _ 393216 := (hC.seq hE).mono (by decide)
  have hEncodeTail : PhaseGroupSpec fineCostModel
      (fun evs3 =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xCInto.chain, rawKey)) ∧
          SeqEnv (StatesIntoPbEnv' xSInto)
            (SeqEnv (ChainIntoPbEnv xCInto)
              (SeqEnv
                (PqRatchetStateEncodeToVecEnv
                  { versionNegotiation := none
                    chain := some xCInto.chain.intoPb
                    inner := some (.v1 xSInto.st.into_pb) })
                FreeOnlyEvs)) evs3)
      (gIntoS + 393216) :=
    (hSIntoGrp.seq hCE).of_imp fun _ h => h.2
  have hAddEvs2 := (hAdd.seq (phaseGroupSpec_or_freeOnly
    (hRk.seq (phaseGroupSpec_or_freeOnly hEncodeTail)))).of_imp
    (E₁ := fun evs1 =>
      rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
        SeqEnv (OptChainAddEpochEnv F esOpt xAdd) _ evs1)
    fun _ h => h.2.2
  have hSeq := hCf.seq (phaseGroupSpec_or_freeOnly hAddEvs2)
  have hgrp :
      333513 + (333513 + (chainRecvKeyTightGroupS + (gIntoS + 393216))) ≤
        v1ChainAndEncodeTightGroupS + gIntoS := by
    have heq : 333513 + (333513 + (chainRecvKeyTightGroupS + (gIntoS + 393216))) =
        (333513 + 333513 + chainRecvKeyTightGroupS + 393216) + gIntoS := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.add_le_add_right
      (by decide : 333513 + 333513 + chainRecvKeyTightGroupS + 393216 ≤ v1ChainAndEncodeTightGroupS)
      gIntoS
  unfold V1ChainAndEncodeTightEnv
  exact hSeq.mono hgrp

/-- `Ordering::Equal` branch `PhaseGroupSpec` (`gFromS + gRecvS + (421,107,504 + gIntoS)`). -/
theorem spqrRecvOrderingEqual_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {gDecS gFromS gIntoS gRecvS : Nat}
    (C07G : C07TightGroupSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      gDecS gFromS gIntoS)
    (C09aG : StatesRecvTightGroupSpec F StatesRecvEnv gRecvS)
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
      (SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS)) := by
  have hFrom := C07G.fromPb_group pb hv1Pts hv1Raw
  have hAfterFromOk : PhaseGroupSpec fineCostModel
      (fun evsAfterFrom =>
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
          SeqEnv (StatesRecvEnv st0 sckaMsg)
            (fun evsAfterRecv =>
              FreeOnlyEvs evsAfterRecv ∨
                (States.recv K st0 sckaMsg = .ok v ∧
                  xSInto.st = v.state ∧
                  V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                    xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)
      (gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS)) := by
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · have hpts : StatesDecPtsNeededBound st0 := StatesDecPtsNeededBound.of_from_pb hfrom
      have hpts640 : StatesPtsBoundedAt 640 st0 := statesPtsBoundedAt_of_from_pb hv1Pts hfrom
      have hst0_raw : rawV1State st0.into_pb ≤ 46880 :=
        Nat.le_trans (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom).1 hv1Raw
      have hRecv := C09aG.recv_group st0 sckaMsg hpts hpts640 hst0_raw
      have hAfterRecvOk : PhaseGroupSpec fineCostModel
          (fun evsAfterRecv =>
            States.recv K st0 sckaMsg = .ok v ∧
              xSInto.st = v.state ∧
              V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                xAdd xRk xSInto xCInto evsAfterRecv)
          (v1ChainAndEncodeTightGroupS + gIntoS) := by
        by_cases hrv : States.recv K st0 sckaMsg = .ok v ∧ xSInto.st = v.state
        · obtain ⟨hrecv_ok, hst_eq⟩ := hrv
          have hv_pts640 : StatesPtsBoundedAt 640 xSInto.st :=
            hst_eq ▸ statesPtsBoundedAt_of_recv (by decide : 576 ≤ 640) hpts640 hrecv_ok
          have hv_into_pts : ValidV1PtsAt 640 xSInto.st.into_pb :=
            validV1PtsAt_states_into_pb hv_pts640
          have hv_raw : rawV1State xSInto.st.into_pb ≤ 49856 := by
            rw [hst_eq]
            exact Nat.le_trans
              (states_recv_raw_le_2976 hpts.toStatesPtsNeededBound hrecv_ok)
              (Nat.le_trans (Nat.add_le_add_right hst0_raw 2976) (by decide))
          have hSInto := C07G.intoPb_group xSInto hv_pts640 hv_into_pts hv_raw
          exact (v1ChainAndEncode_phaseGroupSpec_tight F hSInto hParams hPrev).of_imp
            fun _ h => h.2.2
        · exact phaseGroupSpec_of_false _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrv
      exact (hRecv.seq (phaseGroupSpec_or_freeOnly hAfterRecvOk)).of_imp fun _ h => h.2
    · exact phaseGroupSpec_of_false _ fun _ h => absurd h.1 hfrom
  have hFull := phaseGroupSpec_seq_freeOnly_left
    (phaseGroupSpec_or_freeOnly (hFrom.seq (phaseGroupSpec_or_freeOnly hAfterFromOk)))
  unfold SpqrRecvEqualTightEnv
  exact hFull.mono (by simp only [Nat.add_assoc]; exact Nat.le_refl _)

private theorem validV1PtsAt640_of_validEncoderPts640_grp {stBytes : Bytes} {pre_pb : PqRatchetState}
    {pb : V1State} (hPts : ValidEncoderPts640 stBytes)
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb)) :
    ValidV1PtsAt 640 pb := by
  have hpq : ValidPqPtsAt 640 pre_pb := by
    unfold ValidEncoderPts640 SpqrTightCapsAux.ValidEncoderPtsAt at hPts
    rw [hdec] at hPts
    exact hPts
  unfold ValidPqPtsAt at hpq
  rw [hinner] at hpq
  exact hpq

/-- `PhaseGroupSpec` for `SpqrRecvTightEnv` (`gDecS + (gFromS + gRecvS + (421,107,504 + gIntoS))`, independent of `xRk.G`).
-/
theorem spqrRecvParts_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {gDecS gFromS gIntoS gRecvS : Nat}
    (C07G : C07TightGroupSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      gDecS gFromS gIntoS)
    (C09aG : StatesRecvTightGroupSpec F StatesRecvEnv gRecvS)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      (gDecS + (gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS))) := by
  have hDec := C07G.decode_group stBytes hDom.hLen hDom.hPts hDom.hChainParams
  have hAfterDecOk : PhaseGroupSpec fineCostModel
      (fun evsAfterDec =>
        spqrDecodeState stBytes = .ok pre_pb ∧
          ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
              SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
            (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
            (pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
                pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evsAfterDec)))
      (gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS)) := by
    by_cases hdec_ok : spqrDecodeState stBytes = .ok pre_pb
    · obtain ⟨_, _, hv1Raw, _, _, hPrev, hParams, _, _⟩ := hDom.hDecoded pre_pb hdec_ok
      have hLess : PhaseGroupSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
            SpqrRecvLessCallEnv F pre_pb vn xInit xCInto ev) 19404489 :=
        (spqrRecvOrderingLess_phaseGroupSpec_tight F pre_pb vn xInit xCInto).of_imp fun _ h => h.2.2
      have hGreater : PhaseGroupSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto ev) 420773991 :=
        (spqrRecvOrderingGreater_phaseGroupSpec_tight F hParams hPrev).of_imp fun _ h => h.2.2
      have hEqual : PhaseGroupSpec fineCostModel
          (fun ev => pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
              pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto ev)
          (gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS)) := by
        by_cases hE : pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingEqual_phaseGroupSpec_tight F K C07G C09aG
            (validV1PtsAt640_of_validEncoderPts640_grp hDom.hPts hdec_ok hE)
            (hv1Raw pb hE) hParams hPrev).of_imp fun _ h => h.2
        · exact phaseGroupSpec_of_false _ fun _ h => absurd h.1 hE
      have hL_le : 19404489 ≤ gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS) :=
        Nat.le_trans (by decide : 19404489 ≤ v1ChainAndEncodeTightGroupS)
          (Nat.le_trans (Nat.le_add_right v1ChainAndEncodeTightGroupS gIntoS)
            (Nat.le_add_left _ _))
      have hG_le : 420773991 ≤ gFromS + gRecvS + (v1ChainAndEncodeTightGroupS + gIntoS) :=
        Nat.le_trans (by decide : 420773991 ≤ v1ChainAndEncodeTightGroupS)
          (Nat.le_trans (Nat.le_add_right v1ChainAndEncodeTightGroupS gIntoS)
            (Nat.le_add_left _ _))
      exact ((hLess.or (hGreater.or hEqual)).of_imp fun _ h => h.2).mono
        (Nat.max_le.mpr ⟨hL_le, Nat.max_le.mpr ⟨hG_le, Nat.le_refl _⟩⟩)
    · exact phaseGroupSpec_of_false _ fun _ h => absurd h.1 hdec_ok
  unfold SpqrRecvTightEnv
  exact phaseGroupSpec_or_freeOnly (hDec.seq (phaseGroupSpec_or_freeOnly hAfterDecOk))

/-! ### Concrete Codec-Instantiated Group Specs -/

theorem decodeStateTight_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel DecodeStateTightEnv 16318464 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 83) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (decodeStateTightEnv_nonFreeCount_le h)).mono
    (by decide)

theorem decodeStateTight_fine_phaseGroupSpec_128 :
    PhaseGroupSpec fineCostModel DecodeStateTightEnv 25165824 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 128) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (decodeStateTightEnv_nonFreeCount_le_128 h)).mono
    (by decide)

theorem statesFromPbTight_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel StatesFromPbTightEnv 11010048 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 56) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (statesFromPbTightEnv_nonFreeCount_le h)).mono
    (by decide)

theorem statesFromPbTight_fine_phaseGroupSpec_128 :
    PhaseGroupSpec fineCostModel StatesFromPbTightEnv 25165824 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 128) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (statesFromPbTightEnv_nonFreeCount_le_128 h)).mono
    (by decide)

theorem statesIntoPbTight_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel StatesIntoPbTightEnv 8257536 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 42) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (statesIntoPbTightEnv_nonFreeCount_le h)).mono
    (by decide)

theorem statesIntoPbTight_fine_phaseGroupSpec_128 :
    PhaseGroupSpec fineCostModel StatesIntoPbTightEnv 25165824 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 128) fun evs h =>
    (nonFreeCount_eq_defsPlaced evs).trans_le (statesIntoPbTightEnv_nonFreeCount_le_128 h)).mono
    (by decide)

/-- Concrete `C07TightGroupSpec` at exact `(83, 56, 42)` non-free operation counts. -/
theorem c07TightGroupSpec_inst (F : ShaCompress) :
    C07TightGroupSpec F
      (fun _ : Bytes => DecodeStateTightEnv)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      16318464 11010048 8257536 :=
  ⟨fun _ _ _ _ => decodeStateTight_fine_phaseGroupSpec,
   fun _ _ _ => statesFromPbTight_fine_phaseGroupSpec,
   fun _ _ _ _ => statesIntoPbTight_fine_phaseGroupSpec⟩

theorem c07TightGroupSpec_128_inst (F : ShaCompress) :
    C07TightGroupSpec F
      (fun _ : Bytes => DecodeStateTightEnv)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      25165824 25165824 25165824 :=
  ⟨fun _ _ _ _ => decodeStateTight_fine_phaseGroupSpec_128,
   fun _ _ _ => statesFromPbTight_fine_phaseGroupSpec_128,
   fun _ _ _ _ => statesIntoPbTight_fine_phaseGroupSpec_128⟩

/-- Codec-instantiated `PhaseGroupSpec` for `SpqrRecvC07TightEnv` (`456,693,552 + gRecvS`, independent of `xRk.G`).
-/
theorem spqrRecvParts_c07_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {gRecvS : Nat}
    (C09aG : StatesRecvTightGroupSpec F StatesRecvEnv gRecvS)
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
      (456693552 + gRecvS) := by
  unfold SpqrRecvC07TightEnv
  exact (spqrRecvParts_phaseGroupSpec_tight F K (c07TightGroupSpec_inst F) C09aG
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono
    (by simp only [v1ChainAndEncodeTightGroupS]; omega)

theorem spqrRecvParts_c07_128_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {gRecvS : Nat}
    (C09aG : StatesRecvTightGroupSpec F StatesRecvEnv gRecvS)
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
      (496604976 + gRecvS) :=
  (spqrRecvParts_c07_phaseGroupSpec_tight F K C09aG
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom).mono (by omega)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
