/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Tight `fineCostModel` Leaf, Fresh-Bob `prev1`, & Zero-Skip `try_decrypt` Helpers

Auxiliary tight `fineCostModel` lemmas for `W4OuterTightSpec`:
1. `fineOptLarge` (`optLargeCost fineCostModel` mirror) and `PhaseCreditSpec.zero_live_peak_of_small`.
2. Tight `fineCostModel` bounds for `BoxAllocEnv`, `GrowOneSpeEnv 0#64`, `W4ErrTailEnv`,
   `W4SmallStoreStepEnv`, `W4SessLoadStepEnv`, `W4SessStoreStepEnv`, `PromoteStateArchiveEnv`, and
   `W4TryDecryptCloneFailEnv`.
3. Fresh-Bob `prev1` serialization (`FreshBobPrev1Dom`, `receiverChains = []`).
4. Zero-skip `<Chain>::recv_key` (`ChainRecvKeyZeroSkip`) and `12`-seed Stage P3 `try_decrypt`
   bounds.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux

set_option autoImplicit false

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain EpochSecret HkdfFn Message MlKem PqRatchetState States V1Recv V1State
   VersionNegotiationPB spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SenderChainGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule addressText keyName pathOf)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawChain rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq
   smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSessStorePollPrev1Env CliSmallStorePollEnv
   RecordSerializeCancelEnv cliStorePollPrev1_phaseCredit_tight dropClonedSessionEvents
   optLargeCost sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessLoadPoll_phaseCredit_tight sessStorePollMaxReq
   sessStorePollTightDeltaCum sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
   smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
   smallStorePollTightMaxReq smallStorePoll_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneLarge optTailCloneLen segCloneLarge segCloneMaxReq segCloneTightCum vecCloneLarge)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (serializePrev1MaxReq serializePrev1OutLarge serializePrev1Peak
   serializePrev1TightCum serializePrev1TightCum_fine_le_of_clone vecVecClone1Large
   vecVecClone1MaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
  (OptChainAddEpochEnv SpqrRecvGreaterCallEnv SpqrRecvLessCallEnv V0ChainInitEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (C07TightCreditSpec SpqrRecvC07TightEnv SpqrRecvEqualTightEnv SpqrRecvTightDomain
   SpqrRecvTightEnv StatesRecvTightCreditSpec V1ChainAndEncodeTightEnv c07TightCreditSpec_inst
   phaseCreditSpec_of_false_fine phaseCreditSpec_or_freeOnly_fine
   phaseCreditSpec_seq_freeOnly_left_fine phaseCreditSpec_seq_freeOnly_right_fine
   phaseCreditSpec_seq_zero_left_fine spqrRecvOrderingLess_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
  (chainAddEpoch_fine_phaseCreditSpec_4 chainFrom_fine_phaseCreditSpec
   chainIntoPb_fine_phaseCreditSpec_4 chainNew_fine_phaseCreditSpec chainRecvKey_links_length_eq
   nextKeyInternal_fine_phaseCreditSpec pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw (states_recv_raw_le_2976)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
  (StatesPtsBoundedAt ValidPqPtsAt ValidV1PtsAt statesPtsBoundedAt_of_from_pb
   statesPtsBoundedAt_of_recv validV1PtsAt_states_into_pb)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid
   segCloneMaxReq_le_of_dom segCloneTightCum_fine_keys_le_of_dom serialize_dom_phaseCredit_tight
   sessStorePoll_dom_phaseCredit_tight sessionClone_drop_cancel_dom_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak (DoublingChainLe)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (W2TryDecryptSeedsEnv w2TryDecryptGenSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (PromoteStateArchiveEnv phaseCredit_promoteStateArchive)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (W4ErrTailEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv W4SessLoadStepEnv W4SessStorePrev1StepEnv W4SessStoreStepEnv
   W4SmallStoreStepEnv addressText_peer_length_le_64 phaseCreditSpec_seq_freeOnly_exact
   w4SpqrInit32_phaseCredit w4SpqrInitCum)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
  (ChainRecvKeyEnv chainRecvKeyEvents keyAdvanceLoopEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (senderChainAsProtoGhost)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## Pure `Nat` `fineOptLarge` & Small-Phase Zero-Live/Peak Upgrade -/

/-- Pure `Nat` mirror of `optLargeCost fineCostModel` (`0` for `req ≤ 135,167`, `req + 8,195`
otherwise), avoiding `AllocCostModel` reduction overhead in kernel `(by decide)`. -/
def fineOptLarge (req : Nat) : Nat :=
  if req ≤ 135167 then 0 else req + 8195

theorem optLargeCost_fine_eq (req : Nat) :
    optLargeCost fineCostModel req = fineOptLarge req := by
  unfold optLargeCost fineOptLarge
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]

theorem fineOptLarge_of_le {req : Nat} (h : req ≤ 135167) :
    fineOptLarge req = 0 := by
  unfold fineOptLarge
  simp [h]

theorem fineOptLarge_mono {a b : Nat} (h : a ≤ b) :
    fineOptLarge a ≤ fineOptLarge b := by
  unfold fineOptLarge
  split
  · exact Nat.zero_le _
  · next ha =>
    have hb : ¬ (b ≤ 135167) := fun hle => ha (Nat.le_trans h hle)
    simp only [hb, ↓reduceIte]
    exact Nat.add_le_add_right h 8195

private theorem step_small_live_peak_nonInc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ev : AllocEvent) (st : M.σ)
    (hreq : eventStepReq ev ≤ HasFineReallocCredit.smallMaxReq M)
    (hal : eventStepAlign ev ≤ 16) :
    HasFineReallocCredit.liveLarge (M.step ev st) ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge (M.step ev st) ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    exact (hM.freeNonInc al sz st).2
  | alloc req =>
    simp only [eventStepReq] at hreq
    exact (hM.step_alloc_small_any st hreq).2
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    exact (hM.step_aligned_small_any st hal hreq).2
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    by_cases hold : old ≤ HasFineReallocCredit.smallMaxReq M
    · exact (hM.step_realloc_small_small_any st hal hold hreq).2
    · have hgt : HasFineReallocCredit.smallMaxReq M < old := Nat.lt_of_not_ge hold
      obtain ⟨_, hl, hp⟩ := hM.step_realloc_large_small_any st hal hgt hreq
      exact ⟨Nat.le_trans hl (Nat.sub_le _ _), hp⟩

private theorem stepEvents_small_live_peak_nonInc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ HasFineReallocCredit.smallMaxReq M ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | ev :: rest, st, hall => by
    have hhead := hall ev List.mem_cons_self
    have ⟨hl1, hp1⟩ := step_small_live_peak_nonInc hM ev st hhead.1 hhead.2
    have ⟨hl2, hp2⟩ := stepEvents_small_live_peak_nonInc hM rest (M.step ev st)
      (fun e he => hall e (List.mem_cons_of_mem ev he))
    rw [AllocCostModel.stepEvents_cons]
    exact ⟨Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩

/-- Generic small-regime upgrade: whenever `r ≤ smallMaxReq M`, every event in `Env` stays in
`sc < 48` (or shrinks `sc = 63 → sc < 48`), giving `Δlive = 0` and `Δpeak = 0`. -/
theorem PhaseCreditSpec.zero_live_peak_of_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {Env : List AllocEvent → Prop} {c l p r : Nat}
    (hr : r ≤ HasFineReallocCredit.smallMaxReq M)
    (h : PhaseCreditSpec M Env c l p r) :
    PhaseCreditSpec M Env c 0 0 r where
  req_align := h.req_align
  credit_le st0 {evs} hE := by
    have hc := (h.credit_le st0 hE).1
    have hall : ∀ ev ∈ evs,
        eventStepReq ev ≤ HasFineReallocCredit.smallMaxReq M ∧ eventStepAlign ev ≤ 16 := by
      intro ev hev
      obtain ⟨hreq, hal⟩ := h.req_align evs hE ev hev
      exact ⟨Nat.le_trans hreq hr, hal⟩
    obtain ⟨hl, hp⟩ := stepEvents_small_live_peak_nonInc hM evs st0 hall
    simp only [Nat.add_zero]
    exact ⟨hc, hl, Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-- Tight `fineCostModel` bound for `InitialStateEnv F x_spqr` (`x_spqr.p.authKey.length ≤ 32`):
`maxReq = 4,224 ≤ 135,167`, giving `Δlive = 0` and `Δpeak = 0`. -/
theorem w4SpqrInit32_fine_phaseCredit (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hkey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec fineCostModel (InitialStateEnv F x_spqr)
      (w4SpqrInitCum 32) 0 0 4224 :=
  PhaseCreditSpec.zero_live_peak_of_small fineCostModel_modelHyps
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    (w4SpqrInit32_phaseCredit fineCostModel_modelHyps F x_spqr hkey)

/-! ## Tight `fineCostModel` Boxed Store Steps, `GrowOneSpeEnv`, & `RecordSerialize` Helpers -/

theorem boxAllocEnv_fine_le_28 {boxSz : Nat} (hsz : boxSz ≤ 28) :
    PhaseCreditSpec fineCostModel (BoxAllocEnv boxSz) 488 0 0 boxSz := by
  have h1 : PhaseCreditSpec fineCostModel (fun evs => boxSz = 0 ∧ evs = []) 0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil (M := fineCostModel) (fun _ h => h.2)
  have hsm : boxSz ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have h2 : PhaseCreditSpec fineCostModel
      (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8) 488 0 0 boxSz :=
    (PhaseCreditSpec.of_imp (fun _ h => h.2)
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := boxSz) (al := 8) (by decide) hsm)).mono
      (smallAllocCost_le_488_of_le_28 hsz) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl boxSz)
  exact (PhaseCreditSpec.or_of_imp (fun _ h => h) h1 h2).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 488, Nat.le_refl 488⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le boxSz, Nat.le_refl boxSz⟩)

theorem boxAllocEnv_fine_le_44 {boxSz : Nat} (hsz : boxSz ≤ 44) :
    PhaseCreditSpec fineCostModel (BoxAllocEnv boxSz) 738 0 0 boxSz := by
  have h1 : PhaseCreditSpec fineCostModel (fun evs => boxSz = 0 ∧ evs = []) 0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil (M := fineCostModel) (fun _ h => h.2)
  have hsm : boxSz ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; omega
  have h2 : PhaseCreditSpec fineCostModel
      (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8) 738 0 0 boxSz :=
    (PhaseCreditSpec.of_imp (fun _ h => h.2)
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := boxSz) (al := 8) (by decide) hsm)).mono
      (smallAllocCost_le_738_of_le_44 hsz) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl boxSz)
  exact (PhaseCreditSpec.or_of_imp (fun _ h => h) h1 h2).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 738, Nat.le_refl 738⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le boxSz, Nat.le_refl boxSz⟩)

theorem w4BoxedStoreStep_fine_le_28 {boxSz : Nat} (hsz : boxSz ≤ 28)
    {E_poll : List AllocEvent → Prop} {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec fineCostModel E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (W4BoxedStoreStepEnv boxSz E_poll)
      (488 + c_p) l_p p_p (max boxSz r_p) := by
  have hbox := boxAllocEnv_fine_le_28 hsz
  have hpollF := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hpoll
  exact (hbox.seq hpollF).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

theorem w4BoxedStoreStep_fine_le_44 {boxSz : Nat} (hsz : boxSz ≤ 44)
    {E_poll : List AllocEvent → Prop} {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec fineCostModel E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (W4BoxedStoreStepEnv boxSz E_poll)
      (738 + c_p) l_p p_p (max boxSz r_p) := by
  have hbox := boxAllocEnv_fine_le_44 hsz
  have hpollF := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hpoll
  exact (hbox.seq hpollF).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

theorem growOneSpeZero_fine_phaseCredit_tight :
    PhaseCreditSpec fineCostModel (GrowOneSpeEnv 0#64) 8186 0 0 192 := by
  have hsm : 192 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha := PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 192) (al := 8) (by decide) hsm
  have hc : HasFineReallocCredit.smallAllocCost fineCostModel 192 ≤ 8186 := by
    change fineSmallAllocCost 192 ≤ 8186
    decide
  refine ha.congr_mono ?_ hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  rintro evs (⟨_, h1⟩ | ⟨hne, _⟩)
  · exact h1
  · exact absurd rfl hne

theorem w4ErrTail_fine_phaseCredit_tight :
    PhaseCreditSpec fineCostModel W4ErrTailEnv 8186 0 0 192 := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hSpe : PhaseCreditSpec fineCostModel (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs)
      8186 0 0 192 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      growOneSpeZero_fine_phaseCredit_tight
  exact (hFree.or hSpe).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 8186, Nat.le_refl 8186⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le 192, Nat.le_refl 192⟩)

theorem w4SmallStoreStep16_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (W4SmallStoreStepEnv 16 rd files dir name)
      (488 + smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (max 16 (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries)) :=
  w4BoxedStoreStep_fine_le_28 (by decide)
    (smallStorePoll_phaseCredit_tight hdc hdir hname hcap)

theorem w4SmallStoreStep32_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (W4SmallStoreStepEnv 32 rd files dir name)
      (738 + smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (max 32 (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries)) :=
  w4BoxedStoreStep_fine_le_44 (by decide)
    (smallStorePoll_phaseCredit_tight hdc hdir hname hcap)

theorem w4PeerSmallStoreStep32_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles} {peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel
      (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (738 + smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (max 32 (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries)) :=
  w4SmallStoreStep32_fine_phaseCredit hdc hdir (addressText_peer_length_le_64 hpeer) hcap

theorem w4KeyIdSmallStoreStep16_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} (id : BitVec 32)
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path (keyName id)) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (W4SmallStoreStepEnv 16 rd files dir (keyName id))
      (488 + smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (max 16 (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries)) :=
  w4SmallStoreStep16_fine_phaseCredit hdc hdir
    (Nat.le_trans (keyName_length_le id) (by decide)) hcap

theorem w4SessLoadStep_fine_phaseCredit
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal sessFileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessFileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (W4SessLoadStepEnv rd DeserEnv files sessDir peer)
      (488 + sessLoadPollTightDeltaCum (max maxVal sessFileCap) deserCum)
      (sessLoadPollTightDeltaLive (max maxVal sessFileCap) deserLive)
      (sessLoadPollTightDeltaPeak (max maxVal sessFileCap) deserPeak)
      (max 24 (sessLoadPollTightMaxReq (max maxVal sessFileCap) deserMaxReq)) :=
  w4BoxedStoreStep_fine_le_28 (by decide)
    (sessLoadPoll_phaseCredit_tight hdc hdir hpeer hcap hdeser)

theorem w4SessStoreStep_dom_fine_phaseCredit
    {sessDir : DirGhost} {peer : AddrGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal pqCap encCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    PhaseCreditSpec fineCostModel (W4SessStoreStepEnv sessDir peer g_rec r_rec)
      (738 + sessStorePollTightDeltaCum 8420940 maxEntries)
      (sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries)
      (sessStorePollTightDeltaPeak
        (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries)
      (max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)) := by
  have hpoll := sessStorePoll_dom_phaseCredit_tight hdc hpeer hValid hEnc
  rw [optLargeCost_fine_eq pqCap, optLargeCost_fine_eq encCap] at hpoll
  exact w4BoxedStoreStep_fine_le_44 (by decide) hpoll

theorem promoteStateArchive_dom_fine_phaseCredit_tight
    {pqCap encCap c_push r_push : Nat}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    (hValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_arch).length ≤ encCap)
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec fineCostModel
      (PromoteStateArchiveEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv)
      (8420940 + c_push)
      (fineOptLarge encCap)
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap)
      (max (max (max 208000 pqCap) encCap) r_push) := by
  have hSer := serialize_dom_phaseCredit_tight hValid hEnc
  rw [optLargeCost_fine_eq pqCap, optLargeCost_fine_eq encCap] at hSer
  have hProm := phaseCredit_promoteStateArchive fineCostModel_modelHyps hSer hPush
  have hle : fineOptLarge encCap ≤ 1080975 + fineOptLarge pqCap + fineOptLarge encCap :=
    Nat.le_add_left _ _
  exact hProm.mono
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.le_refl _, hle⟩)
    (Nat.le_refl _)

theorem tryDecryptCloneFail_dom_fine_cancel_phaseCredit
    {curPqCap c_cur p_cur r_cur : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur) :
    PhaseCreditSpec fineCostModel
      (W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur))
      (8277456 + c_cur + 8186)
      0
      (1080975 + fineOptLarge curPqCap + p_cur)
      (max (max (max 208000 curPqCap) r_cur) 192) := by
  rcases hCurDom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
  · refine (PhaseCreditSpec.empty fineCostModel).congr_mono ?_
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    intro evs hE
    rcases hE with h1 | ⟨a, _, _, h1, _⟩
    · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
      exact hNo e2 htf
    · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
      exact hNo e2 htf
  · subst hst_eq
    have hCancel := sessionClone_drop_cancel_dom_phaseCredit_tight hgv hdom hCurTrial
    rw [optLargeCost_fine_eq curPqCap] at hCancel
    have hSpe := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      growOneSpeZero_fine_phaseCredit_tight
    exact (hCancel.seq hSpe).mono
      (Nat.le_refl _)
      (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
      (Nat.le_refl _)

/-! ## Fresh-Bob `prev1` Serialization (`FreshBobPrev1Dom`, `0` Receiver Chains) -/

/-- Domain bundle for Path C `prev1` output `sess_out1` on a fresh Bob session with
`receiverChains = []`, `SessionGhostValid G ses`, `SessionCloneDom bobPqCap ses`,
`enc.length ≤ prevEncCap`, and `(encodeRecordPrev1Mem G ses enc).length ≤ totalPrev1Cap`. -/
structure FreshBobPrev1Dom (bobPqCap prevEncCap totalPrev1Cap : Nat)
    (G : SessionGhost) (ses : Session (List (BitVec 8))) (enc : List (BitVec 8)) : Prop where
  rc_nil : ses.state.receiverChains = []
  gv : SessionGhostValid G ses
  dom : SessionCloneDom bobPqCap ses
  prev_len : enc.length ≤ prevEncCap
  total_len : (encodeRecordPrev1Mem G ses enc).length ≤ totalPrev1Cap

private theorem vecCloneLarge_fine_of_le {n : Nat} (h : n ≤ 135167) :
    vecCloneLarge fineCostModel n = 0 := by
  unfold vecCloneLarge
  split
  · rfl
  · rw [optLargeCost_fine_eq]
    exact fineOptLarge_of_le h

private theorem senderChainLarge_fine_eq_zero {gs : SenderChainGhost}
    {sc : CryptoGames.LibsignalSession.SenderChain}
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneLarge fineCostModel (senderChainAsProtoGhost gs sc) = 0 := by
  unfold chainCloneLarge senderChainAsProtoGhost
  dsimp only
  rw [vecCloneLarge_fine_of_le (by omega),
      vecCloneLarge_fine_of_le (by omega),
      optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)]
  rfl

theorem segCloneTightCum_fine_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    segCloneTightCum fineCostModel G ses.state ≤ 897456 := by
  have hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ 0 := by
    rw [hbob.rc_nil, List.zip_nil_right]
    exact Nat.le_refl 0
  exact segCloneTightCum_fine_keys_le_of_dom hbob.gv hbob.dom hkeys

theorem segCloneLarge_fine_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    segCloneLarge fineCostModel G ses.state ≤ fineOptLarge bobPqCap := by
  obtain ⟨hloc_len, hrem_len, _, _, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid hbob.gv
  have hdom := hbob.dom
  unfold segCloneLarge
  have hloc : vecCloneLarge fineCostModel G.localIk.bytes.length = 0 :=
    vecCloneLarge_fine_of_le (by omega)
  have hrem : vecCloneLarge fineCostModel G.remoteIk.bytes.length = 0 :=
    vecCloneLarge_fine_of_le (by omega)
  have hroot : optLargeCost fineCostModel 32 = 0 := by
    rw [optLargeCost_fine_eq]; exact fineOptLarge_of_le (by decide)
  have hpend : vecCloneLarge fineCostModel (optTailCloneLen G.pending) = 0 :=
    vecCloneLarge_fine_of_le (by omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hdom.kyber_cap k hk
  have hkyb : vecCloneLarge fineCostModel (optTailCloneLen G.kyber) = 0 :=
    vecCloneLarge_fine_of_le (Nat.le_trans hkyb_le (by decide))
  have halice : vecCloneLarge fineCostModel G.alice.bytes.length = 0 :=
    vecCloneLarge_fine_of_le (by rw [halice_eq]; exact Nat.le_trans hdom.alice_len (by decide))
  have hpq : vecCloneLarge fineCostModel ses.state.pqRatchetState.length ≤
      fineOptLarge bobPqCap := by
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · rw [optLargeCost_fine_eq]
      exact fineOptLarge_mono hdom.pq_len
  rw [hbob.rc_nil]
  simp only [↓reduceIte, hloc, hrem, hroot, hpend, hkyb, halice]
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]
    simpa only [Nat.zero_add, Nat.add_zero] using hpq
  · rw [h1, h2]
    dsimp only
    rw [senderChainLarge_fine_eq_zero hsrk hpriv]
    simpa only [Nat.zero_add, Nat.add_zero] using hpq

theorem serializePrev1TightCum_fine_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1TightCum fineCostModel G ses enc ≤ 1184912 :=
  Nat.le_trans
    (serializePrev1TightCum_fine_le_of_clone (segCloneTightCum_fine_freshBob_le hbob))
    (by decide)

theorem serializePrev1OutLarge_fine_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1OutLarge fineCostModel G ses enc ≤ fineOptLarge totalPrev1Cap := by
  unfold serializePrev1OutLarge
  rw [optLargeCost_fine_eq]
  exact fineOptLarge_mono hbob.total_len

theorem serializePrev1Peak_fine_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1Peak fineCostModel G ses enc ≤
      fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap := by
  unfold serializePrev1Peak
  have hcl := segCloneLarge_fine_freshBob_le hbob
  have hvv : vecVecClone1Large fineCostModel enc ≤ fineOptLarge prevEncCap := by
    unfold vecVecClone1Large
    rw [optLargeCost_fine_eq 24, fineOptLarge_of_le (by decide), Nat.zero_add]
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · rw [optLargeCost_fine_eq]
      exact fineOptLarge_mono hbob.prev_len
  have hout : optLargeCost fineCostModel (encodeRecordPrev1Mem G ses enc).length ≤
      fineOptLarge totalPrev1Cap := by
    rw [optLargeCost_fine_eq]
    exact fineOptLarge_mono hbob.total_len
  exact Nat.add_le_add (Nat.add_le_add hcl hvv) hout

theorem serializePrev1MaxReq_freshBob_le
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1MaxReq G ses enc ≤
      max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap) := by
  unfold serializePrev1MaxReq vecVecClone1MaxReq
  have hcl := segCloneMaxReq_le_of_dom hbob.gv hbob.dom
  have hvv : max 24 enc.length ≤ max 24 prevEncCap :=
    Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hbob.prev_len (Nat.le_max_right _ _)⟩
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.le_trans hcl (Nat.le_max_left _ _),
       Nat.le_trans hvv (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))⟩,
     Nat.le_trans hbob.total_len (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩

theorem w4SessStorePrev1Step_freshBob_fine_phaseCredit
    {sessDir : DirGhost} {peer : AddrGhost}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {maxDir maxEntries maxVal bobPqCap prevEncCap totalPrev1Cap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G sess enc) :
    PhaseCreditSpec fineCostModel (W4SessStorePrev1StepEnv sessDir peer G sess enc)
      (738 + sessStorePollTightDeltaCum 1184912 maxEntries)
      (sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries)
      (sessStorePollTightDeltaPeak
        (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries)
      (max 32
        (sessStorePollMaxReq
          (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)) := by
  have hpoll := (cliStorePollPrev1_phaseCredit_tight hdc hpeer).mono
    (Nat.add_le_add_right
      (Nat.add_le_add_left (serializePrev1TightCum_fine_freshBob_le hbob) 9789) _)
    (Nat.add_le_add_right (serializePrev1OutLarge_fine_freshBob_le hbob) _)
    (Nat.add_le_add_right (serializePrev1Peak_fine_freshBob_le hbob) _)
    (Nat.max_le.mpr
      ⟨Nat.le_trans (serializePrev1MaxReq_freshBob_le hbob) (Nat.le_max_left _ _),
       Nat.le_max_right _ _⟩)
  exact w4BoxedStoreStep_fine_le_44 (by decide) hpoll

/-! ## Zero-Skip `<Chain>::recv_key` & Bob `12`-Seed Stage P3 `try_decrypt` -/

/-- Fresh-responder / `0`-skip invariant for `<spqr::chain::Chain>::recv_key`: on the first
handshake message (`index ≤ ctr + 1`), `keyAdvanceLoop` performs `0` skipped-key iterations. -/
def ChainRecvKeyZeroSkip (x : ChainRecvKeyGhost) : Prop :=
  ∀ epochIndex (h : epochIndex < x.self.links.length),
    x.index.toNat ≤ (x.self.links[epochIndex]'h).recv.ctr.toNat + 1

private theorem keyAdvanceLoopEvents_eq_nil_of_le_one
    (hkdf : HkdfFn) (params : CryptoVerification.LibsignalSpqrV1.ChainParamsPB)
    (atIdx : BitVec 32) (rem : Nat)
    (ced : CryptoVerification.LibsignalSpqrV1.ChainEpochDirection) (cap : Nat)
    (hrem : rem ≤ 1) (hidx : atIdx.toNat ≤ ced.ctr.toNat + 1) :
    keyAdvanceLoopEvents hkdf params atIdx rem ced cap = [] := by
  cases rem with
  | zero => rfl
  | succ r =>
    have hr0 : r = 0 := by omega
    subst hr0
    unfold keyAdvanceLoopEvents
    have hnot : ¬ (ced.ctr.toNat + 1 < atIdx.toNat) := by omega
    simp [hnot]

/-- Under `ChainRecvKeyZeroSkip x`, `<Chain>::recv_key` emits `[]`, `rustAllocEvents 32 1`, or
`nextKeyInternalEvents ++ rustAllocEvents 32 1`, costing at most `(1476, 0, 0, 35)`. -/
theorem chainRecvKey_zeroSkip_fine_phaseCreditSpec_tight
    (hkdf : HkdfFn) (x : ChainRecvKeyGhost) (hZero : ChainRecvKeyZeroSkip x) :
    PhaseCreditSpec fineCostModel (ChainRecvKeyEnv hkdf x) 1476 0 0 35 := by
  have hsm32 : 32 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha32 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 32 1) 738 0 0 32 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 32) (al := 1) (by decide) hsm32).mono
      (smallAllocCost_le_738_of_le_44 (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  have hnk : PhaseCreditSpec fineCostModel (· = nextKeyInternalEvents) 738 0 0 35 :=
    nextKeyInternal_fine_phaseCreditSpec
  have hboth : PhaseCreditSpec fineCostModel
      (· = nextKeyInternalEvents ++ rustAllocEvents 32 1) 1476 0 0 35 :=
    ((hnk.concat ha32).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have htri : chainRecvKeyEvents hkdf x = [] ∨
      chainRecvKeyEvents hkdf x = rustAllocEvents 32 1 ∨
      chainRecvKeyEvents hkdf x = nextKeyInternalEvents ++ rustAllocEvents 32 1 := by
    unfold chainRecvKeyEvents
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next epochIndex _ =>
        split
        · next hlt =>
          have hbound := hZero epochIndex hlt
          dsimp only
          split
          · split
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl
          · split
            · exact Or.inl rfl
            · split
              · exact Or.inl rfl
              · split
                · exact Or.inl rfl
                · set maxOoo := x.self.params.maxOooKeysOrDefault
                  set link := x.self.links[epochIndex]'hlt
                  set self0 :=
                    if x.index > link.recv.ctr + maxOoo then
                      { link.recv with prev := link.recv.prev.clear }
                    else link.recv
                  have hctr : self0.ctr = link.recv.ctr := by
                    dsimp [self0]; split <;> rfl
                  have hidx0 : x.index.toNat ≤ self0.ctr.toNat + 1 := by
                    rw [hctr]; exact hbound
                  have hrem1 : x.index.toNat - self0.ctr.toNat ≤ 1 := by omega
                  rw [keyAdvanceLoopEvents_eq_nil_of_le_one hkdf x.self.params x.index
                        (x.index.toNat - self0.ctr.toNat) self0 _ hrem1 hidx0,
                      List.nil_append]
                  exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
  rcases htri with hnil | ha | hb
  · exact (PhaseCreditSpec.of_eq_nil (M := fineCostModel)
      (fun _ h => h.trans hnil)).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · exact (ha32.of_imp (fun _ h => h.trans ha)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  · exact hboth.of_imp (fun _ h => h.trans hb)

private theorem v0ChainInit_fine_phaseCreditSpec
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (xNew : ChainNewGhost) :
    PhaseCreditSpec fineCostModel (V0ChainInitEnv pre_pb vn xNew) 16643 0 0 448 := by
  unfold V0ChainInitEnv
  exact phaseCreditSpec_or_freeOnly_fine
    ((chainNew_fine_phaseCreditSpec.or
      (chainFrom_fine_phaseCreditSpec pre_pb.chain (some vn))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide))

theorem spqrRecvOrderingGreater_zeroSkip_phaseCreditSpec_tight
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {xNew : ChainNewGhost} {xRk : ChainRecvKeyGhost} {xInto : ChainIntoPbCall}
    (hZero : ChainRecvKeyZeroSkip xRk)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := some vn, chain := some c.intoPb, inner := some (.v1 pb) } ≤
          spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel (SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xInto)
      190086 294391 294391 286196 := by
  have hInit := v0ChainInit_fine_phaseCreditSpec pre_pb vn xNew
  have hRk := chainRecvKey_zeroSkip_fine_phaseCreditSpec_tight (spqrHkdfWith F) xRk hZero
  have hTailOk : PhaseCreditSpec fineCostModel
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
      171967 294391 294391 286196 := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hInto := chainIntoPb_fine_phaseCreditSpec_4 xInto hlen4
      have hEnc := phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := some vn, chain := some xInto.chain.intoPb, inner := some (.v1 pb) }
          (hOutCap xInto.chain ⟨rawKey, hrk⟩))
      exact ((phaseCreditSpec_seq_zero_left_fine hInto hEnc).of_imp fun _ h => h.2).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hTail := phaseCreditSpec_or_freeOnly_fine hTailOk
  have hRkTail : PhaseCreditSpec fineCostModel _ 173443 294391 294391 286196 :=
    (phaseCreditSpec_seq_zero_left_fine hRk hTail).mono
      (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)
  have hSeq := (phaseCreditSpec_seq_zero_left_fine hInit hRkTail).of_imp
    (E₁ := fun evs => rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      SeqEnv (V0ChainInitEnv pre_pb vn xNew)
        (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk) _) evs)
    fun _ h => h.2
  unfold SpqrRecvGreaterCallEnv
  exact (phaseCreditSpec_or_freeOnly_fine hSeq).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem optChainAddEpoch_fine_4_local
    (F : ShaCompress) (esOpt : Option EpochSecret) (xAdd : ChainAddEpochGhost)
    (hlen : xAdd.self.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (OptChainAddEpochEnv F esOpt xAdd) 17539 0 0 896 := by
  unfold OptChainAddEpochEnv
  cases esOpt with
  | none =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some _ =>
    exact chainAddEpoch_fine_phaseCreditSpec_4 (spqrHkdfWith F) xAdd hlen

theorem v1ChainAndEncode_zeroSkip_phaseCreditSpec_tight
    (F : ShaCompress)
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {cInto rInto : Nat}
    (hSIntoSpec : PhaseCreditSpec fineCostModel (StatesIntoPbEnv' xSInto) cInto 0 0 rInto)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hZero : ChainRecvKeyZeroSkip xRk)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 xSInto.st.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb esOpt xAdd xRk xSInto xCInto)
      (207625 + cInto) 294391 294391 (max 286196 rInto) := by
  have hCf := chainFrom_fine_phaseCreditSpec pre_pb.chain pre_pb.versionNegotiation
  have hAdd := optChainAddEpoch_fine_4_local F esOpt xAdd hAddLinks
  have hRk := chainRecvKey_zeroSkip_fine_phaseCreditSpec_tight (spqrHkdfWith F) xRk hZero
  have hEncodeTail : PhaseCreditSpec fineCostModel
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
      (cInto + 171967) 294391 294391 (max rInto 286196) := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xCInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xCInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hC := chainIntoPb_fine_phaseCreditSpec_4 xCInto hlen4
      have hE := SpqrRecvTightBranches.phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := none
            chain := some xCInto.chain.intoPb
            inner := some (.v1 xSInto.st.into_pb) }
          (hOutCap xCInto.chain ⟨rawKey, hrk⟩))
      have hCE : PhaseCreditSpec fineCostModel _ 171967 294391 294391 286196 :=
        (phaseCreditSpec_seq_zero_left_fine hC hE).mono
          (by decide) (by decide) (by decide) (by decide)
      exact (phaseCreditSpec_seq_zero_left_fine hSIntoSpec hCE).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hEvs3 := phaseCreditSpec_or_freeOnly_fine hEncodeTail
  have hRkTail : PhaseCreditSpec fineCostModel _
      (1476 + (cInto + 171967)) 294391 294391 (max 286196 rInto) :=
    (phaseCreditSpec_seq_zero_left_fine hRk hEvs3).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.max_le.mpr ⟨Nat.le_trans (by decide : 35 ≤ 286196) (Nat.le_max_left 286196 rInto),
        Nat.max_le.mpr ⟨Nat.le_max_right 286196 rInto, Nat.le_max_left 286196 rInto⟩⟩)
  have hEvs2 := phaseCreditSpec_or_freeOnly_fine hRkTail
  have hAddEvs2 := (phaseCreditSpec_seq_zero_left_fine hAdd hEvs2).of_imp
    (E₁ := fun evs1 =>
      rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
        SeqEnv (OptChainAddEpochEnv F esOpt xAdd) _ evs1)
    fun _ h => h.2.2
  have hSeq := phaseCreditSpec_seq_zero_left_fine hCf (phaseCreditSpec_or_freeOnly_fine hAddEvs2)
  have hcum : 16643 + (17539 + (1476 + (cInto + 171967))) ≤ 207625 + cInto := by
    have heq : 16643 + (17539 + (1476 + (cInto + 171967))) =
        (16643 + 17539 + 1476 + 171967) + cInto := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.add_le_add_right
      (by decide : 16643 + 17539 + 1476 + 171967 ≤ 207625) cInto
  have hreq : max 448 (max 896 (max 286196 rInto)) ≤ max 286196 rInto :=
    Nat.max_le.mpr ⟨Nat.le_trans (by decide : 448 ≤ 286196) (Nat.le_max_left _ _),
      Nat.max_le.mpr ⟨Nat.le_trans (by decide : 896 ≤ 286196) (Nat.le_max_left _ _),
        Nat.le_refl _⟩⟩
  unfold V1ChainAndEncodeTightEnv
  exact hSeq.mono hcum (Nat.le_refl _) (Nat.le_refl _) hreq

theorem spqrRecvOrderingEqual_zeroSkip_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hv1Pts : ValidV1PtsAt 640 pb)
    (hv1Raw : rawV1State pb ≤ 46880)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hZero : ChainRecvKeyZeroSkip xRk)
    (hOutCap : ∀ c : Chain,
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 v.state.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto)
      (cFrom + cRecv + (207625 + cInto)) 294391 294391
      (max rFrom (max rRecv (max 286196 rInto))) := by
  have hFrom := C07.fromPb_spec pb hv1Pts hv1Raw
  have hAfterFromOk : PhaseCreditSpec fineCostModel
      (fun evsAfterFrom =>
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
          SeqEnv (StatesRecvEnv st0 sckaMsg)
            (fun evsAfterRecv =>
              FreeOnlyEvs evsAfterRecv ∨
                (States.recv K st0 sckaMsg = .ok v ∧
                  xSInto.st = v.state ∧
                  V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                    xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)
      (cRecv + (207625 + cInto)) 294391 294391 (max rRecv (max 286196 rInto)) := by
    by_cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0
    · have hpts : StatesDecPtsNeededBound st0 := StatesDecPtsNeededBound.of_from_pb hfrom
      have hpts640 : StatesPtsBoundedAt 640 st0 := statesPtsBoundedAt_of_from_pb hv1Pts hfrom
      have hst0_raw : rawV1State st0.into_pb ≤ 46880 :=
        Nat.le_trans (CryptoVerification.SpqrV1.Top.StateSize.States.from_pb_raw_le hfrom).1 hv1Raw
      have hRecv := C09a.recv_spec st0 sckaMsg hpts hpts640 hst0_raw
      have hAfterRecvOk : PhaseCreditSpec fineCostModel
          (fun evsAfterRecv =>
            States.recv K st0 sckaMsg = .ok v ∧
              xSInto.st = v.state ∧
              V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                xAdd xRk xSInto xCInto evsAfterRecv)
          (207625 + cInto) 294391 294391 (max 286196 rInto) := by
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
          have hSInto := C07.intoPb_spec xSInto hv_pts640 hv_into_pts hv_raw
          exact (v1ChainAndEncode_zeroSkip_phaseCreditSpec_tight F hSInto hAddLinks hRkLinks
            hZero (fun c hc => hst_eq.symm ▸ hOutCap c hfrom hrecv_ok hc)).of_imp
            fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hrv
      have hAfterRecv := phaseCreditSpec_or_freeOnly_fine hAfterRecvOk
      exact (phaseCreditSpec_seq_zero_left_fine hRecv hAfterRecv).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hfrom
  have hAfterFrom := phaseCreditSpec_or_freeOnly_fine hAfterFromOk
  have hAfterMd := phaseCreditSpec_or_freeOnly_fine
    (phaseCreditSpec_seq_zero_left_fine hFrom hAfterFrom)
  have hFull := phaseCreditSpec_seq_freeOnly_left_fine hAfterMd
  unfold SpqrRecvEqualTightEnv
  exact hFull.mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

private theorem validV1PtsAt640_local {stBytes : Bytes} {pre_pb : PqRatchetState}
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

theorem spqrRecvParts_zeroSkip_phaseCreditSpec_tight_of_caps
    (F : ShaCompress) (K : MlKem)
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cInto rInto cRecv rRecv : Nat}
    (C07 : C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv'
      cDec rDec cFrom rFrom cInto rInto)
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hZero : ChainRecvKeyZeroSkip xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      (cDec + max 1348326 (cFrom + cRecv + (207625 + cInto)))
      294391 294391
      (max rDec (max rFrom (max rRecv (max 286196 rInto)))) := by
  have hDec := C07.decode_spec stBytes hDom.hLen hDom.hPts hDom.hChainParams
  have hAfterDecOk : PhaseCreditSpec fineCostModel
      (fun evsAfterDec =>
        spqrDecodeState stBytes = .ok pre_pb ∧
          ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
              SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
            (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
            (pre_pb.inner = some (.v1 pb) ∧
              SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
                pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evsAfterDec)))
      (max 1348326 (cFrom + cRecv + (207625 + cInto)))
      294391 294391
      (max rFrom (max rRecv (max 286196 rInto))) := by
    by_cases hdec_ok : spqrDecodeState stBytes = .ok pre_pb
    · obtain ⟨hvn32, hcLinks, hv1Raw, hAddL, hRkL, _, _, hOutG, hOutE⟩ :=
        hDom.hDecoded pre_pb hdec_ok
      have hLess : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
            SpqrRecvLessCallEnv F pre_pb vn xInit xCInto ev)
          1348326 0 0 2112 := by
        by_cases hL : pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey
        · exact (spqrRecvOrderingLess_phaseCreditSpec_tight F hL.2 (hvn32 vn hL.1)
            hcLinks).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hL
      have hGreater : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto ev)
          190086 294391 294391 286196 := by
        by_cases hG : pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingGreater_zeroSkip_phaseCreditSpec_tight F hZero hRkL
            (fun c hc => hOutG vn pb c hG.1 hG.2 hc)).of_imp fun _ h => h.2.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd ⟨h.1, h.2.1⟩ hG
      have hEqual : PhaseCreditSpec fineCostModel
          (fun ev => pre_pb.inner = some (.v1 pb) ∧
            SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
              pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto ev)
          (cFrom + cRecv + (207625 + cInto)) 294391 294391
          (max rFrom (max rRecv (max 286196 rInto))) := by
        by_cases hE : pre_pb.inner = some (.v1 pb)
        · exact (spqrRecvOrderingEqual_zeroSkip_phaseCreditSpec_tight F K C07 C09a
            (validV1PtsAt640_local hDom.hPts hdec_ok hE)
            (hv1Raw pb hE) hAddL hRkL hZero
            (fun c hfrom hrecv hc => hOutE pb st0 sckaMsg v c hE hfrom hrecv hc)).of_imp
            fun _ h => h.2
        · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hE
      have hOr := hLess.or (hGreater.or hEqual)
      have hG_le : 190086 ≤ max 1348326 (cFrom + cRecv + (207625 + cInto)) :=
        Nat.le_trans (by decide : 190086 ≤ 1348326) (Nat.le_max_left _ _)
      have hr2112 : 2112 ≤ max rFrom (max rRecv (max 286196 rInto)) :=
        Nat.le_trans (by decide : 2112 ≤ 286196)
          (Nat.le_trans (Nat.le_max_left 286196 rInto)
            (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _)))
      have hr286 : 286196 ≤ max rFrom (max rRecv (max 286196 rInto)) :=
        Nat.le_trans (Nat.le_max_left 286196 rInto)
          (Nat.le_trans (Nat.le_max_right rRecv _) (Nat.le_max_right rFrom _))
      exact (hOr.of_imp fun _ h => h.2).mono
        (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.max_le.mpr ⟨hG_le, Nat.le_max_right _ _⟩⟩)
        (by decide) (by decide)
        (Nat.max_le.mpr ⟨hr2112, Nat.max_le.mpr ⟨hr286, Nat.le_refl _⟩⟩)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hdec_ok
  unfold SpqrRecvTightEnv
  exact phaseCreditSpec_or_freeOnly_fine
    (phaseCreditSpec_seq_zero_left_fine hDec (phaseCreditSpec_or_freeOnly_fine hAfterDecOk))

/-- Zero-skip SPQR `recv` bound (`Δcum = 4,160,856 ≤ 4,862,949` for any `cRecv ≤ 1,910,199`). -/
theorem spqrRecvParts_c07_zeroSkip_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hZero : ChainRecvKeyZeroSkip xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      4160856 294391 294391 (max rRecv 286196) := by
  unfold SpqrRecvC07TightEnv
  have hBase := spqrRecvParts_zeroSkip_phaseCreditSpec_tight_of_caps F K (c07TightCreditSpec_inst F)
    C09a stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hZero
  have heq : 359623 + cRecv + (207625 + 376193) = cRecv + 943441 := by
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hle_eq : 359623 + cRecv + (207625 + 376193) ≤ 2853640 := by
    rw [heq]
    exact Nat.le_trans (Nat.add_le_add_right hcRecv 943441) (by decide)
  have hmax : max 1348326 (359623 + cRecv + (207625 + 376193)) ≤ 2853640 :=
    Nat.max_le.mpr ⟨by decide, hle_eq⟩
  have hcum : 1307216 + max 1348326 (359623 + cRecv + (207625 + 376193)) ≤ 4160856 :=
    Nat.le_trans (Nat.add_le_add_left hmax 1307216) (by decide)
  have hreq : max 79236 (max 2560 (max rRecv (max 286196 2400))) ≤ max rRecv 286196 := by
    have h286 : 286196 ≤ max rRecv 286196 := Nat.le_max_right _ _
    exact Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 79236 ≤ 286196) h286,
       Nat.max_le.mpr
         ⟨Nat.le_trans (by decide : 2560 ≤ 286196) h286,
          Nat.max_le.mpr
            ⟨Nat.le_max_left _ _,
             Nat.max_le.mpr ⟨h286, Nat.le_trans (by decide : 2400 ≤ 286196) h286⟩⟩⟩⟩
  exact hBase.mono hcum (Nat.le_refl _) (Nat.le_refl _) hreq

/-- Specialization of `spqrRecvParts_c07_zeroSkip_phaseCreditSpec_tight` at `cRecv = 1,647,247` (`Δcum = 3,897,904` B). -/
theorem spqrRecvParts_c07_zeroSkip_c09a_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hZero : ChainRecvKeyZeroSkip xRk) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      3897904 294391 294391 (max rRecv 286196) := by
  unfold SpqrRecvC07TightEnv
  have hBase := spqrRecvParts_zeroSkip_phaseCreditSpec_tight_of_caps F K (c07TightCreditSpec_inst F)
    C09a stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hZero
  have hreq : max 79236 (max 2560 (max rRecv (max 286196 2400))) ≤ max rRecv 286196 := by
    have h286 : 286196 ≤ max rRecv 286196 := Nat.le_max_right _ _
    exact Nat.max_le.mpr
      ⟨Nat.le_trans (by decide : 79236 ≤ 286196) h286,
       Nat.max_le.mpr
         ⟨Nat.le_trans (by decide : 2560 ≤ 286196) h286,
          Nat.max_le.mpr
            ⟨Nat.le_max_left _ _,
             Nat.max_le.mpr ⟨h286, Nat.le_trans (by decide : 2400 ≤ 286196) h286⟩⟩⟩⟩
  exact hBase.mono (by decide) (Nat.le_refl _) (Nat.le_refl _) hreq

/-- Stage P3 `try_decrypt` `PhaseCreditSpec` (`maxSeeds = 12`, `dhCap ≤ 5`) for fresh Bob sessions
(`≤ 12` sender/receiver seeds, `0` skipped SPQR keys):
`w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904 = 5,890,676 ≤ 6,855,721` B. -/
theorem w2TryDecrypt_bob12_zeroSkip_spqrC07_phaseCreditSpec
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hZero : ChainRecvKeyZeroSkip xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptSeedsEnv 12 dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum 12 dhCap needGrow maxSteps 4160856)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12) hDhSmall hlen hchain
    (spqrRecvParts_c07_zeroSkip_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hZero)
    hct

/-- Specialization of `w2TryDecrypt_bob12_zeroSkip_spqrC07_phaseCreditSpec` at `cRecv = 1,647,247` (`5,890,676` B at `dhCap = 5, maxSteps = 12`). -/
theorem w2TryDecrypt_bob12_zeroSkip_spqrC07_c09a_phaseCreditSpec
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hZero : ChainRecvKeyZeroSkip xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptSeedsEnv 12 dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum 12 dhCap needGrow maxSteps 3897904)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12) hDhSmall hlen hchain
    (spqrRecvParts_c07_zeroSkip_c09a_phaseCreditSpec_tight F K C09a
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hZero)
    hct

end LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
