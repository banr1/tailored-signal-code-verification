/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Tight `fineCostModel` `decrypt_prekey` Slot Specification

Tight `fineCostModel` slot credit specification for `signal_session_handshake::decrypt_prekey` /
`process_prekey`:
1. Tight clone, record-serialize, and store-poll bounds (`segCloneTightCum`,
   `recordSerializeTightCum`, `sessLoadPollTightDelta*`, `sessStorePollTightDelta*`,
   `smallStorePollTightDelta*`, `w4SpqrInit32_fine_phaseCredit`) with separate
   `(sessFileCap, smallFileCap)` store caps.
2. Fresh-Bob `prev1` serialization (`FreshBobPrev1Dom`, `0` receiver chains) on Path C.
3. Split-arm slot envelopes (`W4DecryptPrekeySplitSlotEnv`, `W4DecryptPrekeySplitWideSlotEnv`)
   parameterized by black-box `PhaseCreditSpec` inputs (`TryDecEnv` vs `TryDecAC`), `FitsEnv`
   corollaries, `W4SlotR3bEnv` wire+slot composition, and closed `Nat` cap evaluations.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec

set_option autoImplicit false

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText keyName pathOf)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents sessLoadPollTightDeltaCum
   sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak sessLoadPollTightMaxReq
   sessStorePollMaxReq sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak smallStorePollTightDeltaCum smallStorePollTightDeltaLive
   smallStorePollTightDeltaPeak smallStorePollTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom SessionCloneDom phaseCreditSpec_fromFEnv_fine_488
   phaseCreditSpec_fromMEnv_fine_8674 serialize_dom_phaseCredit_tight
   sessionClone_dom_phaseCredit_tight sessionClone_drop_cancel_dom_phaseCredit_tight
   sessionClone_freshBob16K_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv phaseCredit_archivedTrialLoop_le4)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4InitBobSpqrEnv W4PqxdhAcceptEnv W4StageP2OverBobEnv
   phaseCredit_w4BobSessionBuild_small phaseCredit_w4InitBob_small
   phaseCredit_w4PqxdhAccept_small phaseCredit_w4StageP2OverBob_small w4InitBobOuterCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (phaseCreditSpec_ite_nil phaseCreditSpec_or4 stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathAWideEnv W4DecryptPrekeyPathBEnv
   W4DecryptPrekeyPathBWideEnv W4DecryptPrekeyPathCEnv W4DecryptPrekeyPathCWideEnv
   W4DecryptPrekeySlotEnv W4DecryptPrekeySlotParams W4DecryptPrekeySplitWideSlotEnv
   W4DecryptPrekeyWideSlotEnv W4ErrTailEnv W4ErrTailWideEnv W4InitBobSpqrWideEnv
   W4InitBobWideEnv W4SlotR3bEnv W4StageP2MatchedCheckEnv W4StageP2MatchedEnv
   W4StageP2MatchedErrStrEnv W4StageP2MatchedWideEnv W4StageP2OverBobWideEnv
   W4StageP2PathACliEnv W4StageP2PathACliWideEnv W4StageP2PathCCliEnv W4StageP2PathCCliWideEnv
   W4StageP3Env W4StageP3WideEnv W4StageP4MatchedCliWideEnv W4StageP4PathACliWideEnv
   W4StageP4PathCCliWideEnv W4TryDecryptCloneFailWideEnv phaseCredit_optStageEnv
   w4SlotR3bDeltaCum w4SlotR3bDeltaLive w4SlotR3bDeltaPeak w4SlotR3bMaxReq
   w4SlotR3b_fine_phaseCredit w4SlotR3b_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4SmallStoreStepEnv W4StageP1OkCliEnv W4StageP1UntrustedCliEnv W4StageP4MatchedCliEnv
   W4StageP4PathACliEnv W4StageP4PathCCliEnv opened_all_dirDomainCaps
   phaseCreditSpec_seq_freeOnly_exact w4SpqrInitCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (FreshBobPrev1Dom fineOptLarge optLargeCost_fine_eq promoteStateArchive_dom_fine_phaseCredit_tight
   tryDecryptCloneFail_dom_fine_cancel_phaseCredit w4ErrTail_fine_phaseCredit_tight
   w4KeyIdSmallStoreStep16_fine_phaseCredit w4PeerSmallStoreStep32_fine_phaseCredit
   w4SessLoadStep_fine_phaseCredit w4SessStorePrev1Step_freshBob_fine_phaseCredit
   w4SessStoreStep_dom_fine_phaseCredit w4SmallStoreStep16_fine_phaseCredit
   w4SmallStoreStep32_fine_phaseCredit w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## Arithmetic Combinators -/

private theorem max_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    max a b ≤ max a' b' :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _),
    Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem seqPeak_mono {p1 p1' l1 l1' q q' : Nat}
    (hp : p1 ≤ p1') (hl : l1 ≤ l1') (hq : q ≤ q') :
    max p1 (l1 + q) ≤ max p1' (l1' + q') :=
  max_mono hp (Nat.add_le_add hl hq)

private theorem fourStagePeak_mono
    {p1 p1' l1 l1' p2 p2' l2 l2' p3 p3' l3 l3' p4 p4' : Nat}
    (hp1 : p1 ≤ p1') (hl1 : l1 ≤ l1')
    (hp2 : p2 ≤ p2') (hl2 : l2 ≤ l2')
    (hp3 : p3 ≤ p3') (hl3 : l3 ≤ l3')
    (hp4 : p4 ≤ p4') :
    max p1 (l1 + max p2 (l2 + max p3 (l3 + p4))) ≤
      max p1' (l1' + max p2' (l2' + max p3' (l3' + p4'))) :=
  seqPeak_mono hp1 hl1 (seqPeak_mono hp2 hl2 (seqPeak_mono hp3 hl3 hp4))

private theorem fiveStepPeak_mono {p l q q' : Nat} (hq : q ≤ q') :
    max p (l + max p (l + max p (l + max p (l + q)))) ≤
      max p (l + max p (l + max p (l + max p (l + q')))) :=
  seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
    (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) hq)))

private theorem le_fiveStepPeak_inner (p l pOver tail : Nat) :
    pOver ≤ max p (l + max p (l + max p (l + max p (l + max pOver tail)))) := by
  have h1 : pOver ≤ max pOver tail := Nat.le_max_left _ _
  have h2 : pOver ≤ max p (l + max pOver tail) :=
    Nat.le_trans h1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  have h3 : pOver ≤ max p (l + max p (l + max pOver tail)) :=
    Nat.le_trans h2 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  have h4 : pOver ≤ max p (l + max p (l + max p (l + max pOver tail))) :=
    Nat.le_trans h3 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
  exact Nat.le_trans h4 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))

private theorem le_twoStepPeak_left (p2 l2 p3 l3 a b : Nat) :
    a ≤ max p2 (l2 + max p3 (l3 + max a b)) := by
  have h1 : a ≤ max a b := Nat.le_max_left a b
  have h2 : a ≤ max p3 (l3 + max a b) :=
    Nat.le_trans h1 (Nat.le_trans (Nat.le_add_left _ l3) (Nat.le_max_right p3 _))
  exact Nat.le_trans h2 (Nat.le_trans (Nat.le_add_left _ l2) (Nat.le_max_right p2 _))

private theorem zero_or_max4_le (x : Nat) :
    max 0 (max (max x x) (max x x)) ≤ x := by
  omega

private theorem slot_final_peak_le (rp l : Nat) :
    max 0 (max (max rp rp) (max rp rp)) ≤ max rp l :=
  Nat.le_trans (zero_or_max4_le rp) (Nat.le_max_left rp l)

/-! ## Tight `fineCostModel` Stage P1, P2, P3, & P4 `PhaseCreditSpec`s -/

theorem w4StageP1OkCli_fine_phaseCredit
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hSessCap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessFileCap)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    let cL := 488 + sessLoadPollTightDeltaCum sCap deserCum
    let lL := sessLoadPollTightDeltaLive sCap deserLive
    let pL := sessLoadPollTightDeltaPeak sCap deserPeak
    let rL := max 24 (sessLoadPollTightMaxReq sCap deserMaxReq)
    let cT := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let lT := smallStorePollTightDeltaLive smCap maxEntries
    let pT := smallStorePollTightDeltaPeak smCap maxEntries
    let rT := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel (W4StageP1OkCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT) (lL + lT) (max pL (lL + pT)) (max rL rT) := by
  dsimp only
  have hLoad := w4SessLoadStep_fine_phaseCredit hdcSess hdir hpeer hSessCap hdeser
  have hTrust := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  exact hLoad.seq hTrust

theorem w4StageP1UntrustedCli_fine_phaseCredit
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hSessCap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ sessFileCap)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    let cL := 488 + sessLoadPollTightDeltaCum sCap deserCum
    let lL := sessLoadPollTightDeltaLive sCap deserLive
    let pL := sessLoadPollTightDeltaPeak sCap deserPeak
    let rL := max 24 (sessLoadPollTightMaxReq sCap deserMaxReq)
    let cT := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let lT := smallStorePollTightDeltaLive smCap maxEntries
    let pT := smallStorePollTightDeltaPeak smCap maxEntries
    let rT := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP1UntrustedCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT + 9619)
      (lL + lT)
      (max pL (lL + max pT lT))
      (max rL (max rT 40)) := by
  dsimp only
  have hSm40 : 40 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hLoad := w4SessLoadStep_fine_phaseCredit hdcSess hdir hpeer hSessCap hdeser
  have hTrust := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  have hClone := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (stringClone_phaseCredit_small fineCostModel_modelHyps hpeer hSm40)
  have hTC := (hTrust.seq hClone).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  exact (hLoad.seq hTC).mono
    (Nat.le_of_eq (Nat.add_assoc _ _ 9619).symm)
    (Nat.le_of_eq (Nat.add_assoc _ _ 0 ▸ rfl))
    (Nat.le_refl _)
    (Nat.le_refl _)

theorem w4StageP2Matched_dom_fine_phaseCredit {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec fineCostModel
      (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (4 * (c_dec + c_tr) + (8420940 + c_push))
      (fineOptLarge archEncCap)
      (max (p_dec + p_tr) (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap))
      (max (max r_dec r_tr) (max (max (max 208000 archPqCap) archEncCap) r_push)) := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoop := phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop
  have hProm := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (promoteStateArchive_dom_fine_phaseCredit_tight hArchValid hArchEnc hPush)
  have hOptProm := (hFree.or hProm).mono
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hSeq := (hLoop.seq hOptProm).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.zero_add _))
    (Nat.le_of_eq (congrArg (max _) (Nat.zero_add _))) (Nat.le_refl _)
  exact (hFree.or hSeq).mono
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
    (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))

private theorem p2a_tight_cum_le (a b1 b2 c : Nat) :
    a + (a + (a + (a + ((b1 + b2) + (a + c))))) ≤ 5 * a + b1 + b2 + c := by
  omega

private theorem p2a_tight_live_le (a : Nat) :
    a + (a + (a + (a + (0 + a)))) ≤ 5 * a := by
  omega

private theorem p2a_bob_maxReq_le (ikmCap : Nat) :
    max (max ikmCap 1569) (max 4224 68) ≤ max ikmCap 4224 :=
  Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _,
       Nat.le_trans (by decide : 1569 ≤ 4224) (Nat.le_max_right _ _)⟩,
     Nat.max_le.mpr ⟨Nat.le_max_right _ _,
       Nat.le_trans (by decide : 68 ≤ 4224) (Nat.le_max_right _ _)⟩⟩

private theorem p2a_tight_maxReq_le (r16 ikmCap : Nat) :
    max r16 (max r16 (max r16 (max r16 (max (max ikmCap 4224) (max r16 192))))) ≤
      max r16 (max ikmCap 4224) := by
  have hr : r16 ≤ max r16 (max ikmCap 4224) := Nat.le_max_left _ _
  have hb : max ikmCap 4224 ≤ max r16 (max ikmCap 4224) := Nat.le_max_right _ _
  have h192 : 192 ≤ max r16 (max ikmCap 4224) :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hb)
  exact Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr,
    Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hb, Nat.max_le.mpr ⟨hr, h192⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathACli_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 8186)
      (5 * l16)
      (max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
        (l16 + max 0 (0 + max p16 l16))))))
      (max r16 (max ikmCap 4224)) := by
  dsimp only
  have hSpk := w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
    (fun bs hr => hSmallCap spkDir (by simp) _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hKp := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hSpqr := w4SpqrInit32_fine_phaseCredit F x_spqr hspqrKey
  have hBob : PhaseCreditSpec fineCostModel (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      (w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) 0 0 (max ikmCap 4224) :=
    (phaseCredit_w4InitBob_small fineCostModel_modelHyps (hasOpk := hasOpk)
      hold hnew hSmall hSpqr).mono
      (Nat.le_refl _) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl 0, Nat.le_refl 0⟩)
      (p2a_bob_maxReq_le ikmCap)
  have hReg := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hTail := w4ErrTail_fine_phaseCredit_tight
  have h67 := (hReg.seq hTail).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h57 := hBob.seq h67
  have h47 := hKp.seq h57
  have h37 := hOptPk.seq h47
  have h27 := hKpk.seq h37
  exact (hSpk.seq h27).mono
    (p2a_tight_cum_le _ _ _ _)
    (p2a_tight_live_le _)
    (Nat.le_refl _)
    (p2a_tight_maxReq_le _ _)

private theorem p2c_tight_cum_le (cCur cLoop c16 cOver cTail : Nat) :
    cCur + (cLoop + (c16 + (c16 + (c16 + (c16 + (cOver + (c16 + cTail))))))) ≤
      cCur + cLoop + 5 * c16 + cOver + cTail := by
  omega

private theorem p2c_tight_live_le (l16 lOver : Nat) :
    0 + (0 + (l16 + (l16 + (l16 + (l16 + (lOver + l16)))))) ≤ 5 * l16 + lOver := by
  omega

private theorem p2c_tight_maxReq_le (rCurAll rDec rTr rSerAll r16 ikmCap : Nat) :
    max (max rCurAll 192)
      (max (max rDec rTr)
        (max r16 (max r16 (max r16 (max r16
          (max (max rSerAll (max ikmCap 4224)) (max r16 192))))))) ≤
    max (max rCurAll (max rDec rTr))
      (max rSerAll (max r16 (max ikmCap 4224))) := by
  let T := max (max rCurAll (max rDec rTr))
    (max rSerAll (max r16 (max ikmCap 4224)))
  have hL : max rCurAll (max rDec rTr) ≤ T := Nat.le_max_left _ _
  have hR : max rSerAll (max r16 (max ikmCap 4224)) ≤ T := Nat.le_max_right _ _
  have h1 : rCurAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hL
  have h2 : max rDec rTr ≤ T := Nat.le_trans (Nat.le_max_right _ _) hL
  have h3 : rSerAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hR
  have h4 : max r16 (max ikmCap 4224) ≤ T := Nat.le_trans (Nat.le_max_right _ _) hR
  have hr16 : r16 ≤ T := Nat.le_trans (Nat.le_max_left _ _) h4
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_right _ _) h4
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hikm)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨h1, h192⟩,
     Nat.max_le.mpr ⟨h2,
       Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨hr16,
         Nat.max_le.mpr ⟨hr16, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h3, hikm⟩,
           Nat.max_le.mpr ⟨hr16, h192⟩⟩⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathCCli_dom_fine_phaseCredit {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    {CurTrialFailEnv : List AllocEvent → Prop} {curPqCap c_cur p_cur r_cur : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let lOver := fineOptLarge archEncCap
    let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
    let pRest := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    PhaseCreditSpec fineCostModel
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((8277456 + c_cur + 8186) + 4 * (c_dec + c_tr) +
        5 * c16 + (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 8186)
      (5 * l16 + lOver)
      (max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pRest))
      (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
        (max (max (max (max 208000 archPqCap) archEncCap) r_push)
          (max r16 (max ikmCap 4224)))) := by
  dsimp only
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hCur : PhaseCreditSpec fineCostModel
      (fun e1 => FreeOnlyEvs e1 ∨
        W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur) e1)
      (8277456 + c_cur + 8186) 0
      (1080975 + fineOptLarge curPqCap + p_cur)
      (max (max (max 208000 curPqCap) r_cur) 192) :=
    (hFree.or (tryDecryptCloneFail_dom_fine_cancel_phaseCredit hCurDom hCurTrial)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hLoop : PhaseCreditSpec fineCostModel
      (fun e2 => FreeOnlyEvs e2 ∨
        IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs e2)
      (4 * (c_dec + c_tr)) 0 (p_dec + p_tr) (max r_dec r_tr) :=
    (hFree.or (phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hSpk := w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
    (fun bs hr => hSmallCap spkDir (by simp) _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hKp := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hSer := serialize_dom_phaseCredit_tight hArchValid hArchEnc
  rw [optLargeCost_fine_eq archPqCap, optLargeCost_fine_eq archEncCap] at hSer
  have hSpqr := w4SpqrInit32_fine_phaseCredit F x_spqr hspqrKey
  have hOver : PhaseCreditSpec fineCostModel
      (W4StageP2OverBobEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32)
      (fineOptLarge archEncCap)
      (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap)
      (max (max (max (max 208000 archPqCap) archEncCap) r_push) (max ikmCap 4224)) := by
    have h0 := phaseCredit_w4StageP2OverBob_small fineCostModel_modelHyps (hasOpk := hasOpk)
      hSer hPush hold hnew hSmall hSpqr
    have hle : fineOptLarge archEncCap ≤
        1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap :=
      Nat.le_add_left _ _
    exact h0.mono
      (Nat.le_refl _)
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr
        ⟨Nat.le_refl _,
         by simp only [Nat.max_self, Nat.add_zero]; exact hle⟩)
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (p2a_bob_maxReq_le ikmCap) (Nat.le_max_right _ _)⟩)
  have hReg := w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
    (fun bs hr => hSmallCap ownDir (by simp) _ bs hr)
  have hTail := w4ErrTail_fine_phaseCredit_tight
  have h89 := (hReg.seq hTail).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h79 := hOver.seq h89
  have h69 := hKp.seq h79
  have h59 := hOptPk.seq h69
  have h49 := hKpk.seq h59
  have h39 := hSpk.seq h49
  have h29 := hLoop.seq h39
  exact (hCur.seq h29).mono
    (p2c_tight_cum_le _ _ _ _ _)
    (p2c_tight_live_le _ _)
    (by simp only [Nat.zero_add]; exact Nat.le_refl _)
    (p2c_tight_maxReq_le _ _ _ _ _ _)

theorem w4StageP3_fine_phaseCredit_tight
    {TryDecEnv : List AllocEvent → Prop} {c l p r : Nat}
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c l p r) :
    PhaseCreditSpec fineCostModel (W4StageP3Env TryDecEnv)
      (c + 8186) l (max p l) (max r 192) :=
  (hTd.seq w4ErrTail_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero l))
    (Nat.le_of_eq (congrArg (max p) (Nat.add_zero l))) (Nat.le_refl _)

theorem w4StageP4MatchedCli_dom_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles}
    {peersDir sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel (W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec)
      (c32 + cSt0) (l32 + lSt0) (max p32 (l32 + pSt0)) (max r32 rSt0) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc)
  exact hSave.seq hStore

private theorem p4_maxReq_le (r32 r16 rSt : Nat) :
    max r32 (max r32 (max r16 rSt)) ≤ max (max r32 r32) (max r16 rSt) := by
  have hr32 : r32 ≤ max (max r32 r32) (max r16 rSt) :=
    Nat.le_trans (Nat.le_max_left r32 r32) (Nat.le_max_left _ _)
  exact Nat.max_le.mpr ⟨hr32, Nat.max_le.mpr ⟨hr32, Nat.le_max_right _ _⟩⟩

theorem w4StageP4PathACli_dom_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        g_rec r_rec)
      (c32 + c32 + c16 + cSt0)
      (l32 + l32 + l16 + lSt0)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt0))))
      (max (max r32 r32) (max r16 rSt0)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
    (fun bs hr => hSmallCap peersDir (by simp) _ bs hr)
  have hMark := w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_maxReq_le _ _ _)

theorem w4StageP4PathCCli_freshBob_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal smallFileCap bobPqCap prevEncCap totalPrev1Cap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G sess enc) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
    let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
    let pSt1 := sessStorePollTightDeltaPeak
      (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
    let rSt1 := max 32
      (sessStorePollMaxReq
        (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        G sess enc)
      (c32 + c32 + c16 + cSt1)
      (l32 + l32 + l16 + lSt1)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt1))))
      (max (max r32 r32) (max r16 rSt1)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
    (fun bs hr => hSmallCap peersDir (by simp) _ bs hr)
  have hMark := w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName
    (fun bs hr => hSmallCap kpkDir (by simp) _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
      (fun bs hr => hSmallCap opkDir (by simp) _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (w4SessStorePrev1Step_freshBob_fine_phaseCredit hdcSess hpeer hbob)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_maxReq_le _ _ _)

/-! ## Closed-Form Tight Slot Formulas & `W4DecryptPrekeySplitSlotEnv` -/

/-- Split-arm `decrypt_prekey` slot envelope allowing Path A and Path C (fresh Bob responder
sessions) to carry a sharper Stage P3 `TryDecAC` envelope than Path B (`TryDecEnv`).
At `TryDecAC := P.TryDecEnv`, `W4DecryptPrekeySplitSlotEnv P P.TryDecEnv = W4DecryptPrekeySlotEnv P`
definitionally (`rfl`). -/
def W4DecryptPrekeySplitSlotEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (TryDecAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
      W4DecryptPrekeyPathBEnv P e ∨
      W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
      W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
    FreeOnlyEvs evs

theorem w4DecryptPrekeySplitSlotEnv_self {α : Type} (P : W4DecryptPrekeySlotParams α) :
    W4DecryptPrekeySplitSlotEnv P P.TryDecEnv = W4DecryptPrekeySlotEnv P :=
  rfl

/-- Domain bundle for `W4DecryptPrekeySplitSlotEnv` and `W4DecryptPrekeySlotEnv`. -/
structure W4DecryptPrekeyTightDom {α : Type} (P : W4DecryptPrekeySlotParams α)
    (sessFileCap smallFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat) : Prop where
  peer_len : P.peer.name.bytes.length ≤ 40
  ownKey_len : P.ownKeyName.length ≤ 64
  ownReg_len : P.ownRegName.length ≤ 64
  kpkMark_len : P.kpkMarkName.length ≤ 64
  res_old : P.x_res.cap.toNat ≤ ikmCap
  res_new : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap
  ikm_small : max ikmCap 1569 ≤ 135167
  spqr_key : P.x_spqr.p.authKey.length ≤ 32
  sess_cap : ∀ bs, P.rd P.files (pathOf P.sessDir.path (addressText P.peer.val)) = .ok bs →
    bs.length ≤ sessFileCap
  small_cap : ∀ d ∈ [P.ownDir, P.peersDir, P.spkDir, P.kpkDir, P.opkDir],
    ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  cur_dom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = P.st_cur ∧ SessionGhostValid P.G_cur ses_cur ∧
        SessionCloneDom curPqCap ses_cur
  arch_valid : ∀ G ses, P.g_arch.cur = some G → P.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses
  arch_enc : (encodeRecord P.r_arch).length ≤ archEncCap
  out0_valid : ∀ G ses, P.g_out0.cur = some G → P.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom out0PqCap ses
  out0_enc : (encodeRecord P.r_out0).length ≤ out0EncCap
  out1_freshBob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap P.G_out1 P.sess_out1 P.enc_prev1
  trials_len4 : P.archivedTrials.length ≤ 4

/-- Closed `Nat` tight `Δcum` bound across all four arms of `W4DecryptPrekeySplitSlotEnv`
(taking `max` of Untrusted, Path B, Path A, and Path C). -/
def w4DecryptPrekeySplitTightCum
    (sessCap smallCap maxEntries deserCum c_cur c_dec c_tr c_push
     c_tdB c_tdAC ikmCap : Nat) : Nat :=
  let cL := 488 + sessLoadPollTightDeltaCum sessCap deserCum
  let c32 := 738 + smallStorePollTightDeltaCum smallCap maxEntries
  let c16 := 488 + smallStorePollTightDeltaCum smallCap maxEntries
  let cP1Ok := cL + c32
  let cUntr := cP1Ok + 9619
  let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
  let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
  let cPathB := cP1Ok + (4 * (c_dec + c_tr) + (8420940 + c_push)) +
    (c_tdB + 8186) + (c32 + cSt0)
  let cPathA := cP1Ok + (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 8186) +
    (c_tdAC + 8186) + (c32 + c32 + c16 + cSt0)
  let cPathC := cP1Ok +
    ((8277456 + c_cur + 8186) + 4 * (c_dec + c_tr) +
      5 * c16 + (8420940 + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 8186) +
    (c_tdAC + 8186) + (c32 + c32 + c16 + cSt1)
  max (max cUntr cPathB) (max cPathA cPathC)

/-- Pure closed-`Nat` tight `Δlive` bound across all 4 arms of `W4DecryptPrekeySplitSlotEnv`. -/
def w4DecryptPrekeySplitTightLive
    (sessCap smallCap maxEntries deserLive archEncCap out0EncCap totalPrev1Cap
     l_tdB l_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let l32 := smallStorePollTightDeltaLive smallCap maxEntries
  let l16 := smallStorePollTightDeltaLive smallCap maxEntries
  let lP1 := lL + l32
  let lSt0 := sessStorePollTightDeltaLive (fineOptLarge out0EncCap) maxEntries
  let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
  let lUntr := lP1
  let lPathB := lP1 + fineOptLarge archEncCap + l_tdB + (l32 + lSt0)
  let lPathA := lP1 + 5 * l16 + l_tdAC + (l32 + l32 + l16 + lSt0)
  let lPathC := lP1 + (5 * l16 + fineOptLarge archEncCap) + l_tdAC + (l32 + l32 + l16 + lSt1)
  max (max lUntr lPathB) (max lPathA lPathC)

/-- Pure closed-`Nat` sequential `Δpeak` bound before clamping with `Δlive`. -/
def w4DecryptPrekeySplitTightRawPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let pL := sessLoadPollTightDeltaPeak sessCap deserPeak
  let l32 := smallStorePollTightDeltaLive smallCap maxEntries
  let p32 := smallStorePollTightDeltaPeak smallCap maxEntries
  let l16 := smallStorePollTightDeltaLive smallCap maxEntries
  let p16 := smallStorePollTightDeltaPeak smallCap maxEntries
  let lP1 := lL + l32
  let pP1 := max pL (lL + max p32 l32)
  let pSt0 := sessStorePollTightDeltaPeak
    (1080975 + fineOptLarge out0PqCap + fineOptLarge out0EncCap) maxEntries
  let pSt1 := sessStorePollTightDeltaPeak
    (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
  let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
  let lOver := fineOptLarge archEncCap
  let pPeakB :=
    let pP2B := max (p_dec + p_tr) pOver
    let pP3B := max p_tdB l_tdB
    let pP4B := max p32 (l32 + pSt0)
    max pP1 (lP1 + max pP2B (lOver + max pP3B (l_tdB + pP4B)))
  let pPeakA :=
    let pP2A := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 l16))))
    let pP3A := max p_tdAC l_tdAC
    let pP4A := max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt0)))
    max pP1 (lP1 + max pP2A (5 * l16 + max pP3A (l_tdAC + pP4A)))
  let pPeakC :=
    let pP2Store := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    let pP2C := max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pP2Store)
    let pP3C := max p_tdAC l_tdAC
    let pP4C := max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt1)))
    max pP1 (lP1 + max pP2C ((5 * l16 + lOver) + max pP3C (l_tdAC + pP4C)))
  max (max pP1 pPeakB) (max pPeakA pPeakC)

/-- Closed `Nat` tight `Δpeak` bound (`max rawPeak live` so `live ≤ peak` holds by
`Nat.le_max_right`). -/
def w4DecryptPrekeySplitTightPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  max
    (w4DecryptPrekeySplitTightRawPeak sessCap smallCap maxEntries deserLive deserPeak
      curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
      p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
    (w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
      archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)

/-- Pure closed-`Nat` tight `maxReq` bound across all 4 arms of `W4DecryptPrekeySplitSlotEnv`. -/
def w4DecryptPrekeySplitTightMaxReq
    (sessCap smallCap maxEntries deserMaxReq
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap : Nat) : Nat :=
  let rL := max 24 (sessLoadPollTightMaxReq sessCap deserMaxReq)
  let r32 := max 32 (smallStorePollTightMaxReq smallCap maxEntries)
  let r16 := max 16 (smallStorePollTightMaxReq smallCap maxEntries)
  let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 out0PqCap) out0EncCap) maxEntries)
  let rSt1 := max 32
    (sessStorePollMaxReq
      (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
  max (max rL (max r32 (max r16 40)))
    (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
      (max (max (max (max 208000 archPqCap) archEncCap) r_push)
        (max (max (max r_tdB r_tdAC) 192) (max (max ikmCap 4224) (max rSt0 rSt1)))))

theorem w4DecryptPrekeySplitTight_live_le_peak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) :
    w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC ≤
      w4DecryptPrekeySplitTightPeak sessCap smallCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC :=
  Nat.le_max_right _ _

/-- Single-`TryDecEnv` specialization (`c_tdAC = c_td`, `l_tdAC = l_td`, `p_tdAC = p_td`,
`r_tdAC = r_td`) for unmodified `W4DecryptPrekeySlotEnv P`. -/
abbrev w4DecryptPrekeyTightCum
    (sessCap smallCap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap : Nat) : Nat :=
  w4DecryptPrekeySplitTightCum sessCap smallCap maxEntries deserCum
    c_cur c_dec c_tr c_push c_td c_td ikmCap

abbrev w4DecryptPrekeyTightLive
    (sessCap smallCap maxEntries deserLive archEncCap out0EncCap totalPrev1Cap l_td : Nat) : Nat :=
  w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
    archEncCap out0EncCap totalPrev1Cap l_td l_td

abbrev w4DecryptPrekeyTightPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_td p_td : Nat) : Nat :=
  w4DecryptPrekeySplitTightPeak sessCap smallCap maxEntries deserLive deserPeak
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    p_cur p_dec p_tr l_td p_td l_td p_td

abbrev w4DecryptPrekeyTightMaxReq
    (sessCap smallCap maxEntries deserMaxReq
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     r_cur r_dec r_tr r_push r_td ikmCap : Nat) : Nat :=
  w4DecryptPrekeySplitTightMaxReq sessCap smallCap maxEntries deserMaxReq
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    r_cur r_dec r_tr r_push r_td r_td ikmCap

/-! ## End-to-End Tight `PhaseCreditSpec`, `FitsEnv`, & `W4SlotR3bEnv` Theorems -/

private theorem splitMaxReq_untr_le (rL r32 r16 rRest : Nat) :
    max rL (max r32 40) ≤ max (max rL (max r32 (max r16 40))) rRest := by
  let T := max (max rL (max r32 (max r16 40))) rRest
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have h40 : 40 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  exact Nat.max_le.mpr ⟨hrL, Nat.max_le.mpr ⟨hr32, h40⟩⟩

private theorem splitMaxReq_B_le
    (rL r32 r16 rCur r_dec r_tr rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max (max r_dec r_tr) rArch)
        (max (max r_tdB 192) (max r32 rSt0))) ≤
    max (max rL (max r32 (max r16 40)))
      (max (max rCur (max r_dec r_tr))
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max (max rCur (max r_dec r_tr))
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB : max (max rCur (max r_dec r_tr))
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))) ≤ T :=
    Nat.le_max_right _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hdt : max r_dec r_tr ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hB)
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdB : max r_tdB 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_left r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRR))
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hdt, hArch⟩,
       Nat.max_le.mpr ⟨htdB, Nat.max_le.mpr ⟨hr32, hrSt0⟩⟩⟩⟩

private theorem splitMaxReq_A_le
    (rL r32 r16 rCurDt rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max r16 rIkm)
        (max (max r_tdAC 192) (max (max r32 r32) (max r16 rSt0)))) ≤
    max (max rL (max r32 (max r16 40)))
      (max rCurDt
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max rCurDt
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max r32 (max r16 40)))
    (max rCurDt (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr16 : r16 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdAC : max r_tdAC 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr16, hrIkm⟩,
       Nat.max_le.mpr ⟨htdAC,
         Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt0⟩⟩⟩⟩⟩

private theorem splitMaxReq_C_le
    (rL r32 r16 rCurDt rArch r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max rCurDt (max rArch (max r16 rIkm)))
        (max (max r_tdAC 192) (max (max r32 r32) (max r16 rSt1)))) ≤
    max (max rL (max r32 (max r16 40)))
      (max rCurDt
        (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 (max r16 40)))
    (max rCurDt
      (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max r32 (max r16 40)) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max r32 (max r16 40)))
    (max rCurDt (max rArch (max (max (max r_tdB r_tdAC) 192) (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr16 : r16 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA))
  have hCur : rCurDt ≤ T := Nat.le_trans (Nat.le_max_left _ _) hB
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htdAll : max (max r_tdB r_tdAC) 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have htdAC : max r_tdAC 192 ≤ T :=
    Nat.le_trans (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)) htdAll
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt1 : rSt1 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr
       ⟨Nat.max_le.mpr ⟨hCur, Nat.max_le.mpr ⟨hArch, Nat.max_le.mpr ⟨hr16, hrIkm⟩⟩⟩,
        Nat.max_le.mpr ⟨htdAC,
          Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt1⟩⟩⟩⟩⟩

/-- Tight `PhaseCreditSpec fineCostModel` for `W4DecryptPrekeySplitSlotEnv P TryDecAC` combining
tight clone/serialize/store bounds, `FreshBobPrev1Dom`, `w4SpqrInit32_fine_phaseCredit`
(`Δlive = 0, Δpeak = 0`), separate `(sessFileCap, smallFileCap)` store caps, and split Stage P3
(`TryDecEnv` vs `TryDecAC`) credits. -/
theorem w4DecryptPrekeySplitSlot_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {TryDecAC : List AllocEvent → Prop}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitSlotEnv P TryDecAC)
      (w4DecryptPrekeySplitTightCum sCap smCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap)
      (w4DecryptPrekeySplitTightLive sCap smCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)
      (w4DecryptPrekeySplitTightPeak sCap smCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitTightMaxReq sCap smCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap) := by
  dsimp only
  set sCap := max maxVal sessFileCap
  set smCap := max maxVal smallFileCap
  have hPeersCap : ∀ bs, P.rd P.files (pathOf P.peersDir.path (addressText P.peer.val)) = .ok bs →
      bs.length ≤ smallFileCap :=
    fun bs hr => hDom.small_cap P.peersDir (by simp) _ bs hr
  have hSmallP2 : ∀ d ∈ [P.spkDir, P.kpkDir, P.opkDir, P.ownDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.spkDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.kpkDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact hDom.small_cap P.opkDir (by simp) n bs hr
        · rcases List.mem_cons.mp hd3 with rfl | hd4
          · exact hDom.small_cap P.ownDir (by simp) n bs hr
          · nomatch hd4
  have hSmallP4 : ∀ d ∈ [P.peersDir, P.kpkDir, P.opkDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.peersDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.kpkDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact hDom.small_cap P.opkDir (by simp) n bs hr
        · nomatch hd3
  have hIkmSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hDom.ikm_small
  -- Target bounds across all 4 arms:
  set cTot := w4DecryptPrekeySplitTightCum sCap smCap maxEntries deserCum
    c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap
  set lTot := w4DecryptPrekeySplitTightLive sCap smCap maxEntries deserLive
    archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC
  set rpTot := w4DecryptPrekeySplitTightRawPeak sCap smCap maxEntries deserLive deserPeak
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC
  set rTot := w4DecryptPrekeySplitTightMaxReq sCap smCap maxEntries deserMaxReq
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap
  -- Arm 1: Untrusted
  have hUntr0 := w4StageP1UntrustedCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hUntr : PhaseCreditSpec fineCostModel
      (W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      cTot lTot rpTot rTot := hUntr0.mono
    (by dsimp only [cTot, w4DecryptPrekeySplitTightCum]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [lTot, w4DecryptPrekeySplitTightLive]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_untr_le _ _ _ _)
  -- Arm 2: Path B
  have hP1Ok := w4StageP1OkCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hP2B := w4StageP2Matched_dom_fine_phaseCredit P.g_arch P.r_arch
    hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush
  have hP3B := w4StageP3_fine_phaseCredit_tight hTdB
  have hP4B := w4StageP4MatchedCli_dom_fine_phaseCredit P.g_out0 P.r_out0
    hdcPeers hdcSess hdir hDom.peer_len hPeersCap hDom.out0_valid hDom.out0_enc
  have hPathB : PhaseCreditSpec fineCostModel (W4DecryptPrekeyPathBEnv P)
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2B.seq (hP3B.seq hP4B))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_B_le _ _ _ _ _ _ _ _ _ _ _ _)
  -- Arm 3: Path A (with TryDecAC)
  have hP2A := w4StageP2PathACli_fine_phaseCredit P.hasOpk P.spkId P.kpkId P.opkId
    P.F P.x_spqr hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
    hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2
  have hP3AC := w4StageP3_fine_phaseCredit_tight hTdAC
  have hP4A := w4StageP4PathACli_dom_fine_phaseCredit P.hasOpk P.opkId P.g_out0 P.r_out0
    hdcPeers hdcKpk hdcOpk hdcSess hdir hDom.peer_len hDom.kpkMark_len hSmallP4
    hDom.out0_valid hDom.out0_enc
  have hPathA : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }))
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2A.seq (hP3AC.seq hP4A))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      have h0eq : max 0 (0 + max (smallStorePollTightDeltaPeak smCap maxEntries)
          (smallStorePollTightDeltaLive smCap maxEntries)) ≤
          max (smallStorePollTightDeltaPeak smCap maxEntries)
            (smallStorePollTightDeltaLive smCap maxEntries) := by
        simp only [Nat.zero_add, Nat.zero_max]
        exact Nat.le_refl _
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _)
        (fiveStepPeak_mono h0eq)
        (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_A_le _ _ _ _ _ _ _ _ _ _)
  -- Arm 4: Path C (with TryDecAC + FreshBobPrev1Dom)
  have hP2C := w4StageP2PathCCli_dom_fine_phaseCredit P.G_cur P.st_cur P.g_arch P.r_arch
    P.hasOpk P.spkId P.kpkId P.opkId P.F P.x_spqr hDom.cur_dom hCurTrial
    hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush
    hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
    hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2
  have hP4C := w4StageP4PathCCli_freshBob_fine_phaseCredit P.hasOpk P.opkId
    P.G_out1 P.sess_out1 P.enc_prev1 hdcPeers hdcKpk hdcOpk hdcSess hdir
    hDom.peer_len hDom.kpkMark_len hSmallP4 hDom.out1_freshBob
  have hPathC : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }))
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2C.seq (hP3AC.seq hP4C))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitTightCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitTightLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitTightRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitTightMaxReq]
        exact splitMaxReq_C_le _ _ _ _ _ _ _ _ _ _)
  have h4 := phaseCreditSpec_or4 (fun _ h => h) hUntr hPathB hPathA hPathC
  have hSeq := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps h4
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (hFree.or hSeq).mono
    (zero_or_max4_le cTot)
    (zero_or_max4_le lTot)
    (slot_final_peak_le rpTot lTot)
    (zero_or_max4_le rTot)

/-- Unmodified `W4DecryptPrekeySlotEnv P` specialization (`TryDecAC := P.TryDecEnv`). -/
theorem w4DecryptPrekeySlot_fine_phaseCredit_tight {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec fineCostModel P.TryDecEnv c_td l_td p_td r_td) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeyTightCum sCap smCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeyTightLive sCap smCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_td)
      (w4DecryptPrekeyTightPeak sCap smCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeyTightMaxReq sCap smCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_td ikmCap) :=
  w4DecryptPrekeySplitSlot_fine_phaseCredit P hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess
    hdir hDom hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hTd hTd

/-- `StoresGhost.opened` (`maxDir = 26 ≤ 64`, `maxEntries = 0`, `maxVal = 0`) specialization of
`w4DecryptPrekeySplitSlot_fine_phaseCredit`. -/
theorem w4DecryptPrekeySplitSlot_opened_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {TryDecAC : List AllocEvent → Prop}
    {sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSpk : P.spkDir = StoresGhost.opened.signed)
    (hKpk : P.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            P.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hOpk : P.opkDir = StoresGhost.opened.oneTime)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitSlotEnv P TryDecAC)
      (w4DecryptPrekeySplitTightCum sessFileCap smallFileCap 0 deserCum
        c_cur c_dec c_tr c_push c_tdB c_tdAC ikmCap)
      (w4DecryptPrekeySplitTightLive sessFileCap smallFileCap 0 deserLive
        archEncCap out0EncCap totalPrev1Cap l_tdB l_tdAC)
      (w4DecryptPrekeySplitTightPeak sessFileCap smallFileCap 0 deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitTightMaxReq sessFileCap smallFileCap 0 deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap) := by
  obtain ⟨hdcOwn0, hdcPeers0, hdcSpk0, hdcKot0, hdcKlr0, hdcOpk0, hdcSess0⟩ :=
    opened_all_dirDomainCaps
  have hdcOwn : DirDomainCaps 26 0 0 P.ownDir := hOwn ▸ hdcOwn0
  have hdcPeers : DirDomainCaps 26 0 0 P.peersDir := hPeers ▸ hdcPeers0
  have hdcSpk : DirDomainCaps 26 0 0 P.spkDir := hSpk ▸ hdcSpk0
  have hdcKpk : DirDomainCaps 26 0 0 P.kpkDir := by
    rcases hKpk with h1 | h2
    · exact h1 ▸ hdcKot0
    · exact h2 ▸ hdcKlr0
  have hdcOpk : DirDomainCaps 26 0 0 P.opkDir := hOpk ▸ hdcOpk0
  have hdcSess : DirDomainCaps 26 0 0 P.sessDir := hSess ▸ hdcSess0
  have h := w4DecryptPrekeySplitSlot_fine_phaseCredit P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess (by decide)
    hDom hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hTdB hTdAC
  simpa only [Nat.zero_max] using h

/-- Direct `FitsEnv fineCostModel` bridge for `W4DecryptPrekeySplitSlotEnv` & `W4SlotR3bEnv`. -/
theorem w4SlotR3b_split_fine_phaseCredit {α : Type}
    (x_pksm : PksmGhost) (P : W4DecryptPrekeySlotParams α)
    {TryDecAC : List AllocEvent → Prop} {c l p r : Nat}
    (hDec : PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitSlotEnv P TryDecAC) c l p r) :
    PhaseCreditSpec fineCostModel
      (W4SlotR3bEnv x_pksm (W4DecryptPrekeySplitSlotEnv P TryDecAC))
      (w4SlotR3bDeltaCum x_pksm c)
      (w4SlotR3bDeltaLive x_pksm l)
      (w4SlotR3bDeltaPeak x_pksm l p)
      (w4SlotR3bMaxReq x_pksm r) :=
  w4SlotR3b_fine_phaseCredit x_pksm hDec

export LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fitsEnv_fineCostModel_of_phaseCredit)
export LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (w4SlotR3b_live_le_peak)

/-! ## Closed-`Nat` Canonical Slot Cap Evaluations -/

/-- Canonical CLI domain instantiated `w4DecryptPrekeySplitTightCum`:
- `curPqCap = 286,196`, `archPqCap = 286,196`, `archEncCap = 2,097,152`,
  `out0PqCap = 286,196`, `out0EncCap = 2,097,152`, `bobPqCap = 16,384`,
  `prevEncCap = 2,097,152`, `totalPrev1Cap = 2,457,152`, `ikmCap = 4,096`;
- `c_cur = w2TryDecryptSeeds738Cum 5 true 12 23313687` (`26,766,574`),
  `c_dec = deserCum` (`0` under `deser = 0`, `20,638,720` under Set A, `19,417,728` under Set B),
  `c_tr = 8,277,456 + w2TryDecryptSeeds738Cum 5 true 12 23313687 + 8,186` (`35,052,216`),
  `c_push = 9,923` (`Vec::push` 4-entry `Vec<Vec<u8>>`),
  `c_tdB = w2TryDecryptSeeds738Cum 5 true 12 23313687 + 57,642` (`26,824,216`). -/
def w4CanonicalSplitCum (sessCap smallCap maxEntries deserCum c_tdAC : Nat) : Nat :=
  let cFail := w2TryDecryptSeeds738Cum 5 true 12 23313687
  let cTr := 8277456 + cFail + 8186
  let cTdB := w2TryDecryptSeeds738Cum 5 true 12 23313687 + 57642
  w4DecryptPrekeySplitTightCum sessCap smallCap maxEntries deserCum
    cFail deserCum cTr 9923 cTdB c_tdAC 4096

/-- Canonical CLI domain instantiated `w4DecryptPrekeySplitTightLive` (`maxOldCap = 2,000`,
`maxCt = 65,536`, parameterized by `spqrLive` ∈ `{294391, 605066}`). -/
def w4CanonicalSplitLive (sessCap smallCap maxEntries deserLive spqrLive : Nat) : Nat :=
  let lTd := w2TryDecryptTightLive 2000 spqrLive 65536
  w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
    2097152 2097152 2457152 lTd (w2TryDecryptTightLive 2000 294391 65536)

/-- Canonical CLI domain instantiated `w4DecryptPrekeySplitTightPeak` (`maxOldCap = 2,000`,
`maxCt = 65,536`, `p_dec = 2,407,932`, parameterized by `spqrLive`, `spqrPeak`). -/
def w4CanonicalSplitPeak
    (sessCap smallCap maxEntries deserLive deserPeak spqrLive spqrPeak : Nat) : Nat :=
  let pFail := w2TryDecryptTightPeak 2000 spqrLive spqrPeak 65536
  let pTr := 1080975 + fineOptLarge 286196 + pFail
  let lTdB := w2TryDecryptTightLive 2000 spqrLive 65536
  let pTdB := w2TryDecryptTightPeak 2000 spqrLive spqrPeak 65536
  let lTdAC := w2TryDecryptTightLive 2000 294391 65536
  let pTdAC := w2TryDecryptTightPeak 2000 294391 294391 65536
  w4DecryptPrekeySplitTightPeak sessCap smallCap maxEntries deserLive deserPeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    pFail 2407932 pTr lTdB pTdB lTdAC pTdAC

/-- Canonical CLI domain instantiated `w4DecryptPrekeySplitTightMaxReq`. -/
def w4CanonicalSplitMaxReq (sessCap smallCap maxEntries deserMaxReq : Nat) : Nat :=
  let rTd := w2TryDecryptMaxReq 5 2000 302480 65536
  w4DecryptPrekeySplitTightMaxReq sessCap smallCap maxEntries deserMaxReq
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    rTd 286196 (max 286196 rTd) 96 rTd rTd 4096

/-- Unsplit (`TryDecAC = TryDecB`) canonical `Δcum` (`c_tdAC = c_tdB = 26,824,216`). -/
def w4CanonicalUnsplitCum (sessCap smallCap maxEntries deserCum : Nat) : Nat :=
  w4CanonicalSplitCum sessCap smallCap maxEntries deserCum
    (w2TryDecryptSeeds738Cum 5 true 12 23313687 + 57642)

/-- Unsplit (`spqrLive` on all arms) canonical `Δlive`. -/
def w4CanonicalUnsplitLive (sessCap smallCap maxEntries deserLive spqrLive : Nat) : Nat :=
  let lTd := w2TryDecryptTightLive 2000 spqrLive 65536
  w4DecryptPrekeySplitTightLive sessCap smallCap maxEntries deserLive
    2097152 2097152 2457152 lTd lTd

/-- Unsplit (`spqrLive / spqrPeak` on all arms) canonical `Δpeak`. -/
def w4CanonicalUnsplitPeak
    (sessCap smallCap maxEntries deserLive deserPeak spqrLive spqrPeak : Nat) : Nat :=
  let pFail := w2TryDecryptTightPeak 2000 spqrLive spqrPeak 65536
  let pTr := 1080975 + fineOptLarge 286196 + pFail
  let lTd := w2TryDecryptTightLive 2000 spqrLive 65536
  let pTd := w2TryDecryptTightPeak 2000 spqrLive spqrPeak 65536
  w4DecryptPrekeySplitTightPeak sessCap smallCap maxEntries deserLive deserPeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    pFail 2407932 pTr lTd pTd lTd pTd

/-! ### Zero-Deserialization What-If Targets (`deser = 0`, `sessCap = 2,097,152`, `smallCap ∈ {64, 4096}`) -/

theorem w4_whatif_deser0_cum_c09a_le_d0E4 :
    w4CanonicalSplitCum 2097152 64 0 0
      (w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904) ≤ 207394530 := by
  decide

theorem w4_whatif_deser0_cum_c09a_le :
    w4CanonicalSplitCum 2097152 64 0 0
      (w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904) ≤ 222226419 := by
  decide

theorem w4_whatif_deser0_cum_card6855721_le :
    w4CanonicalSplitCum 2097152 64 0 0 6855721 ≤ 222226419 := by
  decide

theorem w4_whatif_deser0_cum_c16eval6868484_le :
    w4CanonicalSplitCum 2097152 64 0 0 6868484 ≤ 222226419 := by
  decide

theorem w4_whatif_deser0_cum_4096_le :
    w4CanonicalSplitCum 2097152 4096 0 0 6868484 ≤ 222226419 := by
  decide

theorem w4_whatif_deser0_unsplit_cum_le :
    w4CanonicalUnsplitCum 2097152 64 0 0 ≤ 270000000 := by
  decide

theorem w4_whatif_deser0_live_smallHist_le :
    w4CanonicalUnsplitLive 2097152 64 0 0 294391 ≤ 8377739 := by
  decide

theorem w4_whatif_deser0_live_4096_smallHist_le :
    w4CanonicalUnsplitLive 2097152 4096 0 0 294391 ≤ 8377739 := by
  decide

theorem w4_whatif_deser0_live_split_uncondB_le :
    w4CanonicalSplitLive 2097152 64 0 0 605066 ≤ 8481962 := by
  decide

theorem w4_whatif_deser0_peak_smallHist_le :
    w4CanonicalUnsplitPeak 2097152 64 0 0 0 294391 294391 ≤ 12139734 := by
  decide

theorem w4_whatif_deser0_peak_uncondHist_le :
    w4CanonicalUnsplitPeak 2097152 64 0 0 0 605066 621350 ≤ 12139734 := by
  decide

theorem w4_whatif_deser0_peak_4096_uncondHist_le :
    w4CanonicalUnsplitPeak 2097152 4096 0 0 0 605066 621350 ≤ 12139734 := by
  decide

theorem w4_whatif_deser0_maxReq_eq :
    w4CanonicalSplitMaxReq 2097152 64 0 0 = 2457152 := by
  decide

theorem w4_whatif_deser0_maxReq_le :
    w4CanonicalSplitMaxReq 2097152 4096 0 0 ≤ 2457152 := by
  decide

/-! ### Set A Universal Caps (`deser = 20,638,720 / 3,211,282 / 5,316,629 / 2,097,152`) -/

/-- Set A `PrevDec` + `deser` (`c_dec = 20,638,720`, `deserCum = 20,638,720`) cumulative bound. -/
def w4SetASplitCum (smallCap maxEntries c_tdAC : Nat) : Nat :=
  let cFail := w2TryDecryptSeeds738Cum 5 true 12 23313687
  let cTr := 8277456 + cFail + 8186
  let cTdB := w2TryDecryptSeeds738Cum 5 true 12 23313687 + 57642
  w4DecryptPrekeySplitTightCum 2097152 smallCap maxEntries 20638720
    cFail 20638720 cTr 9923 cTdB c_tdAC 4096

theorem w4_c16_setA_cum_c09a_le_exact :
    w4SetASplitCum 64 0 (w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904) ≤ 303343221 := by
  decide

theorem w4_c16_setA_cum_c16eval_le_exact :
    w4SetASplitCum 64 0 6868484 ≤ 303343221 := by
  decide

theorem w4_c16_setA_cum_4096_le_cap :
    w4SetASplitCum 4096 0 6868484 ≤ 303600000 := by
  decide

theorem w4_c16_setA_live_uncondHist_le_exact :
    w4CanonicalUnsplitLive 2097152 64 0 3211282 605066 ≤ 13229185 := by
  decide

theorem w4_c16_setA_live_uncondHist_4096_le_cap :
    w4CanonicalUnsplitLive 2097152 4096 0 3211282 605066 ≤ 13500000 := by
  decide

theorem w4_c16_setA_live_smallHist_le_cap :
    w4CanonicalUnsplitLive 2097152 64 0 3211282 294391 ≤ 13229185 := by
  decide

theorem w4_c16_setA_peak_uncondHist_le_exact :
    let pArchDec := 5316629
    let pFail := w2TryDecryptTightPeak 2000 605066 621350 65536
    let pTr := 1080975 + fineOptLarge 286196 + pFail
    let lTd := w2TryDecryptTightLive 2000 605066 65536
    let pTd := w2TryDecryptTightPeak 2000 605066 621350 65536
    w4DecryptPrekeySplitTightPeak 2097152 64 0 3211282 5316629
      286196 286196 2097152 286196 2097152 16384 2097152 2457152
      pFail pArchDec pTr lTd pTd lTd pTd ≤ 15922058 := by
  decide

theorem w4_c16_setA_peak_uncondHist_4096_le_cap :
    let pArchDec := 5316629
    let pFail := w2TryDecryptTightPeak 2000 605066 621350 65536
    let pTr := 1080975 + fineOptLarge 286196 + pFail
    let lTd := w2TryDecryptTightLive 2000 605066 65536
    let pTd := w2TryDecryptTightPeak 2000 605066 621350 65536
    w4DecryptPrekeySplitTightPeak 2097152 4096 0 3211282 5316629
      286196 286196 2097152 286196 2097152 16384 2097152 2457152
      pFail pArchDec pTr lTd pTd lTd pTd ≤ 16200000 := by
  decide

theorem w4_c16_setA_maxReq_2M_eq :
    w4CanonicalSplitMaxReq 2097152 4096 0 2097152 = 2457152 := by
  decide

theorem w4_c16_setA_maxReq_4M_le :
    w4CanonicalSplitMaxReq 2097152 4096 0 4194304 ≤ 4194304 := by
  decide

/-! ### Set B Universal Cap (`(20064, 16, 48)`: `deserCum = cPrevDec = 19,417,728`) -/

def w4SetBSplitCum (smallCap maxEntries c_tdAC : Nat) : Nat :=
  let cFail := w2TryDecryptSeeds738Cum 5 true 12 23313687
  let cTr := 8277456 + cFail + 8186
  let cTdB := w2TryDecryptSeeds738Cum 5 true 12 23313687 + 57642
  w4DecryptPrekeySplitTightCum 2097152 smallCap maxEntries 19417728
    cFail 19417728 cTr 9923 cTdB c_tdAC 4096

theorem w4_c16_setB_cum_c09a_le_exact :
    w4SetBSplitCum 64 0 (w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904) ≤ 297238261 := by
  decide

theorem w4_c16_setB_cum_c16eval_le_exact :
    w4SetBSplitCum 64 0 6868484 ≤ 297238261 := by
  decide

theorem w4_c16_setB_cum_4096_le_cap :
    w4SetBSplitCum 4096 0 6868484 ≤ 298000000 := by
  decide

/-! ## Widened Binary-Complete Tight `fineCostModel` `PhaseCreditSpec`s

Tight `PhaseCreditSpec fineCostModel` bounds for the widened Stage P2, P3, P4, and 4-arm slot
envelopes in `W4OuterPeakSpec` (`W4DecryptPrekeySplitWideSlotEnv`), supporting both per-directory
`(smallFileCap, kpkFileCap)` caps and uniform `smallFileCap` (`kpkFileCap := smallFileCap`), while
splitting Stage P3 `SegCloneEnv` between `CloneB` (Path B) and `CloneAC` (Paths A & C, `0` live /
`0` peak under `FreshBobCloneDom bobPqCap` with `bobPqCap ≤ 16,384`). -/

section WidenedBinaryCompleteTightSpecs

/-! ### Widened Error Tail, Path B Match/Mismatch Prefix, & Failed-Trial Bounds -/

theorem w4ErrTailWide_fine_phaseCredit_tight :
    PhaseCreditSpec fineCostModel W4ErrTailWideEnv 8674 0 0 192 :=
  (w4ErrTail_fine_phaseCredit_tight.or
    (phaseCreditSpec_fromFEnv_fine_488.or phaseCreditSpec_fromMEnv_fine_8674)).mono
    (by decide) (by decide) (by decide) (by decide)

theorem w4StageP2MatchedErrStr_fine_phaseCredit :
    PhaseCreditSpec fineCostModel W4StageP2MatchedErrStrEnv 1607 0 0 70 := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have ha70 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 70) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 70 ≤ 1607; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 70)
  have h70 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps ha70
  have ha14 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 14) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 14 ≤ 1607; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 14)
  have h14 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps ha14
  exact (hFree.or (h70.or h14)).mono (by decide) (by decide) (by decide) (by decide)

theorem w4StageP2MatchedCheck_fine_phaseCredit :
    PhaseCreditSpec fineCostModel W4StageP2MatchedCheckEnv 2345 0 0 70 := by
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have ha33 := (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 33) (al := 1)
    (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by change fineSmallAllocCost 33 ≤ 738; decide)
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
  have hd33 := PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 33) (al := 1) (by decide)
  have hSeq := ha33.seq (hd33.seq w4StageP2MatchedErrStr_fine_phaseCredit)
  exact (hFree.or hSeq).mono (by decide) (by decide) (by decide) (by decide)

theorem sessionClone_dom_fine_phaseCredit_tight {pqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses) :
    PhaseCreditSpec fineCostModel (SegCloneEnv G ses.state)
      8277456
      (1080975 + fineOptLarge pqCap)
      (1080975 + fineOptLarge pqCap)
      (max 208000 pqCap) := by
  have h := sessionClone_dom_phaseCredit_tight hgv hdom
  rwa [optLargeCost_fine_eq pqCap] at h

theorem w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit
    {curPqCap c_cur p_cur r_cur : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur) :
    PhaseCreditSpec fineCostModel
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur))
      (8277456 + c_cur + 8674)
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
    exact (hCancel.seq w4ErrTailWide_fine_phaseCredit_tight).mono
      (Nat.le_refl _)
      (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
      (Nat.le_refl _)

/-! ### Widened Stage P2 (`Matched`, `InitBob`, `OverBob`, `PathA`, `PathC`) Bounds -/

theorem w4StageP2MatchedWide_dom_fine_phaseCredit {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec fineCostModel
      (W4StageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (2345 + (4 * (c_dec + c_tr) + (8420940 + c_push)))
      (fineOptLarge archEncCap)
      (max (p_dec + p_tr) (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap))
      (max (max r_dec r_tr) (max (max (max 208000 archPqCap) archEncCap) r_push)) := by
  have hChk := w4StageP2MatchedCheck_fine_phaseCredit
  have hNarrow := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP2Matched_dom_fine_phaseCredit g_arch r_arch hArchValid hArchEnc
      hlen4 hl_le_p hDec hTrial hDrop hPush)
  have h70 : 70 ≤ max (max r_dec r_tr) (max (max (max 208000 archPqCap) archEncCap) r_push) :=
    Nat.le_trans (by decide : 70 ≤ 208000)
      (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))))
  exact (hChk.seq hNarrow).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add _))
    (by simp only [Nat.zero_add, Nat.zero_max]; exact Nat.le_refl _)
    (Nat.max_le.mpr ⟨h70, Nat.le_refl _⟩)

private theorem bob_wide_cum_le (a cq b : Nat) :
    a + (cq + b) ≤ (a + b) + cq := by
  omega

theorem w4InitBobWide_small_fine_phaseCredit
    {x_res : DoReserveCall} {hasOpk : Bool}
    {E_spqrInit : List AllocEvent → Prop} {ikmCap c_q l_q p_q r_q : Nat}
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hSpqr : PhaseCreditSpec fineCostModel E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec fineCostModel (W4InitBobWideEnv x_res hasOpk E_spqrInit)
      (W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + c_q)
      l_q
      (max p_q l_q)
      (max (max ikmCap 1569) (max r_q 68)) := by
  have hSm68 : 68 ≤ HasFineReallocCredit.smallMaxReq fineCostModel :=
    Nat.le_trans (by decide : 68 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hPq := phaseCredit_w4PqxdhAccept_small fineCostModel_modelHyps (hasOpk := hasOpk)
    hold hnew hSmall
  have hBuild := phaseCredit_optStageEnv fineCostModel_modelHyps
    (W4OuterPeakSpec.phaseCredit_w4BobSessionBuild9_small fineCostModel_modelHyps hSm68)
  have hInner := phaseCredit_optStageEnv fineCostModel_modelHyps (hSpqr.seq hBuild)
  refine (hPq.seq hInner).mono ?_ ?_ ?_ (Nat.le_refl _)
  · unfold W4OuterPeakSpec.w4InitBobOuterCum9
    exact bob_wide_cum_le _ _ _
  · simp only [Nat.zero_add, Nat.add_zero]
    exact Nat.le_refl _
  · simp only [Nat.zero_add, Nat.add_zero, Nat.zero_max]
    exact Nat.le_refl _

theorem w4InitBobSpqrWide_fine_phaseCredit
    (F : ShaCompress) {x_res : DoReserveCall} (hasOpk : Bool)
    (x_spqr : InitialStateGhost) {ikmCap : Nat}
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec fineCostModel (W4InitBobSpqrWideEnv F x_res hasOpk x_spqr)
      (W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32)
      0 0 (max ikmCap 4224) :=
  (w4InitBobWide_small_fine_phaseCredit (hasOpk := hasOpk) hold hnew hSmall
    (w4SpqrInit32_fine_phaseCredit F x_spqr hspqrKey)).mono
    (Nat.le_refl _) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.le_refl 0, Nat.le_refl 0⟩)
    (p2a_bob_maxReq_le ikmCap)

theorem w4StageP2OverBobWide_dom_fine_phaseCredit
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (F : ShaCompress) {x_res : DoReserveCall} (hasOpk : Bool) (x_spqr : InitialStateGhost)
    {archPqCap archEncCap c_push r_push ikmCap : Nat}
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec fineCostModel
      (W4StageP2OverBobWideEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (8420940 + c_push + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32)
      (fineOptLarge archEncCap)
      (1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap)
      (max (max (max (max 208000 archPqCap) archEncCap) r_push) (max ikmCap 4224)) := by
  have hProm := phaseCredit_optStageEnv fineCostModel_modelHyps
    (promoteStateArchive_dom_fine_phaseCredit_tight hArchValid hArchEnc hPush)
  have hBob := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4InitBobSpqrWide_fine_phaseCredit F hasOpk x_spqr hold hnew hSmall hspqrKey)
  have hle : fineOptLarge archEncCap ≤
      1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap :=
    Nat.le_add_left _ _
  exact (hProm.seq hBob).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_of_eq (Nat.add_zero _))
    (Nat.max_le.mpr ⟨Nat.le_refl _, by simp only [Nat.add_zero]; exact hle⟩)
    (Nat.le_refl _)

private theorem p2a_split_cum_le (cs ck b1 b2 c : Nat) :
    cs + (ck + (cs + (cs + ((b1 + b2) + (cs + c))))) ≤ (4 * cs + ck) + b1 + b2 + c := by
  omega

private theorem p2a_split_live_le (ls lk : Nat) :
    ls + (lk + (ls + (ls + ls))) ≤ 4 * ls + lk := by
  omega

private theorem p2a_split_maxReq_le (rs rk ikmCap : Nat) :
    max rs (max rk (max rs (max rs (max (max ikmCap 4224) (max rs 192))))) ≤
      max (max rs rk) (max ikmCap 4224) := by
  let T := max (max rs rk) (max ikmCap 4224)
  have hsm : max rs rk ≤ T := Nat.le_max_left _ _
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) hsm
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) hsm
  have hb : max ikmCap 4224 ≤ T := Nat.le_max_right _ _
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hb)
  exact Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hrk, Nat.max_le.mpr ⟨hrs,
    Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hb, Nat.max_le.mpr ⟨hrs, h192⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathACliWide_splitDir_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap kpkFileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hKpkCap : ∀ n bs, rd files (pathOf kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap) :
    let smCap := max maxVal smallFileCap
    let kCap := max maxVal kpkFileCap
    let cs := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let ck := 488 + smallStorePollTightDeltaCum kCap maxEntries
    let ls := smallStorePollTightDeltaLive smCap maxEntries
    let lk := smallStorePollTightDeltaLive kCap maxEntries
    let ps := smallStorePollTightDeltaPeak smCap maxEntries
    let pk := smallStorePollTightDeltaPeak kCap maxEntries
    let rs := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let rk := max 16 (smallStorePollTightMaxReq kCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP2PathACliWideEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      ((4 * cs + ck) + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32 + 8674)
      (4 * ls + lk)
      (max ps (ls + max pk (lk + max ps (ls + max ps (ls + max ps ls)))))
      (max (max rs rk) (max ikmCap 4224)) := by
  dsimp only
  have hSpk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
      (fun bs hr => hSmallCap spkDir (by simp) _ bs hr))
  have hKpk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir (fun bs hr => hKpkCap _ bs hr))
  have hOptPk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_ite_nil hasOpk fun _ =>
      w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
        (fun bs hr => hSmallCap opkDir (by simp) _ bs hr))
  have hKp := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
      (fun bs hr => hSmallCap ownDir (by simp) _ bs hr))
  have hBob := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4InitBobSpqrWide_fine_phaseCredit F hasOpk x_spqr hold hnew hSmall hspqrKey)
  have hReg := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
      (fun bs hr => hSmallCap ownDir (by simp) _ bs hr))
  have h67 := (hReg.seq w4ErrTailWide_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h57 := (hBob.seq h67).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add _))
    (by simp only [Nat.zero_add, Nat.zero_max]; exact Nat.le_refl _)
    (Nat.le_refl _)
  have h47 := hKp.seq h57
  have h37 := hOptPk.seq h47
  have h27 := hKpk.seq h37
  exact (hSpk.seq h27).mono
    (p2a_split_cum_le _ _ _ _ _)
    (p2a_split_live_le _ _)
    (Nat.le_refl _)
    (p2a_split_maxReq_le _ _ _)

theorem w4StageP2PathACliWide_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP2PathACliWideEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      ((4 * c16 + c16) + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32 + 8674)
      (4 * l16 + l16)
      (max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16 l16)))))
      (max (max r16 r16) (max ikmCap 4224)) :=
  w4StageP2PathACliWide_splitDir_fine_phaseCredit hasOpk spkId kpkId opkId F x_spqr
    hdcSpk hdcKpk hdcOpk hdcOwn hdir hkeyName hregName hold hnew hSmall hspqrKey
    (fun d hd n bs hr => by
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact hSmallCap d (by simp) n bs hr
      · rcases List.mem_cons.mp hd1 with rfl | hd2
        · exact hSmallCap d (by simp) n bs hr
        · rcases List.mem_cons.mp hd2 with rfl | hd3
          · exact hSmallCap d (by simp) n bs hr
          · nomatch hd3)
    (fun n bs hr => hSmallCap kpkDir (by simp) n bs hr)

private theorem p2c_split_cum_le (cCur cLoop cs ck cOver cTail : Nat) :
    cCur + (cLoop + (cs + (ck + (cs + (cs + (cOver + (cs + cTail))))))) ≤
      cCur + cLoop + (4 * cs + ck) + cOver + cTail := by
  omega

private theorem p2c_split_live_le (ls lk lOver : Nat) :
    0 + (0 + (ls + (lk + (ls + (ls + (lOver + ls)))))) ≤ (4 * ls + lk) + lOver := by
  omega

private theorem p2c_split_maxReq_le (rCurAll rDec rTr rSerAll rs rk ikmCap : Nat) :
    max (max rCurAll 192)
      (max (max rDec rTr)
        (max rs (max rk (max rs (max rs
          (max (max rSerAll (max ikmCap 4224)) (max rs 192))))))) ≤
    max (max rCurAll (max rDec rTr))
      (max rSerAll (max (max rs rk) (max ikmCap 4224))) := by
  let T := max (max rCurAll (max rDec rTr))
    (max rSerAll (max (max rs rk) (max ikmCap 4224)))
  have hL : max rCurAll (max rDec rTr) ≤ T := Nat.le_max_left _ _
  have hR : max rSerAll (max (max rs rk) (max ikmCap 4224)) ≤ T := Nat.le_max_right _ _
  have h1 : rCurAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hL
  have h2 : max rDec rTr ≤ T := Nat.le_trans (Nat.le_max_right _ _) hL
  have h3 : rSerAll ≤ T := Nat.le_trans (Nat.le_max_left _ _) hR
  have h4 : max (max rs rk) (max ikmCap 4224) ≤ T := Nat.le_trans (Nat.le_max_right _ _) hR
  have hsm : max rs rk ≤ T := Nat.le_trans (Nat.le_max_left _ _) h4
  have hrs : rs ≤ T := Nat.le_trans (Nat.le_max_left _ _) hsm
  have hrk : rk ≤ T := Nat.le_trans (Nat.le_max_right _ _) hsm
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_right _ _) h4
  have h192 : 192 ≤ T :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hikm)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨h1, h192⟩,
     Nat.max_le.mpr ⟨h2,
       Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨hrk, Nat.max_le.mpr ⟨hrs,
         Nat.max_le.mpr ⟨hrs, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h3, hikm⟩,
           Nat.max_le.mpr ⟨hrs, h192⟩⟩⟩⟩⟩⟩⟩⟩

theorem w4StageP2PathCCliWide_splitDir_dom_fine_phaseCredit {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    {CurTrialFailEnv : List AllocEvent → Prop} {curPqCap c_cur p_cur r_cur : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap kpkFileCap : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hKpkCap : ∀ n bs, rd files (pathOf kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap) :
    let smCap := max maxVal smallFileCap
    let kCap := max maxVal kpkFileCap
    let cs := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let ck := 488 + smallStorePollTightDeltaCum kCap maxEntries
    let ls := smallStorePollTightDeltaLive smCap maxEntries
    let lk := smallStorePollTightDeltaLive kCap maxEntries
    let ps := smallStorePollTightDeltaPeak smCap maxEntries
    let pk := smallStorePollTightDeltaPeak kCap maxEntries
    let rs := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let rk := max 16 (smallStorePollTightMaxReq kCap maxEntries)
    let lOver := fineOptLarge archEncCap
    let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
    let pRest := max ps (ls + max pk (lk + max ps (ls + max ps
      (ls + max pOver (lOver + max ps ls)))))
    PhaseCreditSpec fineCostModel
      (W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((8277456 + c_cur + 8674) + 4 * (c_dec + c_tr) +
        (4 * cs + ck) + (8420940 + c_push + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32) + 8674)
      ((4 * ls + lk) + lOver)
      (max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pRest))
      (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
        (max (max (max (max 208000 archPqCap) archEncCap) r_push)
          (max (max rs rk) (max ikmCap 4224)))) := by
  dsimp only
  have hCur := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit hCurDom hCurTrial)
  have hLoop := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop)
  have hSpk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4KeyIdSmallStoreStep16_fine_phaseCredit spkId hdcSpk hdir
      (fun bs hr => hSmallCap spkDir (by simp) _ bs hr))
  have hKpk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4KeyIdSmallStoreStep16_fine_phaseCredit kpkId hdcKpk hdir (fun bs hr => hKpkCap _ bs hr))
  have hOptPk := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_ite_nil hasOpk fun _ =>
      w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
        (fun bs hr => hSmallCap opkDir (by simp) _ bs hr))
  have hKp := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hkeyName
      (fun bs hr => hSmallCap ownDir (by simp) _ bs hr))
  have hOver := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP2OverBobWide_dom_fine_phaseCredit g_arch r_arch F hasOpk x_spqr
      hArchValid hArchEnc hPush hold hnew hSmall hspqrKey)
  have hReg := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep16_fine_phaseCredit hdcOwn hdir hregName
      (fun bs hr => hSmallCap ownDir (by simp) _ bs hr))
  have h89 := (hReg.seq w4ErrTailWide_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
    (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h79 := hOver.seq h89
  have h69 := hKp.seq h79
  have h59 := hOptPk.seq h69
  have h49 := hKpk.seq h59
  have h39 := hSpk.seq h49
  have h29 := hLoop.seq h39
  exact (hCur.seq h29).mono
    (p2c_split_cum_le _ _ _ _ _ _)
    (p2c_split_live_le _ _ _)
    (by simp only [Nat.zero_add]; exact Nat.le_refl _)
    (p2c_split_maxReq_le _ _ _ _ _ _ _)

theorem w4StageP2PathCCliWide_dom_fine_phaseCredit {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    {CurTrialFailEnv : List AllocEvent → Prop} {curPqCap c_cur p_cur r_cur : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push archPqCap archEncCap : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal smallFileCap : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom curPqCap ses_cur)
    (hCurTrial : PhaseCreditSpec fineCostModel CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hArchValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses)
    (hArchEnc : (encodeRecord r_arch).length ≤ archEncCap)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec fineCostModel (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec fineCostModel (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel VecPushEnv c_push 0 0 r_push)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hSmallCap : ∀ d ∈ [spkDir, kpkDir, opkDir, ownDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap) :
    let smCap := max maxVal smallFileCap
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let lOver := fineOptLarge archEncCap
    let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
    let pRest := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    PhaseCreditSpec fineCostModel
      (W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((8277456 + c_cur + 8674) + 4 * (c_dec + c_tr) +
        (4 * c16 + c16) + (8420940 + c_push + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32) + 8674)
      ((4 * l16 + l16) + lOver)
      (max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pRest))
      (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
        (max (max (max (max 208000 archPqCap) archEncCap) r_push)
          (max (max r16 r16) (max ikmCap 4224)))) :=
  w4StageP2PathCCliWide_splitDir_dom_fine_phaseCredit G_cur st_cur g_arch r_arch
    hasOpk spkId kpkId opkId F x_spqr hCurDom hCurTrial hArchValid hArchEnc
    hlen4 hl_le_p hDec hTrial hDrop hPush hdcSpk hdcKpk hdcOpk hdcOwn hdir
    hkeyName hregName hold hnew hSmall hspqrKey
    (fun d hd n bs hr => by
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact hSmallCap d (by simp) n bs hr
      · rcases List.mem_cons.mp hd1 with rfl | hd2
        · exact hSmallCap d (by simp) n bs hr
        · rcases List.mem_cons.mp hd2 with rfl | hd3
          · exact hSmallCap d (by simp) n bs hr
          · nomatch hd3)
    (fun n bs hr => hSmallCap kpkDir (by simp) n bs hr)

/-! ### Widened Stage P3 (`CloneEnv → OptStageEnv TryDecEnv → W4ErrTailWideEnv`) Bounds -/

theorem w4StageP3Wide_fine_phaseCredit_tight
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {c_cl l_cl p_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec fineCostModel CloneEnv c_cl l_cl p_cl r_cl)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv CloneEnv TryDecEnv)
      (c_cl + c_td + 8674)
      (l_cl + l_td)
      (max p_cl (l_cl + max p_td l_td))
      (max r_cl (max r_td 192)) := by
  have hOptTd := phaseCredit_optStageEnv fineCostModel_modelHyps hTd
  have hTdTail := (hOptTd.seq w4ErrTailWide_fine_phaseCredit_tight).mono
    (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero l_td))
    (Nat.le_of_eq (congrArg (max p_td) (Nat.add_zero l_td))) (Nat.le_refl _)
  exact (hClone.seq hTdTail).mono
    (Nat.le_of_eq (Nat.add_assoc c_cl c_td 8674).symm)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem w4StageP3Wide_zeroLive_fine_phaseCredit_tight
    {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {c_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec fineCostModel CloneEnv c_cl 0 0 r_cl)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv CloneEnv TryDecEnv)
      (c_cl + c_td + 8674)
      l_td
      (max p_td l_td)
      (max r_cl (max r_td 192)) :=
  (w4StageP3Wide_fine_phaseCredit_tight hClone hTd).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_td))
    (by simp only [Nat.zero_add, Nat.zero_max]; exact Nat.le_refl _)
    (Nat.le_refl _)

/-- Path B Stage P3 bound under `SessionCloneDom pqCap` (`Δcum = 8,277,456 + c_td + 8,674`). -/
theorem w4StageP3Wide_domB_fine_phaseCredit {pqCap c_td l_td p_td r_td : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TryDecEnv : List AllocEvent → Prop}
    (hgv : SessionGhostValid G ses) (hdom : SessionCloneDom pqCap ses)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv (SegCloneEnv G ses.state) TryDecEnv)
      (8277456 + c_td + 8674)
      ((1080975 + fineOptLarge pqCap) + l_td)
      (max (1080975 + fineOptLarge pqCap) ((1080975 + fineOptLarge pqCap) + max p_td l_td))
      (max (max 208000 pqCap) (max r_td 192)) :=
  w4StageP3Wide_fine_phaseCredit_tight (sessionClone_dom_fine_phaseCredit_tight hgv hdom) hTd

/-- Paths A & C Stage P3 bound under `FreshBobCloneDom bobPqCap` with `bobPqCap ≤ 16,384`
(`Δcum = 36,295 + c_td + 8,674`, with `Δlive` and `Δpeak` unchanged from `TryDecEnv`). -/
theorem w4StageP3Wide_freshBob16K_fine_phaseCredit {bobPqCap c_td l_td p_td r_td : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    {TryDecEnv : List AllocEvent → Prop}
    (hbob : FreshBobCloneDom bobPqCap G ses) (hpq : bobPqCap ≤ 16384)
    (hTd : PhaseCreditSpec fineCostModel TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec fineCostModel (W4StageP3WideEnv (SegCloneEnv G ses.state) TryDecEnv)
      (36295 + c_td + 8674)
      l_td
      (max p_td l_td)
      (max 208000 (max r_td 192)) :=
  w4StageP3Wide_zeroLive_fine_phaseCredit_tight (sessionClone_freshBob16K_fine_phaseCredit hbob hpq) hTd

/-! ### Widened Stage P4 (`Matched`, `PathA`, `PathC`) Early-Reject Bounds -/

theorem w4StageP4MatchedCliWide_dom_fine_phaseCredit
    {rd : ReadRule} {files : FsFiles}
    {peersDir sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hPeersCap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4MatchedCliWideEnv rd files peersDir sessDir peer g_rec r_rec)
      (c32 + cSt0) (l32 + lSt0) (max p32 (l32 + pSt0)) (max r32 rSt0) := by
  dsimp only
  have hSave := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer hPeersCap)
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc))
  exact hSave.seq hStore

private theorem p4_split_maxReq_le (r32s r32k r16s rSt : Nat) :
    max r32s (max r32k (max r16s rSt)) ≤ max (max r32s r32k) (max r16s rSt) := by
  have hsm : max r32s r32k ≤ max (max r32s r32k) (max r16s rSt) := Nat.le_max_left _ _
  exact Nat.max_le.mpr
    ⟨Nat.le_trans (Nat.le_max_left _ _) hsm,
     Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_right _ _) hsm, Nat.le_max_right _ _⟩⟩

theorem w4StageP4PathACliWide_splitDir_dom_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap kpkFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hKpkCap : ∀ n bs, rd files (pathOf kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let kCap := max maxVal kpkFileCap
    let c32s := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let c32k := 738 + smallStorePollTightDeltaCum kCap maxEntries
    let ls := smallStorePollTightDeltaLive smCap maxEntries
    let lk := smallStorePollTightDeltaLive kCap maxEntries
    let ps := smallStorePollTightDeltaPeak smCap maxEntries
    let pk := smallStorePollTightDeltaPeak kCap maxEntries
    let r32s := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let r32k := max 32 (smallStorePollTightMaxReq kCap maxEntries)
    let c16s := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let r16s := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        g_rec r_rec)
      (c32s + c32k + c16s + cSt0)
      (ls + lk + ls + lSt0)
      (max ps (ls + max pk (lk + max ps (ls + pSt0))))
      (max (max r32s r32k) (max r16s rSt0)) := by
  dsimp only
  have hSave := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
      (fun bs hr => hSmallCap peersDir (by simp) _ bs hr))
  have hMark := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName (fun bs hr => hKpkCap _ bs hr))
  have hRem := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_ite_nil hasOpk fun _ =>
      w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
        (fun bs hr => hSmallCap opkDir (by simp) _ bs hr))
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (w4SessStoreStep_dom_fine_phaseCredit hdcSess hpeer hValid hEnc))
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_split_maxReq_le _ _ _ _)

theorem w4StageP4PathACliWide_dom_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal smallFileCap pqCap encCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r_rec).length ≤ encCap) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
    let lSt0 := sessStorePollTightDeltaLive (fineOptLarge encCap) maxEntries
    let pSt0 := sessStorePollTightDeltaPeak
      (1080975 + fineOptLarge pqCap + fineOptLarge encCap) maxEntries
    let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        g_rec r_rec)
      (c32 + c32 + c16 + cSt0)
      (l32 + l32 + l16 + lSt0)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt0))))
      (max (max r32 r32) (max r16 rSt0)) :=
  w4StageP4PathACliWide_splitDir_dom_fine_phaseCredit hasOpk opkId g_rec r_rec
    hdcPeers hdcKpk hdcOpk hdcSess hdir hpeer hkpkName
    (fun d hd n bs hr => by
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact hSmallCap d (by simp) n bs hr
      · rcases List.mem_cons.mp hd1 with rfl | hd2
        · exact hSmallCap d (by simp) n bs hr
        · nomatch hd2)
    (fun n bs hr => hSmallCap kpkDir (by simp) n bs hr) hValid hEnc

theorem w4StageP4PathCCliWide_splitDir_freshBob_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal smallFileCap kpkFileCap bobPqCap prevEncCap totalPrev1Cap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hKpkCap : ∀ n bs, rd files (pathOf kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap)
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G sess enc) :
    let smCap := max maxVal smallFileCap
    let kCap := max maxVal kpkFileCap
    let c32s := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let c32k := 738 + smallStorePollTightDeltaCum kCap maxEntries
    let ls := smallStorePollTightDeltaLive smCap maxEntries
    let lk := smallStorePollTightDeltaLive kCap maxEntries
    let ps := smallStorePollTightDeltaPeak smCap maxEntries
    let pk := smallStorePollTightDeltaPeak kCap maxEntries
    let r32s := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let r32k := max 32 (smallStorePollTightMaxReq kCap maxEntries)
    let c16s := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let r16s := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
    let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
    let pSt1 := sessStorePollTightDeltaPeak
      (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
    let rSt1 := max 32
      (sessStorePollMaxReq
        (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        G sess enc)
      (c32s + c32k + c16s + cSt1)
      (ls + lk + ls + lSt1)
      (max ps (ls + max pk (lk + max ps (ls + pSt1))))
      (max (max r32s r32k) (max r16s rSt1)) := by
  dsimp only
  have hSave := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4PeerSmallStoreStep32_fine_phaseCredit hdcPeers hdir hpeer
      (fun bs hr => hSmallCap peersDir (by simp) _ bs hr))
  have hMark := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4SmallStoreStep32_fine_phaseCredit hdcKpk hdir hkpkName (fun bs hr => hKpkCap _ bs hr))
  have hRem := phaseCredit_optStageEnv fineCostModel_modelHyps
    (phaseCreditSpec_ite_nil hasOpk fun _ =>
      w4KeyIdSmallStoreStep16_fine_phaseCredit opkId hdcOpk hdir
        (fun bs hr => hSmallCap opkDir (by simp) _ bs hr))
  have hStore := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (w4SessStorePrev1Step_freshBob_fine_phaseCredit hdcSess hpeer hbob))
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (by simp only [Nat.add_assoc]; exact Nat.le_refl _)
    (Nat.le_refl _)
    (p4_split_maxReq_le _ _ _ _)

theorem w4StageP4PathCCliWide_freshBob_fine_phaseCredit
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal smallFileCap bobPqCap prevEncCap totalPrev1Cap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hSmallCap : ∀ d ∈ [peersDir, kpkDir, opkDir],
      ∀ n bs, rd files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap)
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G sess enc) :
    let smCap := max maxVal smallFileCap
    let c32 := 738 + smallStorePollTightDeltaCum smCap maxEntries
    let l32 := smallStorePollTightDeltaLive smCap maxEntries
    let p32 := smallStorePollTightDeltaPeak smCap maxEntries
    let r32 := max 32 (smallStorePollTightMaxReq smCap maxEntries)
    let c16 := 488 + smallStorePollTightDeltaCum smCap maxEntries
    let l16 := smallStorePollTightDeltaLive smCap maxEntries
    let p16 := smallStorePollTightDeltaPeak smCap maxEntries
    let r16 := max 16 (smallStorePollTightMaxReq smCap maxEntries)
    let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
    let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
    let pSt1 := sessStorePollTightDeltaPeak
      (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
    let rSt1 := max 32
      (sessStorePollMaxReq
        (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
    PhaseCreditSpec fineCostModel
      (W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        G sess enc)
      (c32 + c32 + c16 + cSt1)
      (l32 + l32 + l16 + lSt1)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt1))))
      (max (max r32 r32) (max r16 rSt1)) :=
  w4StageP4PathCCliWide_splitDir_freshBob_fine_phaseCredit hasOpk opkId G sess enc
    hdcPeers hdcKpk hdcOpk hdcSess hdir hpeer hkpkName
    (fun d hd n bs hr => by
      rcases List.mem_cons.mp hd with rfl | hd1
      · exact hSmallCap d (by simp) n bs hr
      · rcases List.mem_cons.mp hd1 with rfl | hd2
        · exact hSmallCap d (by simp) n bs hr
        · nomatch hd2)
    (fun n bs hr => hSmallCap kpkDir (by simp) n bs hr) hbob

/-! ### Closed-Form Widened 4-Arm Slot Formulas & `PhaseCreditSpec`s -/

/-- Per-directory domain bundle (`[ownDir, peersDir, spkDir, opkDir] ≤ smallFileCap` vs
`kpkDir ≤ kpkFileCap`) for `W4DecryptPrekeySplitWideSlotEnv`. -/
structure W4DecryptPrekeySplitWideDirDom {α : Type} (P : W4DecryptPrekeySlotParams α)
    (sessFileCap smallFileCap kpkFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat) : Prop where
  peer_len : P.peer.name.bytes.length ≤ 40
  ownKey_len : P.ownKeyName.length ≤ 64
  ownReg_len : P.ownRegName.length ≤ 64
  kpkMark_len : P.kpkMarkName.length ≤ 64
  res_old : P.x_res.cap.toNat ≤ ikmCap
  res_new : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap
  ikm_small : max ikmCap 1569 ≤ 135167
  spqr_key : P.x_spqr.p.authKey.length ≤ 32
  sess_cap : ∀ bs, P.rd P.files (pathOf P.sessDir.path (addressText P.peer.val)) = .ok bs →
    bs.length ≤ sessFileCap
  small_cap : ∀ d ∈ [P.ownDir, P.peersDir, P.spkDir, P.opkDir],
    ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  kpk_cap : ∀ n bs, P.rd P.files (pathOf P.kpkDir.path n) = .ok bs → bs.length ≤ kpkFileCap
  cur_dom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = P.st_cur ∧ SessionGhostValid P.G_cur ses_cur ∧
        SessionCloneDom curPqCap ses_cur
  arch_valid : ∀ G ses, P.g_arch.cur = some G → P.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses
  arch_enc : (encodeRecord P.r_arch).length ≤ archEncCap
  out0_valid : ∀ G ses, P.g_out0.cur = some G → P.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom out0PqCap ses
  out0_enc : (encodeRecord P.r_out0).length ≤ out0EncCap
  out1_freshBob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap P.G_out1 P.sess_out1 P.enc_prev1
  trials_len4 : P.archivedTrials.length ≤ 4

/-- Uniform `smallFileCap` (`kpkFileCap := smallFileCap`) lift from `W4DecryptPrekeyTightDom`. -/
theorem W4DecryptPrekeyTightDom.toSplitWideDirDom {α : Type} {P : W4DecryptPrekeySlotParams α}
    {sessFileCap smallFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat}
    (h : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap) :
    W4DecryptPrekeySplitWideDirDom P sessFileCap smallFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap where
  peer_len := h.peer_len
  ownKey_len := h.ownKey_len
  ownReg_len := h.ownReg_len
  kpkMark_len := h.kpkMark_len
  res_old := h.res_old
  res_new := h.res_new
  ikm_small := h.ikm_small
  spqr_key := h.spqr_key
  sess_cap := h.sess_cap
  small_cap := fun d hd n bs hr => by
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact h.small_cap P.ownDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact h.small_cap P.peersDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact h.small_cap P.spkDir (by simp) n bs hr
        · rcases List.mem_cons.mp hd3 with rfl | hd4
          · exact h.small_cap P.opkDir (by simp) n bs hr
          · nomatch hd4
  kpk_cap := fun n bs hr => h.small_cap P.kpkDir (by simp) n bs hr
  cur_dom := h.cur_dom
  arch_valid := h.arch_valid
  arch_enc := h.arch_enc
  out0_valid := h.out0_valid
  out0_enc := h.out0_enc
  out1_freshBob := h.out1_freshBob
  trials_len4 := h.trials_len4

/-- Closed-form `Δcum` across all 4 arms of `W4DecryptPrekeySplitWideSlotEnv`, parameterized by
`(smallCap, kpkCap)` and `(c_clB, c_clAC)` (`8,277,456` on Path B, `36,295` on Paths A & C). -/
def w4DecryptPrekeySplitWideDirCum
    (sessCap smallCap kpkCap maxEntries deserCum c_cur c_dec c_tr c_push
     c_clB c_tdB c_clAC c_tdAC ikmCap : Nat) : Nat :=
  let cL := 488 + sessLoadPollTightDeltaCum sessCap deserCum
  let c32s := 738 + smallStorePollTightDeltaCum smallCap maxEntries
  let c32k := 738 + smallStorePollTightDeltaCum kpkCap maxEntries
  let c16s := 488 + smallStorePollTightDeltaCum smallCap maxEntries
  let c16k := 488 + smallStorePollTightDeltaCum kpkCap maxEntries
  let cP1Ok := cL + c32s
  let cUntr := cP1Ok + 9619
  let cSt0 := 738 + sessStorePollTightDeltaCum 8420940 maxEntries
  let cSt1 := 738 + sessStorePollTightDeltaCum 1184912 maxEntries
  let cPathB := cP1Ok + (2345 + (4 * (c_dec + c_tr) + (8420940 + c_push))) +
    (c_clB + c_tdB + 8674) + (c32s + cSt0)
  let cPathA := cP1Ok + ((4 * c16s + c16k) + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32 + 8674) +
    (c_clAC + c_tdAC + 8674) + (c32s + c32k + c16s + cSt0)
  let cPathC := cP1Ok +
    ((8277456 + c_cur + 8674) + 4 * (c_dec + c_tr) +
      (4 * c16s + c16k) + (8420940 + c_push + W4OuterPeakSpec.w4InitBobOuterCum9 ikmCap + w4SpqrInitCum 32) + 8674) +
    (c_clAC + c_tdAC + 8674) + (c32s + c32k + c16s + cSt1)
  max (max cUntr cPathB) (max cPathA cPathC)

/-- Closed-form `Δlive` across all 4 arms of `W4DecryptPrekeySplitWideSlotEnv` (`l_clAC = 0`). -/
def w4DecryptPrekeySplitWideDirLive
    (sessCap smallCap kpkCap maxEntries deserLive archEncCap out0EncCap totalPrev1Cap
     l_clB l_tdB l_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let ls := smallStorePollTightDeltaLive smallCap maxEntries
  let lk := smallStorePollTightDeltaLive kpkCap maxEntries
  let lP1 := lL + ls
  let lSt0 := sessStorePollTightDeltaLive (fineOptLarge out0EncCap) maxEntries
  let lSt1 := sessStorePollTightDeltaLive (fineOptLarge totalPrev1Cap) maxEntries
  let lUntr := lP1
  let lPathB := lP1 + fineOptLarge archEncCap + (l_clB + l_tdB) + (ls + lSt0)
  let lPathA := lP1 + (4 * ls + lk) + l_tdAC + (ls + lk + ls + lSt0)
  let lPathC := lP1 + ((4 * ls + lk) + fineOptLarge archEncCap) + l_tdAC + (ls + lk + ls + lSt1)
  max (max lUntr lPathB) (max lPathA lPathC)

/-- Closed-form sequential `Δpeak` before clamping with `Δlive` (`l_clAC = p_clAC = 0`). -/
def w4DecryptPrekeySplitWideDirRawPeak
    (sessCap smallCap kpkCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  let lL := sessLoadPollTightDeltaLive sessCap deserLive
  let pL := sessLoadPollTightDeltaPeak sessCap deserPeak
  let ls := smallStorePollTightDeltaLive smallCap maxEntries
  let ps := smallStorePollTightDeltaPeak smallCap maxEntries
  let lk := smallStorePollTightDeltaLive kpkCap maxEntries
  let pk := smallStorePollTightDeltaPeak kpkCap maxEntries
  let lP1 := lL + ls
  let pP1 := max pL (lL + max ps ls)
  let pSt0 := sessStorePollTightDeltaPeak
    (1080975 + fineOptLarge out0PqCap + fineOptLarge out0EncCap) maxEntries
  let pSt1 := sessStorePollTightDeltaPeak
    (fineOptLarge bobPqCap + fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap) maxEntries
  let pOver := 1080975 + fineOptLarge archPqCap + fineOptLarge archEncCap
  let lOver := fineOptLarge archEncCap
  let pPeakB :=
    let pP2B := max (p_dec + p_tr) pOver
    let pP3B := max p_clB (l_clB + max p_tdB l_tdB)
    let pP4B := max ps (ls + pSt0)
    max pP1 (lP1 + max pP2B (lOver + max pP3B ((l_clB + l_tdB) + pP4B)))
  let pPeakA :=
    let pP2A := max ps (ls + max pk (lk + max ps (ls + max ps (ls + max ps ls))))
    let pP3A := max p_tdAC l_tdAC
    let pP4A := max ps (ls + max pk (lk + max ps (ls + pSt0)))
    max pP1 (lP1 + max pP2A ((4 * ls + lk) + max pP3A (l_tdAC + pP4A)))
  let pPeakC :=
    let pP2Store := max ps (ls + max pk (lk + max ps (ls + max ps
      (ls + max pOver (lOver + max ps ls)))))
    let pP2C := max (1080975 + fineOptLarge curPqCap + p_cur) (max (p_dec + p_tr) pP2Store)
    let pP3C := max p_tdAC l_tdAC
    let pP4C := max ps (ls + max pk (lk + max ps (ls + pSt1)))
    max pP1 (lP1 + max pP2C (((4 * ls + lk) + lOver) + max pP3C (l_tdAC + pP4C)))
  max (max pP1 pPeakB) (max pPeakA pPeakC)

/-- Closed-form `Δpeak` (`max rawPeak live` so `live ≤ peak` holds by `Nat.le_max_right`). -/
def w4DecryptPrekeySplitWideDirPeak
    (sessCap smallCap kpkCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  max
    (w4DecryptPrekeySplitWideDirRawPeak sessCap smallCap kpkCap maxEntries deserLive deserPeak
      curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
      p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC)
    (w4DecryptPrekeySplitWideDirLive sessCap smallCap kpkCap maxEntries deserLive
      archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC)

/-- Closed-form `maxReq` across all 4 arms of `W4DecryptPrekeySplitWideSlotEnv`. -/
def w4DecryptPrekeySplitWideDirMaxReq
    (sessCap smallCap kpkCap maxEntries deserMaxReq
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap : Nat) : Nat :=
  let rL := max 24 (sessLoadPollTightMaxReq sessCap deserMaxReq)
  let r32s := max 32 (smallStorePollTightMaxReq smallCap maxEntries)
  let r32k := max 32 (smallStorePollTightMaxReq kpkCap maxEntries)
  let r16s := max 16 (smallStorePollTightMaxReq smallCap maxEntries)
  let r16k := max 16 (smallStorePollTightMaxReq kpkCap maxEntries)
  let rSm := max (max r32s r32k) (max r16s r16k)
  let rSt0 := max 32 (sessStorePollMaxReq (max (max 208000 out0PqCap) out0EncCap) maxEntries)
  let rSt1 := max 32
    (sessStorePollMaxReq
      (max (max 208000 bobPqCap) (max (max 24 prevEncCap) totalPrev1Cap)) maxEntries)
  max (max rL (max rSm 40))
    (max (max (max (max 208000 curPqCap) r_cur) (max r_dec r_tr))
      (max (max (max (max 208000 archPqCap) archEncCap) r_push)
        (max (max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192))
          (max (max ikmCap 4224) (max rSt0 rSt1)))))

theorem w4DecryptPrekeySplitWideDir_live_le_peak
    (sessCap smallCap kpkCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC : Nat) :
    w4DecryptPrekeySplitWideDirLive sessCap smallCap kpkCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC ≤
      w4DecryptPrekeySplitWideDirPeak sessCap smallCap kpkCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC :=
  Nat.le_max_right _ _

/-- Uniform `smallCap` (`kpkCap := smallCap`) + standard `SessionCloneDom out0PqCap` (`8,277,456` B) /
`FreshBobCloneDom 16384` (`36,295` B) abbreviations. -/
abbrev w4DecryptPrekeySplitWideTightCum
    (sessCap smallCap maxEntries deserCum c_cur c_dec c_tr c_push
     c_tdB c_tdAC ikmCap : Nat) : Nat :=
  w4DecryptPrekeySplitWideDirCum sessCap smallCap smallCap maxEntries deserCum
    c_cur c_dec c_tr c_push 8277456 c_tdB 36295 c_tdAC ikmCap

abbrev w4DecryptPrekeySplitWideTightLive
    (sessCap smallCap maxEntries deserLive archEncCap out0PqCap out0EncCap totalPrev1Cap
     l_tdB l_tdAC : Nat) : Nat :=
  w4DecryptPrekeySplitWideDirLive sessCap smallCap smallCap maxEntries deserLive
    archEncCap out0EncCap totalPrev1Cap (1080975 + fineOptLarge out0PqCap) l_tdB l_tdAC

abbrev w4DecryptPrekeySplitWideTightPeak
    (sessCap smallCap maxEntries deserLive deserPeak
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     p_cur p_dec p_tr l_tdB p_tdB l_tdAC p_tdAC : Nat) : Nat :=
  w4DecryptPrekeySplitWideDirPeak sessCap smallCap smallCap maxEntries deserLive deserPeak
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    p_cur p_dec p_tr
    (1080975 + fineOptLarge out0PqCap) (1080975 + fineOptLarge out0PqCap)
    l_tdB p_tdB l_tdAC p_tdAC

abbrev w4DecryptPrekeySplitWideTightMaxReq
    (sessCap smallCap maxEntries deserMaxReq
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap
     r_cur r_dec r_tr r_push r_tdB r_tdAC ikmCap : Nat) : Nat :=
  w4DecryptPrekeySplitWideDirMaxReq sessCap smallCap smallCap maxEntries deserMaxReq
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    r_cur r_dec r_tr r_push (max 208000 out0PqCap) 208000 r_tdB r_tdAC ikmCap

private theorem wideMaxReq_untr_le (rL r32s r32k r16s r16k rRest : Nat) :
    max rL (max r32s 40) ≤
      max (max rL (max (max (max r32s r32k) (max r16s r16k)) 40)) rRest := by
  let rSm := max (max r32s r32k) (max r16s r16k)
  let T := max (max rL (max rSm 40)) rRest
  have hA : max rL (max rSm 40) ≤ T := Nat.le_max_left _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hrSm : rSm ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr32s : r32s ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hrSm)
  have h40 : 40 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  exact Nat.max_le.mpr ⟨hrL, Nat.max_le.mpr ⟨hr32s, h40⟩⟩

private theorem wideMaxReq_B_le
    (rL r32s r32k r16s r16k rCur r_dec r_tr rArch r_clB r_clAC r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32s)
      (max (max (max r_dec r_tr) rArch)
        (max (max r_clB (max r_tdB 192)) (max r32s rSt0))) ≤
    max (max rL (max (max (max r32s r32k) (max r16s r16k)) 40))
      (max (max rCur (max r_dec r_tr))
        (max rArch
          (max (max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192))
            (max rIkm (max rSt0 rSt1))))) := by
  let rSm := max (max r32s r32k) (max r16s r16k)
  let rP3All := max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192)
  let T := max (max rL (max rSm 40))
    (max (max rCur (max r_dec r_tr))
      (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max rSm 40) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max rSm 40))
    (max (max rCur (max r_dec r_tr)) (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hrSm : rSm ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr32s : r32s ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) hrSm)
  have hdt : max r_dec r_tr ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hB)
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have hP3All : rP3All ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hP3B : max r_clB (max r_tdB 192) ≤ T :=
    Nat.le_trans
      (max_mono (Nat.le_max_left r_clB r_clAC)
        (max_mono (Nat.le_max_left r_tdB r_tdAC) (Nat.le_refl 192)))
      hP3All
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRR))
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32s⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hdt, hArch⟩,
       Nat.max_le.mpr ⟨hP3B, Nat.max_le.mpr ⟨hr32s, hrSt0⟩⟩⟩⟩

private theorem wideMaxReq_A_le
    (rL r32s r32k r16s r16k rCurDt rArch r_clB r_clAC r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32s)
      (max (max (max r16s r16k) rIkm)
        (max (max r_clAC (max r_tdAC 192)) (max (max r32s r32k) (max r16s rSt0)))) ≤
    max (max rL (max (max (max r32s r32k) (max r16s r16k)) 40))
      (max rCurDt
        (max rArch
          (max (max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192))
            (max rIkm (max rSt0 rSt1))))) := by
  let rSm := max (max r32s r32k) (max r16s r16k)
  let rP3All := max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192)
  let T := max (max rL (max rSm 40))
    (max rCurDt (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max rSm 40) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max rSm 40))
    (max rCurDt (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hrSm : rSm ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr32All : max r32s r32k ≤ T := Nat.le_trans (Nat.le_max_left _ _) hrSm
  have hr16All : max r16s r16k ≤ T := Nat.le_trans (Nat.le_max_right _ _) hrSm
  have hr32s : r32s ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr32All
  have hr16s : r16s ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr16All
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have hP3All : rP3All ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hP3AC : max r_clAC (max r_tdAC 192) ≤ T :=
    Nat.le_trans
      (max_mono (Nat.le_max_right r_clB r_clAC)
        (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)))
      hP3All
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32s⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr16All, hrIkm⟩,
       Nat.max_le.mpr ⟨hP3AC,
         Nat.max_le.mpr ⟨hr32All, Nat.max_le.mpr ⟨hr16s, hrSt0⟩⟩⟩⟩⟩

private theorem wideMaxReq_C_le
    (rL r32s r32k r16s r16k rCurDt rArch r_clB r_clAC r_tdB r_tdAC rIkm rSt0 rSt1 : Nat) :
    max (max rL r32s)
      (max (max rCurDt (max rArch (max (max r16s r16k) rIkm)))
        (max (max r_clAC (max r_tdAC 192)) (max (max r32s r32k) (max r16s rSt1)))) ≤
    max (max rL (max (max (max r32s r32k) (max r16s r16k)) 40))
      (max rCurDt
        (max rArch
          (max (max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192))
            (max rIkm (max rSt0 rSt1))))) := by
  let rSm := max (max r32s r32k) (max r16s r16k)
  let rP3All := max (max r_clB r_clAC) (max (max r_tdB r_tdAC) 192)
  let T := max (max rL (max rSm 40))
    (max rCurDt (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hA : max rL (max rSm 40) ≤ T := Nat.le_max_left _ _
  have hB := Nat.le_max_right (max rL (max rSm 40))
    (max rCurDt (max rArch (max rP3All (max rIkm (max rSt0 rSt1)))))
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hrSm : rSm ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hr32All : max r32s r32k ≤ T := Nat.le_trans (Nat.le_max_left _ _) hrSm
  have hr16All : max r16s r16k ≤ T := Nat.le_trans (Nat.le_max_right _ _) hrSm
  have hr32s : r32s ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr32All
  have hr16s : r16s ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr16All
  have hCur : rCurDt ≤ T := Nat.le_trans (Nat.le_max_left _ _) hB
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hArch : rArch ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have hP3All : rP3All ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hP3AC : max r_clAC (max r_tdAC 192) ≤ T :=
    Nat.le_trans
      (max_mono (Nat.le_max_right r_clB r_clAC)
        (max_mono (Nat.le_max_right r_tdB r_tdAC) (Nat.le_refl 192)))
      hP3All
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hrIkm : rIkm ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt1 : rSt1 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32s⟩,
     Nat.max_le.mpr
       ⟨Nat.max_le.mpr ⟨hCur, Nat.max_le.mpr ⟨hArch, Nat.max_le.mpr ⟨hr16All, hrIkm⟩⟩⟩,
        Nat.max_le.mpr ⟨hP3AC,
          Nat.max_le.mpr ⟨hr32All, Nat.max_le.mpr ⟨hr16s, hrSt1⟩⟩⟩⟩⟩

/-- Tight `PhaseCreditSpec fineCostModel` for `W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC`
with per-directory `(smallFileCap, kpkFileCap)` caps and split Stage P3 `(CloneB, CloneAC)` bounds. -/
theorem w4DecryptPrekeySplitWideSlot_splitDir_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC TryDecAC : List AllocEvent → Prop}
    {maxDir maxEntries maxVal sessFileCap smallFileCap kpkFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_clB l_clB p_clB r_clB c_clAC r_clAC
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeySplitWideDirDom P sessFileCap smallFileCap kpkFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hCloneB : PhaseCreditSpec fineCostModel CloneB c_clB l_clB p_clB r_clB)
    (hCloneAC : PhaseCreditSpec fineCostModel CloneAC c_clAC 0 0 r_clAC)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    let kCap := max maxVal kpkFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideDirCum sCap smCap kCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_clB c_tdB c_clAC c_tdAC ikmCap)
      (w4DecryptPrekeySplitWideDirLive sCap smCap kCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC)
      (w4DecryptPrekeySplitWideDirPeak sCap smCap kCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitWideDirMaxReq sCap smCap kCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap) := by
  dsimp only
  set sCap := max maxVal sessFileCap
  set smCap := max maxVal smallFileCap
  set kCap := max maxVal kpkFileCap
  have hPeersCap : ∀ bs, P.rd P.files (pathOf P.peersDir.path (addressText P.peer.val)) = .ok bs →
      bs.length ≤ smallFileCap :=
    fun bs hr => hDom.small_cap P.peersDir (by simp) _ bs hr
  have hSmallP2 : ∀ d ∈ [P.spkDir, P.opkDir, P.ownDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.spkDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.opkDir (by simp) n bs hr
      · rcases List.mem_cons.mp hd2 with rfl | hd3
        · exact hDom.small_cap P.ownDir (by simp) n bs hr
        · nomatch hd3
  have hSmallP4 : ∀ d ∈ [P.peersDir, P.opkDir],
      ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap := by
    intro d hd n bs hr
    rcases List.mem_cons.mp hd with rfl | hd1
    · exact hDom.small_cap P.peersDir (by simp) n bs hr
    · rcases List.mem_cons.mp hd1 with rfl | hd2
      · exact hDom.small_cap P.opkDir (by simp) n bs hr
      · nomatch hd2
  have hIkmSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hDom.ikm_small
  set cTot := w4DecryptPrekeySplitWideDirCum sCap smCap kCap maxEntries deserCum
    c_cur c_dec c_tr c_push c_clB c_tdB c_clAC c_tdAC ikmCap
  set lTot := w4DecryptPrekeySplitWideDirLive sCap smCap kCap maxEntries deserLive
    archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC
  set rpTot := w4DecryptPrekeySplitWideDirRawPeak sCap smCap kCap maxEntries deserLive deserPeak
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC
  set rTot := w4DecryptPrekeySplitWideDirMaxReq sCap smCap kCap maxEntries deserMaxReq
    curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
    r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap
  -- Arm 1: Untrusted
  have hUntr0 := w4StageP1UntrustedCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hUntr : PhaseCreditSpec fineCostModel
      (W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      cTot lTot rpTot rTot := hUntr0.mono
    (by dsimp only [cTot, w4DecryptPrekeySplitWideDirCum]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [lTot, w4DecryptPrekeySplitWideDirLive]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rpTot, w4DecryptPrekeySplitWideDirRawPeak]
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (by dsimp only [rTot, w4DecryptPrekeySplitWideDirMaxReq]
        exact wideMaxReq_untr_le _ _ _ _ _ _)
  -- Arm 2: Path B
  have hP1Ok := w4StageP1OkCli_fine_phaseCredit hdcSess hdcPeers hdir
    hDom.peer_len hDom.sess_cap hPeersCap hdeser
  have hP2B := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP2MatchedWide_dom_fine_phaseCredit P.g_arch P.r_arch
      hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush)
  have hP3B := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP3Wide_fine_phaseCredit_tight hCloneB hTdB)
  have hP4B := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP4MatchedCliWide_dom_fine_phaseCredit P.g_out0 P.r_out0
      hdcPeers hdcSess hdir hDom.peer_len hPeersCap hDom.out0_valid hDom.out0_enc)
  have hPathB : PhaseCreditSpec fineCostModel (W4DecryptPrekeyPathBWideEnv P CloneB)
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2B.seq (hP3B.seq hP4B))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitWideDirCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitWideDirLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitWideDirRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitWideDirMaxReq]
        exact wideMaxReq_B_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  -- Arm 3: Path A (with CloneAC + TryDecAC)
  have hP2A := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP2PathACliWide_splitDir_fine_phaseCredit P.hasOpk P.spkId P.kpkId P.opkId
      P.F P.x_spqr hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
      hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2 hDom.kpk_cap)
  have hP3AC := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP3Wide_zeroLive_fine_phaseCredit_tight hCloneAC hTdAC)
  have hP4A := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP4PathACliWide_splitDir_dom_fine_phaseCredit P.hasOpk P.opkId P.g_out0 P.r_out0
      hdcPeers hdcKpk hdcOpk hdcSess hdir hDom.peer_len hDom.kpkMark_len hSmallP4 hDom.kpk_cap
      hDom.out0_valid hDom.out0_enc)
  have hPathA : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC)
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2A.seq (hP3AC.seq hP4A))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitWideDirCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitWideDirLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitWideDirRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitWideDirMaxReq]
        exact wideMaxReq_A_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  -- Arm 4: Path C (with CloneAC + TryDecAC + FreshBobPrev1Dom)
  have hP2C := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP2PathCCliWide_splitDir_dom_fine_phaseCredit P.G_cur P.st_cur P.g_arch P.r_arch
      P.hasOpk P.spkId P.kpkId P.opkId P.F P.x_spqr hDom.cur_dom hCurTrial
      hDom.arch_valid hDom.arch_enc hDom.trials_len4 hl_le_p hDec hTrial hDrop hPush
      hdcSpk hdcKpk hdcOpk hdcOwn hdir hDom.ownKey_len hDom.ownReg_len
      hDom.res_old hDom.res_new hIkmSmall hDom.spqr_key hSmallP2 hDom.kpk_cap)
  have hP4C := phaseCredit_optStageEnv fineCostModel_modelHyps
    (w4StageP4PathCCliWide_splitDir_freshBob_fine_phaseCredit P.hasOpk P.opkId
      P.G_out1 P.sess_out1 P.enc_prev1 hdcPeers hdcKpk hdcOpk hdcSess hdir
      hDom.peer_len hDom.kpkMark_len hSmallP4 hDom.kpk_cap hDom.out1_freshBob)
  have hPathC : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC)
      cTot lTot rpTot rTot := (hP1Ok.seq (hP2C.seq (hP3AC.seq hP4C))).mono
    (by
      dsimp only [cTot, w4DecryptPrekeySplitWideDirCum]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [lTot, w4DecryptPrekeySplitWideDirLive]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      simp only [Nat.add_assoc]
      exact Nat.le_refl _)
    (by
      dsimp only [rpTot, w4DecryptPrekeySplitWideDirRawPeak]
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      exact fourStagePeak_mono
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (by dsimp only [rTot, w4DecryptPrekeySplitWideDirMaxReq]
        exact wideMaxReq_C_le _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have h4 := phaseCreditSpec_or4 (fun _ h => h) hUntr hPathB hPathA hPathC
  have hSeq := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps h4
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact (hFree.or hSeq).mono
    (zero_or_max4_le cTot)
    (zero_or_max4_le lTot)
    (slot_final_peak_le rpTot lTot)
    (zero_or_max4_le rTot)

/-- Uniform `smallFileCap` specialization over `W4DecryptPrekeyTightDom`. -/
theorem w4DecryptPrekeySplitWideSlot_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC TryDecAC : List AllocEvent → Prop}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_clB l_clB p_clB r_clB c_clAC r_clAC
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hCloneB : PhaseCreditSpec fineCostModel CloneB c_clB l_clB p_clB r_clB)
    (hCloneAC : PhaseCreditSpec fineCostModel CloneAC c_clAC 0 0 r_clAC)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideDirCum sCap smCap smCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_clB c_tdB c_clAC c_tdAC ikmCap)
      (w4DecryptPrekeySplitWideDirLive sCap smCap smCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC)
      (w4DecryptPrekeySplitWideDirPeak sCap smCap smCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitWideDirMaxReq sCap smCap smCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap) :=
  w4DecryptPrekeySplitWideSlot_splitDir_fine_phaseCredit P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess hdir hDom.toSplitWideDirDom
    hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hCloneB hCloneAC hTdB hTdAC

/-- Single-`TryDecEnv` (`TryDecAC := P.TryDecEnv`) specialization for `W4DecryptPrekeyWideSlotEnv`. -/
theorem w4DecryptPrekeyWideSlot_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC : List AllocEvent → Prop}
    {maxDir maxEntries maxVal sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_clB l_clB p_clB r_clB c_clAC r_clAC
     c_td l_td p_td r_td : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hCloneB : PhaseCreditSpec fineCostModel CloneB c_clB l_clB p_clB r_clB)
    (hCloneAC : PhaseCreditSpec fineCostModel CloneAC c_clAC 0 0 r_clAC)
    (hTd : PhaseCreditSpec fineCostModel P.TryDecEnv c_td l_td p_td r_td) :
    let sCap := max maxVal sessFileCap
    let smCap := max maxVal smallFileCap
    PhaseCreditSpec fineCostModel (W4DecryptPrekeyWideSlotEnv P CloneB CloneAC)
      (w4DecryptPrekeySplitWideDirCum sCap smCap smCap maxEntries deserCum
        c_cur c_dec c_tr c_push c_clB c_td c_clAC c_td ikmCap)
      (w4DecryptPrekeySplitWideDirLive sCap smCap smCap maxEntries deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_td l_td)
      (w4DecryptPrekeySplitWideDirPeak sCap smCap smCap maxEntries deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_td p_td l_td p_td)
      (w4DecryptPrekeySplitWideDirMaxReq sCap smCap smCap maxEntries deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_clB r_clAC r_td r_td ikmCap) :=
  w4DecryptPrekeySplitWideSlot_fine_phaseCredit P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess hdir hDom
    hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hCloneB hCloneAC hTd hTd

/-- `StoresGhost.opened` (`maxDir = 26 ≤ 64`, `maxEntries = 0`, `maxVal = 0`) per-directory
(`smallFileCap` vs `kpkFileCap`) specialization of `w4DecryptPrekeySplitWideSlot_splitDir_fine_phaseCredit`. -/
theorem w4DecryptPrekeySplitWideSlot_splitDir_opened_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC TryDecAC : List AllocEvent → Prop}
    {sessFileCap smallFileCap kpkFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_clB l_clB p_clB r_clB c_clAC r_clAC
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSpk : P.spkDir = StoresGhost.opened.signed)
    (hKpk : P.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            P.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hOpk : P.opkDir = StoresGhost.opened.oneTime)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hDom : W4DecryptPrekeySplitWideDirDom P sessFileCap smallFileCap kpkFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hCloneB : PhaseCreditSpec fineCostModel CloneB c_clB l_clB p_clB r_clB)
    (hCloneAC : PhaseCreditSpec fineCostModel CloneAC c_clAC 0 0 r_clAC)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideDirCum sessFileCap smallFileCap kpkFileCap 0 deserCum
        c_cur c_dec c_tr c_push c_clB c_tdB c_clAC c_tdAC ikmCap)
      (w4DecryptPrekeySplitWideDirLive sessFileCap smallFileCap kpkFileCap 0 deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC)
      (w4DecryptPrekeySplitWideDirPeak sessFileCap smallFileCap kpkFileCap 0 deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitWideDirMaxReq sessFileCap smallFileCap kpkFileCap 0 deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap) := by
  obtain ⟨hdcOwn0, hdcPeers0, hdcSpk0, hdcKot0, hdcKlr0, hdcOpk0, hdcSess0⟩ :=
    opened_all_dirDomainCaps
  have hdcOwn : DirDomainCaps 26 0 0 P.ownDir := hOwn ▸ hdcOwn0
  have hdcPeers : DirDomainCaps 26 0 0 P.peersDir := hPeers ▸ hdcPeers0
  have hdcSpk : DirDomainCaps 26 0 0 P.spkDir := hSpk ▸ hdcSpk0
  have hdcKpk : DirDomainCaps 26 0 0 P.kpkDir := by
    rcases hKpk with h1 | h2
    · exact h1 ▸ hdcKot0
    · exact h2 ▸ hdcKlr0
  have hdcOpk : DirDomainCaps 26 0 0 P.opkDir := hOpk ▸ hdcOpk0
  have hdcSess : DirDomainCaps 26 0 0 P.sessDir := hSess ▸ hdcSess0
  have h := w4DecryptPrekeySplitWideSlot_splitDir_fine_phaseCredit P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess (by decide)
    hDom hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hCloneB hCloneAC hTdB hTdAC
  simpa only [Nat.zero_max] using h

/-- `StoresGhost.opened` uniform `smallFileCap` specialization over `W4DecryptPrekeyTightDom`. -/
theorem w4DecryptPrekeySplitWideSlot_opened_fine_phaseCredit {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC TryDecAC : List AllocEvent → Prop}
    {sessFileCap smallFileCap
     curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap
     deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_clB l_clB p_clB r_clB c_clAC r_clAC
     c_tdB l_tdB p_tdB r_tdB c_tdAC l_tdAC p_tdAC r_tdAC : Nat}
    {l_dec : α → Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSpk : P.spkDir = StoresGhost.opened.signed)
    (hKpk : P.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            P.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hOpk : P.opkDir = StoresGhost.opened.oneTime)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hDom : W4DecryptPrekeyTightDom P sessFileCap smallFileCap
      curPqCap archPqCap archEncCap out0PqCap out0EncCap
      bobPqCap prevEncCap totalPrev1Cap ikmCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec fineCostModel (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec fineCostModel (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec fineCostModel P.VecPushEnv c_push 0 0 r_push)
    (hCloneB : PhaseCreditSpec fineCostModel CloneB c_clB l_clB p_clB r_clB)
    (hCloneAC : PhaseCreditSpec fineCostModel CloneAC c_clAC 0 0 r_clAC)
    (hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv c_tdB l_tdB p_tdB r_tdB)
    (hTdAC : PhaseCreditSpec fineCostModel TryDecAC c_tdAC l_tdAC p_tdAC r_tdAC) :
    PhaseCreditSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideDirCum sessFileCap smallFileCap smallFileCap 0 deserCum
        c_cur c_dec c_tr c_push c_clB c_tdB c_clAC c_tdAC ikmCap)
      (w4DecryptPrekeySplitWideDirLive sessFileCap smallFileCap smallFileCap 0 deserLive
        archEncCap out0EncCap totalPrev1Cap l_clB l_tdB l_tdAC)
      (w4DecryptPrekeySplitWideDirPeak sessFileCap smallFileCap smallFileCap 0 deserLive deserPeak
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        p_cur p_dec p_tr l_clB p_clB l_tdB p_tdB l_tdAC p_tdAC)
      (w4DecryptPrekeySplitWideDirMaxReq sessFileCap smallFileCap smallFileCap 0 deserMaxReq
        curPqCap archPqCap archEncCap out0PqCap out0EncCap bobPqCap prevEncCap totalPrev1Cap
        r_cur r_dec r_tr r_push r_clB r_clAC r_tdB r_tdAC ikmCap) :=
  w4DecryptPrekeySplitWideSlot_splitDir_opened_fine_phaseCredit P
    hOwn hPeers hSpk hKpk hOpk hSess hDom.toSplitWideDirDom
    hdeser hCurTrial hl_le_p hDec hTrial hDrop hPush hCloneB hCloneAC hTdB hTdAC

/-- `W4SlotR3bEnv` wire+slot composition for `W4DecryptPrekeySplitWideSlotEnv`. -/
theorem w4SlotR3b_splitWide_fine_phaseCredit {α : Type}
    (x_pksm : PksmGhost) (P : W4DecryptPrekeySlotParams α)
    {CloneB CloneAC TryDecAC : List AllocEvent → Prop} {c l p r : Nat}
    (hDec : PhaseCreditSpec fineCostModel
      (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC) c l p r) :
    PhaseCreditSpec fineCostModel
      (W4SlotR3bEnv x_pksm (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC))
      (w4SlotR3bDeltaCum x_pksm c)
      (w4SlotR3bDeltaLive x_pksm l)
      (w4SlotR3bDeltaPeak x_pksm l p)
      (w4SlotR3bMaxReq x_pksm r) :=
  w4SlotR3b_fine_phaseCredit x_pksm hDec

/-! ### Closed-`Nat` Widened Slot Cap Evaluations -/

/-- Closed `Nat` widened `Δcum` at `DeserCancel` (`16,890,453` B) + `W2Seeds738` +
`FreshBobCloneDom 16384` (`36,295` B), parameterized by `(smallCap, kpkCap)`. -/
def w4CanonicalSplitWideDirCum (smallCap kpkCap : Nat) : Nat :=
  let cFail := w2TryDecryptSeeds738Cum 5 true 12 23313687
  let cTrWide := 8277456 + cFail + 8674
  let cTdAC := w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904
  w4DecryptPrekeySplitWideDirCum 2097152 smallCap kpkCap 0 16890453
    cFail 16890453 cTrWide 9923 8277456 cFail 36295 cTdAC 4096

/-- Closed-`Nat` widened W4 `Δlive` at `DeserCancel` (`3,211,282` B), parameterized by
`(smallCap, kpkCap, maxCt)`. -/
def w4CanonicalSplitWideDirLive (smallCap kpkCap maxCt : Nat) : Nat :=
  let lClB := 1080975 + fineOptLarge 286196
  let lTdB := w2TryDecryptTightLive 2000 605066 maxCt
  let lTdAC := w2TryDecryptTightLive 2000 294391 maxCt
  w4DecryptPrekeySplitWideDirLive 2097152 smallCap kpkCap 0 3211282
    2097152 2097152 2457152 lClB lTdB lTdAC

/-- Closed-`Nat` widened W4 `Δpeak` at `DeserCancel` (`3,211,282` / `5,316,629` B), parameterized by
`(smallCap, kpkCap, maxCt)`. -/
def w4CanonicalSplitWideDirPeak (smallCap kpkCap maxCt : Nat) : Nat :=
  let lClB := 1080975 + fineOptLarge 286196
  let pFail := w2TryDecryptTightPeak 2000 605066 621350 maxCt
  let pTr := 1080975 + fineOptLarge 286196 + pFail
  let lTdB := w2TryDecryptTightLive 2000 605066 maxCt
  let lTdAC := w2TryDecryptTightLive 2000 294391 maxCt
  let pTdAC := w2TryDecryptTightPeak 2000 294391 294391 maxCt
  w4DecryptPrekeySplitWideDirPeak 2097152 smallCap kpkCap 0 3211282 5316629
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    pFail 5316629 pTr lClB lClB lTdB pFail lTdAC pTdAC

/-- Closed-`Nat` widened W4 `maxReq` at `DeserCancel` (`2,097,152` B), parameterized by
`(smallCap, kpkCap, maxCt)`. -/
def w4CanonicalSplitWideDirMaxReq (smallCap kpkCap maxCt : Nat) : Nat :=
  let rTd := w2TryDecryptMaxReq 5 2000 302480 maxCt
  let rTr := max (max (max 208000 286196) rTd) 192
  w4DecryptPrekeySplitWideDirMaxReq 2097152 smallCap kpkCap 0 2097152
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    rTd 2097152 rTr 192 (max 208000 286196) 208000 rTd rTd 4096

/-- `64 KiB` / `4096` B baseline widened slot profile:
`(283,641,187, 11,931,950, 13,307,316, 2,457,152)`. -/
theorem w4CanonicalSplitWide_real64k_eq :
    w4CanonicalSplitWideDirCum 4096 4096 = 283641187 ∧
    w4CanonicalSplitWideDirLive 4096 4096 65536 = 11931950 ∧
    w4CanonicalSplitWideDirPeak 4096 4096 65536 = 13307316 ∧
    w4CanonicalSplitWideDirMaxReq 4096 4096 65536 = 2457152 ∧
    w4CanonicalSplitWideDirLive 4096 4096 65536 ≤
      w4CanonicalSplitWideDirPeak 4096 4096 65536 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `1 MiB` Variant (i) (uniform `2 MiB` directory cap) widened slot profile:
`(288,693,859, 30,610,803, 32,716,150, 2,457,152)`. -/
theorem w4CanonicalSplitWide_real1MiB_i_eq :
    w4CanonicalSplitWideDirCum 2097152 2097152 = 288693859 ∧
    w4CanonicalSplitWideDirLive 2097152 2097152 1048576 = 30610803 ∧
    w4CanonicalSplitWideDirPeak 2097152 2097152 1048576 = 32716150 ∧
    w4CanonicalSplitWideDirMaxReq 2097152 2097152 1048576 = 2457152 ∧
    w4CanonicalSplitWideDirLive 2097152 2097152 1048576 ≤
      w4CanonicalSplitWideDirPeak 2097152 2097152 1048576 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `1 MiB` Variant (ii) (split `4096 / 2 MiB` directory cap) widened slot profile:
`(284,764,003, 15,873,374, 17,978,721, 2,457,152)`. -/
theorem w4CanonicalSplitWide_real1MiB_ii_eq :
    w4CanonicalSplitWideDirCum 4096 2097152 = 284764003 ∧
    w4CanonicalSplitWideDirLive 4096 2097152 1048576 = 15873374 ∧
    w4CanonicalSplitWideDirPeak 4096 2097152 1048576 = 17978721 ∧
    w4CanonicalSplitWideDirMaxReq 4096 2097152 1048576 = 2457152 ∧
    w4CanonicalSplitWideDirLive 4096 2097152 1048576 ≤
      w4CanonicalSplitWideDirPeak 4096 2097152 1048576 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end WidenedBinaryCompleteTightSpecs

end LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
