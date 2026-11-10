/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# W4 Outer `process_prekey` / `decrypt_prekey` Peak Live-Heap Spec

Symbolic `(M : AllocCostModel) [HasFineReallocCredit M]` (`ModelHyps M`) `PhaseCreditSpec` bounds in
binary execution order across W4 `signal_session_handshake::decrypt_prekey` (`process_prekey`,
Stages P1–P4): Stage P1 (`load_session` + `is_trusted_identity`), Stage P2 (`Matched` Path B, fresh
`0`-prev Path A, and `Over` `prev1` Path C), Stage P3 (`try_decrypt_pq`), Stage P4 (`0`-prev and
`prev1` store), the 4-arm `W4DecryptPrekeySlotEnv` and `W4SlotR3bEnv` composers, and binary-complete
widened envelopes (`W4DecryptPrekeySplitWideSlotEnv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec

open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator MessageKeys SessionState ShaCompress
   SignalMessage TripleRatchet)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall SpqrModel TrGhost TryDecryptGhost reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost UuidParser)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost keyName pathOf)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec IterSeqEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents serialize_phaseCredit
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (segCloneCum segCloneLarge segCloneMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak
   serializePrev1Cum serializePrev1MaxReq serializePrev1OutLarge serializePrev1Peak)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4InitBobSpqrEnv W4StageP2OverBobEnv
   phaseCredit_w4InitBob_aff phaseCredit_w4InitBob_small phaseCredit_w4StageP2OverBob_small
   w4InitBobOuterCum)
open LibsignalBinary.Proofs.PeakBudget.W4InnerPeakSpec
  (phaseCredit_archivedTrialLoop_le4 phaseCredit_fromS1GenEnv
   promoteStateArchive_c04_phaseCredit tryDecryptCloneFail_c04_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (phaseCreditSpec_ite_nil phaseCreditSpec_or4)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv W4SessLoadStepEnv W4SessStorePrev1StepEnv W4SessStoreStepEnv
   W4SmallStoreStepEnv W4StageP1OkCliEnv W4StageP1UntrustedCliEnv
   W4StageP4MatchedCliEnv W4StageP4PathACliEnv W4StageP4PathCCliEnv
   growOneSpeZero_phaseCredit_aff growOneSpeZero_phaseCredit_small
   opened_all_dirDomainCaps phaseCreditSpec_seq_freeOnly_exact
   w4BoxedStepCum w4BoxedStepLive w4BoxedStepMaxReq w4BoxedStepPeak
   w4KeyIdSmallStoreStep_phaseCredit w4SmallStoreStep_phaseCredit
   w4SpqrInit32_phaseCredit w4SpqrInitCum w4SpqrInitLive w4SpqrInitPeak
   w4StageP1OkCli_phaseCredit w4StageP1UntrustedCli_phaseCredit
   w4StageP1UntrustedCli_small_phaseCredit
   w4StageP4MatchedCli_phaseCredit w4StageP4PathACli_phaseCredit w4StageP4PathCCli_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (PksmTryFromBoundedEnv WireLowInterceptHyps fineCostModel_wireLowInterceptHyps
   pksmTryFromDeltaCum pksmTryFromDeltaLive pksmTryFromDeltaPeak pksmTryFromMaxReq
   pksmTryFrom_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (FromS1GenEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. Error-Return Tail (`W4ErrTailEnv`) and Stage P1 Exports -/

export W4OuterStageHelpers
  (W4BoxedStoreStepEnv W4SmallStoreStepEnv W4SessLoadStepEnv
   W4SessStoreStepEnv W4SessStorePrev1StepEnv)
export W4OuterStageHelpers
  (W4StageP1OkCliEnv W4StageP1UntrustedCliEnv
   W4StageP4MatchedCliEnv W4StageP4PathACliEnv W4StageP4PathCCliEnv)
export W4OuterStageHelpers
  (w4BoxedStepCum w4BoxedStepLive w4BoxedStepPeak w4BoxedStepMaxReq)

abbrev w4StageP1Ok_phaseCredit := @w4StageP1OkCli_phaseCredit
abbrev w4StageP1Untrusted_phaseCredit := @w4StageP1UntrustedCli_phaseCredit
abbrev w4StageP1Untrusted_small_phaseCredit := @w4StageP1UntrustedCli_small_phaseCredit

/-- Optional `192`-byte `SignalProtocolError` box allocation + `FreeOnlyEvs` teardown on stage exit.
-/
def W4ErrTailEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs evs

theorem w4ErrTail_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M W4ErrTailEnv 9923 8387 8387 192 := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  have hSpe : PhaseCreditSpec M (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs) 9923 8387 8387 192 :=
    phaseCreditSpec_seq_freeOnly_exact hM (growOneSpeZero_phaseCredit_aff hM)
  exact (hFree.or hSpe).mono (by omega) (by omega) (by omega) (by omega)

theorem w4ErrTail_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M W4ErrTailEnv 9923 0 0 192 := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  have hSpe : PhaseCreditSpec M (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs) 9923 0 0 192 :=
    phaseCreditSpec_seq_freeOnly_exact hM (growOneSpeZero_phaseCredit_small hM hsmall)
  exact (hFree.or hSpe).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)

/-! ## 2. Stage P2 Envelopes and `PhaseCreditSpec`s (`Matched`, `PathA`, and `PathC`) -/

/-- Stage P2 Path B (`Matched` existing session) envelope: direct `FreeOnlyEvs` match or `≤ 4` archived-session `PrevDec` + trial iterations followed by optional `PromoteStateArchiveEnv`.
-/
def W4StageP2MatchedEnv {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (VecPushEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs)
    (fun evs2 => FreeOnlyEvs evs2 ∨
      SeqEnv (PromoteStateArchiveEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv)
        FreeOnlyEvs evs2) evs

/-- `PhaseCreditSpec` for `W4StageP2MatchedEnv` (`0` net trial `Δlive`, `1×` trial peak `p_dec + p_tr`).
-/
theorem w4StageP2Matched_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec M (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec M (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec M (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push) :
    PhaseCreditSpec M
      (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (4 * (c_dec + c_tr) + (recordSerializeCum g_arch r_arch + c_push))
      (recordSerializeOutLarge M g_arch r_arch)
      (max (p_dec + p_tr)
        (max (recordSerializePeak M g_arch r_arch) (recordSerializeOutLarge M g_arch r_arch)))
      (max (max r_dec r_tr) (max (recordSerializeMaxReq g_arch r_arch) r_push)) := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  have hLoop := phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop
  have hProm := phaseCreditSpec_seq_freeOnly_exact hM
    (promoteStateArchive_c04_phaseCredit hM g_arch r_arch hPush)
  have hOptProm := hFree.or hProm
  have hSeq := hLoop.seq hOptProm
  exact (hFree.or hSeq).mono (by omega) (by omega) (by omega) (by omega)

/-- Stage P2 Path A (`0`-prev fresh responder handshake) CLI envelope (`spkGet → kpkGet → opt pkGet → idKp → W4InitBobSpqrEnv → idRegId → W4ErrTailEnv`).
-/
def W4StageP2PathACliEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SmallStoreStepEnv 16 rd files spkDir (keyName spkId))
    (SeqEnv (W4SmallStoreStepEnv 16 rd files kpkDir (keyName kpkId))
      (SeqEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = []))
        (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownKeyName)
          (SeqEnv (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
            (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName)
              W4ErrTailEnv))))) evs

private theorem seqPeak_mono {p1 p1' l1 l1' q q' : Nat}
    (hp : p1 ≤ p1') (hl : l1 ≤ l1') (hq : q ≤ q') :
    max p1 (l1 + q) ≤ max p1' (l1' + q') :=
  Nat.max_le.mpr ⟨Nat.le_trans hp (Nat.le_max_left _ _),
    Nat.le_trans (Nat.add_le_add hl hq) (Nat.le_max_right _ _)⟩

private theorem p2a_cum_le (a b1 b2 c : Nat) :
    a + (a + (a + (a + ((b1 + b2) + (a + c))))) ≤ 5 * a + b1 + b2 + c := by
  omega

private theorem p2a_live_le (a b : Nat) :
    a + (a + (a + (a + (b + a)))) ≤ 5 * a + b := by
  omega

private theorem p2a_aff_live_le (a b c : Nat) :
    a + (a + (a + (a + (b + (a + c))))) ≤ 5 * a + b + c := by
  omega

private theorem p2a_bob_maxReq_le (ikmCap : Nat) :
    max (max ikmCap 1569) (max 4224 68) ≤ max ikmCap 4224 :=
  Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _,
       Nat.le_trans (by decide : 1569 ≤ 4224) (Nat.le_max_right _ _)⟩,
     Nat.max_le.mpr ⟨Nat.le_max_right _ _,
       Nat.le_trans (by decide : 68 ≤ 4224) (Nat.le_max_right _ _)⟩⟩

private theorem p2a_maxReq_le (r16 ikmCap : Nat) :
    max r16 (max r16 (max r16 (max r16 (max (max ikmCap 4224) (max r16 192))))) ≤
      max r16 (max ikmCap 4224) := by
  have hr : r16 ≤ max r16 (max ikmCap 4224) := Nat.le_max_left _ _
  have hb : max ikmCap 4224 ≤ max r16 (max ikmCap 4224) := Nat.le_max_right _ _
  have h192 : 192 ≤ max r16 (max ikmCap 4224) :=
    Nat.le_trans (by decide : 192 ≤ 4224) (Nat.le_trans (Nat.le_max_right _ _) hb)
  exact Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hr,
    Nat.max_le.mpr ⟨hr, Nat.max_le.mpr ⟨hb, Nat.max_le.mpr ⟨hr, h192⟩⟩⟩⟩⟩⟩

private theorem p2c_cum_le (cCur cLoop c16 cOver : Nat) :
    cCur + (cLoop + (c16 + (c16 + (c16 + (c16 + (cOver + (c16 + 9923))))))) ≤
      cCur + cLoop + 5 * c16 + cOver + 9923 := by
  omega

private theorem p2c_live_le (l16 lOver : Nat) :
    0 + (0 + (l16 + (l16 + (l16 + (l16 + (lOver + l16)))))) ≤ 5 * l16 + lOver := by
  omega

private theorem p2c_peak_le (pCur pLoop pRest : Nat) :
    max pCur (0 + max pLoop (0 + pRest)) ≤ max pCur (max pLoop pRest) := by
  simp only [Nat.zero_add]
  exact Nat.le_refl _

private theorem p2c_maxReq_le (rSeg rCur rDec rTr rSer rPush r16 ikmCap : Nat) :
    max (max (max rSeg rCur) 192)
      (max (max rDec rTr)
        (max r16 (max r16 (max r16 (max r16
          (max (max (max rSer rPush) (max ikmCap 4224)) (max r16 192))))))) ≤
    max (max (max rSeg rCur) (max rDec rTr))
      (max (max rSer rPush) (max r16 (max ikmCap 4224))) := by
  let T := max (max (max rSeg rCur) (max rDec rTr))
    (max (max rSer rPush) (max r16 (max ikmCap 4224)))
  have hL : max (max rSeg rCur) (max rDec rTr) ≤ T := Nat.le_max_left _ _
  have hR : max (max rSer rPush) (max r16 (max ikmCap 4224)) ≤ T := Nat.le_max_right _ _
  have h1 : max rSeg rCur ≤ T := Nat.le_trans (Nat.le_max_left _ _) hL
  have h2 : max rDec rTr ≤ T := Nat.le_trans (Nat.le_max_right _ _) hL
  have h3 : max rSer rPush ≤ T := Nat.le_trans (Nat.le_max_left _ _) hR
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

/-- Small-regime `PhaseCreditSpec` for `W4StageP2PathACliEnv`. -/
theorem w4StageP2PathACli_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool)
    {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal fileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
    let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
    let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
    let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
    PhaseCreditSpec M
      (W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 9923)
      (5 * l16 + w4SpqrInitLive 32)
      (max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
        (l16 + max (w4SpqrInitPeak 32) (w4SpqrInitLive 32 + max p16 l16))))))
      (max r16 (max ikmCap 4224)) := by
  dsimp only
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hSpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 spkId hdcSpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 kpkId hdcKpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep_phaseCredit hM 16 opkId hdcOpk hdir (fun bs hr => hfileCap _ bs hr)
  have hKp := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hSpqr := w4SpqrInit32_phaseCredit hM F x_spqr hspqrKey
  have hBob : PhaseCreditSpec M (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      (w4InitBobOuterCum ikmCap + w4SpqrInitCum 32)
      (w4SpqrInitLive 32) (w4SpqrInitPeak 32) (max ikmCap 4224) :=
    (phaseCredit_w4InitBob_small hM (hasOpk := hasOpk) hold hnew hSmall hSpqr).mono
      (Nat.le_refl _) (Nat.le_refl _)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (p2a_bob_maxReq_le ikmCap)
  have hReg := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hTail := w4ErrTail_small_phaseCredit hM hSm192
  have h67 : PhaseCreditSpec M
      (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName) W4ErrTailEnv)
      (w4BoxedStepCum 16 (smallStorePollDeltaCum (max maxVal fileCap) maxEntries) + 9923)
      (w4BoxedStepLive 16 (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (max (w4BoxedStepPeak 16 (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
        (w4BoxedStepLive 16 (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)))
      (max (w4BoxedStepMaxReq 16 (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) 192) :=
    (hReg.seq hTail).mono (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h57 := hBob.seq h67
  have h47 := hKp.seq h57
  have h37 := hOptPk.seq h47
  have h27 := hKpk.seq h37
  exact (hSpk.seq h27).mono
    (p2a_cum_le _ _ _ _)
    (p2a_live_le _ _)
    (Nat.le_refl _)
    (p2a_maxReq_le _ _)

/-- Regime-free `PhaseCreditSpec` for `W4StageP2PathACliEnv`. -/
theorem w4StageP2PathACli_aff_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool)
    {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal fileCap : Nat}
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
    let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
    let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
    let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
    let lBob := (ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 +
      w4SpqrInitLive 32 + 6 * (68 + 8195)
    let pBob := (ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 +
      max (w4SpqrInitPeak 32) (w4SpqrInitLive 32 + 6 * (68 + 8195))
    PhaseCreditSpec M
      (W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir spkId kpkId opkId
        ownKeyName ownRegName F x_res x_spqr)
      (5 * c16 + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32 + 9923)
      (5 * l16 + lBob + 8387)
      (max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
        (l16 + max pBob (lBob + max p16 (l16 + 8387)))))))
      (max r16 (max ikmCap 4224)) := by
  dsimp only
  have hSpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 spkId hdcSpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 kpkId hdcKpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep_phaseCredit hM 16 opkId hdcOpk hdir (fun bs hr => hfileCap _ bs hr)
  have hKp := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hSpqr := w4SpqrInit32_phaseCredit hM F x_spqr hspqrKey
  have hBob : PhaseCreditSpec M (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      (w4InitBobOuterCum ikmCap + w4SpqrInitCum 32)
      ((ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 + w4SpqrInitLive 32 + 6 * (68 + 8195))
      ((ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 +
        max (w4SpqrInitPeak 32) (w4SpqrInitLive 32 + 6 * (68 + 8195)))
      (max ikmCap 4224) :=
    (phaseCredit_w4InitBob_aff hM (hasOpk := hasOpk) hnew hSpqr).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (p2a_bob_maxReq_le ikmCap)
  have hReg := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hTail := w4ErrTail_phaseCredit hM
  have h67 := hReg.seq hTail
  have h57 := hBob.seq h67
  have h47 := hKp.seq h57
  have h37 := hOptPk.seq h47
  have h27 := hKpk.seq h37
  exact (hSpk.seq h27).mono
    (p2a_cum_le _ _ _ _)
    (p2a_aff_live_le _ _ _)
    (Nat.le_refl _)
    (p2a_maxReq_le _ _)

/-- Stage P2 Path C (`Over` / `prev1` responder handshake) CLI envelope. -/
def W4StageP2PathCCliEnv {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (VecPushEnv : List AllocEvent → Prop)
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (fun e1 => FreeOnlyEvs e1 ∨
      W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur) e1)
    (SeqEnv
      (fun e2 => FreeOnlyEvs e2 ∨
        IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs e2)
      (SeqEnv (W4SmallStoreStepEnv 16 rd files spkDir (keyName spkId))
        (SeqEnv (W4SmallStoreStepEnv 16 rd files kpkDir (keyName kpkId))
          (SeqEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = []))
            (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownKeyName)
              (SeqEnv
                (W4StageP2OverBobEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
                  x_res hasOpk (InitialStateEnv F x_spqr))
                (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName)
                  W4ErrTailEnv))))))) evs

/-- Small-regime `PhaseCreditSpec` for `W4StageP2PathCCliEnv`. -/
theorem w4StageP2PathCCli_small_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    {CurTrialFailEnv : List AllocEvent → Prop} {c_cur p_cur r_cur : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop}
    {c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push : Nat}
    {l_dec : α → Nat} {xs : List α}
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    (spkId kpkId opkId : BitVec 32)
    {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress) {x_res : DoReserveCall} (x_spqr : InitialStateGhost)
    {ikmCap maxDir maxEntries maxVal fileCap : Nat}
    (hCurTrial : PhaseCreditSpec M CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : xs.length ≤ 4)
    (hl_le_p : ∀ x ∈ xs, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ xs, PhaseCreditSpec M (DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ xs, PhaseCreditSpec M (TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ xs, DeallocCreditSpec M (DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hdir : maxDir ≤ 64)
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
    let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
    let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
    let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
    let lOver := recordSerializeOutLarge M g_arch r_arch + w4SpqrInitLive 32
    let pOver := max (recordSerializePeak M g_arch r_arch)
      (recordSerializeOutLarge M g_arch r_arch + w4SpqrInitPeak 32)
    let pRest := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
      (l16 + max pOver (lOver + max p16 l16)))))
    PhaseCreditSpec M
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((segCloneCum G_cur st_cur + c_cur + 9923) + 4 * (c_dec + c_tr) +
        5 * c16 + (recordSerializeCum g_arch r_arch + c_push +
          w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 9923)
      (5 * l16 + lOver)
      (max (segCloneLarge M G_cur st_cur + p_cur) (max (p_dec + p_tr) pRest))
      (max (max (max (segCloneMaxReq G_cur st_cur) r_cur) (max r_dec r_tr))
        (max (max (recordSerializeMaxReq g_arch r_arch) r_push)
          (max r16 (max ikmCap 4224)))) := by
  dsimp only
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  have hCur : PhaseCreditSpec M
      (fun e1 => FreeOnlyEvs e1 ∨
        W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur) e1)
      (segCloneCum G_cur st_cur + c_cur + 9923) 0
      (segCloneLarge M G_cur st_cur + p_cur)
      (max (max (segCloneMaxReq G_cur st_cur) r_cur) 192) :=
    (hFree.or (tryDecryptCloneFail_c04_cancel_phaseCredit hM G_cur st_cur hSm192 hCurTrial)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hLoop : PhaseCreditSpec M
      (fun e2 => FreeOnlyEvs e2 ∨
        IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs e2)
      (4 * (c_dec + c_tr)) 0 (p_dec + p_tr) (max r_dec r_tr) :=
    (hFree.or (phaseCredit_archivedTrialLoop_le4 hlen4 hl_le_p hDec hTrial hDrop)).mono
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
  have hSpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 spkId hdcSpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hKpk := w4KeyIdSmallStoreStep_phaseCredit hM 16 kpkId hdcKpk hdir
    (fun bs hr => hfileCap _ bs hr)
  have hOptPk := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep_phaseCredit hM 16 opkId hdcOpk hdir (fun bs hr => hfileCap _ bs hr)
  have hKp := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hSpqr := w4SpqrInit32_phaseCredit hM F x_spqr hspqrKey
  have hOver : PhaseCreditSpec M
      (W4StageP2OverBobEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (recordSerializeCum g_arch r_arch + c_push + w4InitBobOuterCum ikmCap + w4SpqrInitCum 32)
      (recordSerializeOutLarge M g_arch r_arch + w4SpqrInitLive 32)
      (max (recordSerializePeak M g_arch r_arch)
        (recordSerializeOutLarge M g_arch r_arch + w4SpqrInitPeak 32))
      (max (max (recordSerializeMaxReq g_arch r_arch) r_push) (max ikmCap 4224)) :=
    (phaseCredit_w4StageP2OverBob_small hM (hasOpk := hasOpk)
      (serialize_phaseCredit hM g_arch r_arch) hPush hold hnew hSmall hSpqr).mono
      (Nat.le_refl _) (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
        (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩))
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (p2a_bob_maxReq_le ikmCap) (Nat.le_max_right _ _)⟩)
  have hReg := w4SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hTail := w4ErrTail_small_phaseCredit hM hSm192
  have h89 : PhaseCreditSpec M
      (SeqEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName) W4ErrTailEnv)
      (w4BoxedStepCum 16 (smallStorePollDeltaCum (max maxVal fileCap) maxEntries) + 9923)
      (w4BoxedStepLive 16 (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (max (w4BoxedStepPeak 16 (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
        (w4BoxedStepLive 16 (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)))
      (max (w4BoxedStepMaxReq 16 (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) 192) :=
    (hReg.seq hTail).mono (Nat.le_refl _) (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (congrArg (max _) (Nat.add_zero _))) (Nat.le_refl _)
  have h79 := hOver.seq h89
  have h69 := hKp.seq h79
  have h59 := hOptPk.seq h69
  have h49 := hKpk.seq h59
  have h39 := hSpk.seq h49
  have h29 := hLoop.seq h39
  exact (hCur.seq h29).mono
    (p2c_cum_le _ _ _ _)
    (p2c_live_le _ _)
    (p2c_peak_le _ _ _)
    (p2c_maxReq_le _ _ _ _ _ _ _ _)

/-! ## 3. Stage P3 (`try_decrypt_pq` + `W4ErrTailEnv`) and Stage P4 Exports -/

/-- Stage P3 inner `SignalMessage` decryption envelope (`TryDecEnv → W4ErrTailEnv`). -/
def W4StageP3Env (TryDecEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv TryDecEnv W4ErrTailEnv evs

theorem w4StageP3_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {TryDecEnv : List AllocEvent → Prop} {c l p r : Nat}
    (hTd : PhaseCreditSpec M TryDecEnv c l p r) :
    PhaseCreditSpec M (W4StageP3Env TryDecEnv)
      (c + 9923) (l + 8387) (max p (l + 8387)) (max r 192) :=
  hTd.seq (w4ErrTail_phaseCredit hM)

theorem w4StageP3_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    {TryDecEnv : List AllocEvent → Prop} {c l p r : Nat}
    (hTd : PhaseCreditSpec M TryDecEnv c l p r) :
    PhaseCreditSpec M (W4StageP3Env TryDecEnv)
      (c + 9923) l (max p l) (max r 192) := by
  exact (hTd.seq (w4ErrTail_small_phaseCredit hM hsmall)).mono
    (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

/-- Small-regime Stage P3 bound specialized to `RootBudgetAux.FromS1GenEnv`. -/
theorem w4StageP3_fromS1Gen_small_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
    {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    {c1 l1 p1 r1 c3 l3 p3 r3 c4 l4 p4 r4 c5 l5 p5 r5 c6 l6 p6 r6
     c7 l7 p7 r7 c8 l8 p8 r8 c9 l9 p9 r9 : Nat}
    {x : TryDecryptGhost}
    (hS1 : PhaseCreditSpec M (s1OkEnv x) c1 l1 p1 r1)
    (hS3 : ∀ trG' tr', PhaseCreditSpec M (s3Env x trG' tr') c3 l3 p3 r3)
    (hS4 : ∀ trG' tr' ck, PhaseCreditSpec M (s4Env x trG' tr' ck) c4 l4 p4 r4)
    (hS5 : ∀ tr', PhaseCreditSpec M (s5Env x tr') c5 l5 p5 r5)
    (hS6 : ∀ mkg, PhaseCreditSpec M (s6Env mkg) c6 l6 p6 r6)
    (hS7 : ∀ tr' mks pqr, PhaseCreditSpec M (s7Env x tr' mks pqr) c7 l7 p7 r7)
    (hS8 : ∀ mks pqr, PhaseCreditSpec M (s8Env x mks pqr) c8 l8 p8 r8)
    (hS9 : ∀ trG' tr' st1 pqr, PhaseCreditSpec M (s9Env x trG' tr' st1 pqr) c9 l9 p9 r9) :
    PhaseCreditSpec M
      (W4StageP3Env
        (FromS1GenEnv C parse S aesOpt s1OkEnv s3Env s4Env s5Env s6Env s7Env s8Env s9Env x))
      ((c1 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + c9))))))) + 9923)
      (l1 + (l3 + (l4 + (l5 + (l6 + (l7 + (l8 + l9)))))))
      (max
        (max p1 (l1 + max p3 (l3 + max p4 (l4 + max p5 (l5 +
          max p6 (l6 + max p7 (l7 + max p8 (l8 + p9))))))))
        (l1 + (l3 + (l4 + (l5 + (l6 + (l7 + (l8 + l9))))))))
      (max (max r1 (max r3 (max r4 (max r5 (max r6 (max r7 (max r8 r9))))))) 192) :=
  w4StageP3_small_phaseCredit hM hsmall
    (phaseCredit_fromS1GenEnv hM hS1 hS3 hS4 hS5 hS6 hS7 hS8 hS9)

abbrev w4StageP4Matched_phaseCredit := @w4StageP4MatchedCli_phaseCredit
abbrev w4StageP4PathA_phaseCredit := @w4StageP4PathACli_phaseCredit
abbrev w4StageP4PathC_phaseCredit := @w4StageP4PathCCli_phaseCredit

/-! ## 4. End-to-End 4-Arm `W4DecryptPrekeySlotEnv` -/

/-- Bundled parameters for a 4-arm W4 `decrypt_prekey` (`process_prekey`) CLI slot invocation across Stages P1–P4.
-/
structure W4DecryptPrekeySlotParams (α : Type) where
  rd : ReadRule
  DeserEnv : List (BitVec 8) → List AllocEvent → Prop
  files : FsFiles
  ownDir : DirGhost
  peersDir : DirGhost
  spkDir : DirGhost
  kpkDir : DirGhost
  opkDir : DirGhost
  sessDir : DirGhost
  peer : AddrGhost
  hasOpk : Bool
  spkId : BitVec 32
  kpkId : BitVec 32
  opkId : BitVec 32
  kpkMarkName : List (BitVec 8)
  ownKeyName : List (BitVec 8)
  ownRegName : List (BitVec 8)
  F : ShaCompress
  x_res : DoReserveCall
  x_spqr : InitialStateGhost
  G_cur : SessionGhost
  st_cur : SessionState (List (BitVec 8))
  CurTrialFailEnv : List AllocEvent → Prop
  DecEnv : α → List AllocEvent → Prop
  TrialEnv : α → List AllocEvent → Prop
  DropEnv : α → List AllocEvent → Prop
  archivedTrials : List α
  g_arch : RecordGhost
  r_arch : SessionRecord (List (BitVec 8))
  VecPushEnv : List AllocEvent → Prop
  TryDecEnv : List AllocEvent → Prop
  g_out0 : RecordGhost
  r_out0 : SessionRecord (List (BitVec 8))
  G_out1 : SessionGhost
  sess_out1 : Session (List (BitVec 8))
  enc_prev1 : List (BitVec 8)

/-- Path B (`Matched` session) Stages P1 → P2 → P3 → P4 envelope. -/
def W4DecryptPrekeyPathBEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (W4StageP2MatchedEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
        P.g_arch P.r_arch P.VecPushEnv)
      (SeqEnv (W4StageP3Env P.TryDecEnv)
        (W4StageP4MatchedCliEnv P.rd P.files P.peersDir P.sessDir P.peer P.g_out0 P.r_out0))) evs

/-- Path A (`0`-prev fresh responder handshake) Stages P1 → P2 → P3 → P4 envelope. -/
def W4DecryptPrekeyPathAEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (W4StageP2PathACliEnv P.hasOpk P.rd P.files P.spkDir P.kpkDir P.opkDir P.ownDir
        P.spkId P.kpkId P.opkId P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
      (SeqEnv (W4StageP3Env P.TryDecEnv)
        (W4StageP4PathACliEnv P.hasOpk P.rd P.files P.peersDir P.kpkDir P.opkDir P.sessDir
          P.peer P.kpkMarkName P.opkId P.g_out0 P.r_out0))) evs

/-- Path C (`Over` / `prev1` responder handshake) Stages P1 → P2 → P3 → P4 envelope. -/
def W4DecryptPrekeyPathCEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (W4StageP2PathCCliEnv P.G_cur P.st_cur P.CurTrialFailEnv P.DecEnv P.TrialEnv P.DropEnv
        P.archivedTrials P.g_arch P.r_arch P.VecPushEnv P.hasOpk P.rd P.files
        P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
        P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
      (SeqEnv (W4StageP3Env P.TryDecEnv)
        (W4StageP4PathCCliEnv P.hasOpk P.rd P.files P.peersDir P.kpkDir P.opkDir P.sessDir
          P.peer P.kpkMarkName P.opkId P.G_out1 P.sess_out1 P.enc_prev1))) evs

/-- 4-arm W4 `decrypt_prekey` (`process_prekey`) slot envelope (`FreeOnlyEvs | Untrusted | PathB | PathA | PathC` + trailing `FreeOnlyEvs`).
-/
def W4DecryptPrekeySlotEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
      W4DecryptPrekeyPathBEnv P e ∨
      W4DecryptPrekeyPathAEnv P e ∨
      W4DecryptPrekeyPathCEnv P e)
    FreeOnlyEvs evs

def w4DecryptPrekeySlotDeltaCum {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap : Nat) : Nat :=
  let cL := w4BoxedStepCum 24 (sessLoadPollDeltaCum cap deserCum)
  let c32 := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
  let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
  let cP1 := cL + c32 + (2 * 40 + 9539)
  let cP2 := (segCloneCum P.G_cur P.st_cur + c_cur + 9923) + 4 * (c_dec + c_tr) +
    5 * c16 + (recordSerializeCum P.g_arch P.r_arch + c_push +
      w4InitBobOuterCum ikmCap + w4SpqrInitCum 32) + 9923
  let cP3 := c_td + 9923
  let cSt0 := w4BoxedStepCum 32
    (sessStorePollDeltaCum (recordSerializeCum P.g_out0 P.r_out0) maxEntries)
  let cSt1 := w4BoxedStepCum 32
    (sessStorePollDeltaCum (serializePrev1Cum P.G_out1 P.sess_out1 P.enc_prev1) maxEntries)
  let cP4 := c32 + c32 + c16 + max cSt0 cSt1
  cP1 + cP2 + cP3 + cP4

def w4DecryptPrekeySlotDeltaLive (M : AllocCostModel) [HasFineReallocCredit M]
    {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserLive l_td : Nat) : Nat :=
  let lL := w4BoxedStepLive 24 (sessLoadPollDeltaLive cap deserLive)
  let l32 := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
  let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
  let lP1 := lL + l32
  let lP2 := 5 * l16 + recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitLive 32
  let lSt0 := w4BoxedStepLive 32
    (sessStorePollDeltaLive (recordSerializeOutLarge M P.g_out0 P.r_out0) maxEntries)
  let lSt1 := w4BoxedStepLive 32
    (sessStorePollDeltaLive (serializePrev1OutLarge M P.G_out1 P.sess_out1 P.enc_prev1) maxEntries)
  let lP4 := l32 + l32 + l16 + max lSt0 lSt1
  lP1 + lP2 + l_td + lP4

def w4DecryptPrekeySlotRawPeak (M : AllocCostModel) [HasFineReallocCredit M]
    {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td : Nat) : Nat :=
  let lL := w4BoxedStepLive 24 (sessLoadPollDeltaLive cap deserLive)
  let pL := w4BoxedStepPeak 24 (sessLoadPollDeltaPeak cap deserPeak)
  let l32 := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
  let p32 := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
  let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
  let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
  let lP1 := lL + l32
  let pP1 := max pL (lL + max p32 l32)
  let lOver := recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitLive 32
  let pOver := max (recordSerializePeak M P.g_arch P.r_arch)
    (recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitPeak 32)
  let pP2Store := max p16 (l16 + max p16 (l16 + max p16 (l16 + max p16
    (l16 + max pOver (lOver + max p16 l16)))))
  let lP2 := 5 * l16 + lOver
  let pP2 := max (segCloneLarge M P.G_cur P.st_cur + p_cur) (max (p_dec + p_tr) pP2Store)
  let pP3 := max p_td l_td
  let pSt0 := w4BoxedStepPeak 32
    (sessStorePollDeltaPeak (recordSerializePeak M P.g_out0 P.r_out0) maxEntries)
  let pSt1 := w4BoxedStepPeak 32
    (sessStorePollDeltaPeak (serializePrev1Peak M P.G_out1 P.sess_out1 P.enc_prev1) maxEntries)
  let pP4 := max p32 (l32 + max p32 (l32 + max p16 (l16 + max pSt0 pSt1)))
  max pP1 (lP1 + max pP2 (lP2 + max pP3 (l_td + pP4)))

/-- Named `Δpeak` bound for `W4DecryptPrekeySlotEnv P` (`max rawPeak live`). -/
def w4DecryptPrekeySlotDeltaPeak (M : AllocCostModel) [HasFineReallocCredit M]
    {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td : Nat) : Nat :=
  max
    (w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td)
    (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)

def w4DecryptPrekeySlotMaxReq {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap : Nat) : Nat :=
  let rL := w4BoxedStepMaxReq 24 (sessLoadPollMaxReq cap deserMaxReq)
  let r32 := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
  let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
  let rSt0 := w4BoxedStepMaxReq 32
    (sessStorePollMaxReq (recordSerializeMaxReq P.g_out0 P.r_out0) maxEntries)
  let rSt1 := w4BoxedStepMaxReq 32
    (sessStorePollMaxReq (serializePrev1MaxReq P.G_out1 P.sess_out1 P.enc_prev1) maxEntries)
  max (max rL (max r32 r16))
    (max (max (max (segCloneMaxReq P.G_cur P.st_cur) r_cur) (max r_dec r_tr))
      (max (max (recordSerializeMaxReq P.g_arch P.r_arch) r_push)
        (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1)))))

/-- Unconditional `decPkLive ≤ decPkPeak` inequality for `w4DecryptPrekeySlotDeltaPeak`. -/
theorem w4DecryptPrekeySlot_live_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td : Nat) :
    w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td ≤
      w4DecryptPrekeySlotDeltaPeak M P cap maxEntries deserLive deserPeak
        p_cur p_dec p_tr l_td p_td :=
  Nat.le_max_right _ _

private theorem max_mono {a a' b b' : Nat} (ha : a ≤ a') (hb : b ≤ b') :
    max a b ≤ max a' b' :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _),
    Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem le_max_right_of_le {x a b : Nat} (h : x ≤ b) : x ≤ max a b :=
  Nat.le_trans h (Nat.le_max_right a b)

private theorem le_max_right2 {x a b c : Nat} (h : x ≤ c) : x ≤ max a (max b c) :=
  le_max_right_of_le (le_max_right_of_le h)

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

private theorem w4InitBobOuterCum_mono {a b : Nat} (h : a ≤ b) :
    w4InitBobOuterCum a ≤ w4InitBobOuterCum b := by
  unfold w4InitBobOuterCum W4InitBobPeak.w4PqxdhAcceptCum
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 9539) 38420) 12677) 9923) 58050

private theorem slotCum_mono_aux
    (cP1 sG c_cur c_cur' c_dec c_dec' c_tr c_tr' c5 cSer c_push c_push'
     cBob cBob' cSpqr cP3 cP4 : Nat)
    (hcur : c_cur ≤ c_cur') (hdec : c_dec ≤ c_dec')
    (htr : c_tr ≤ c_tr') (hpush : c_push ≤ c_push') (hbob : cBob ≤ cBob') :
    cP1 + ((sG + c_cur + 9923) + 4 * (c_dec + c_tr) + c5 +
        (cSer + c_push + cBob + cSpqr) + 9923) + cP3 + cP4 ≤
      cP1 + ((sG + c_cur' + 9923) + 4 * (c_dec' + c_tr') + c5 +
        (cSer + c_push' + cBob' + cSpqr) + 9923) + cP3 + cP4 := by
  omega

private theorem w4DecryptPrekeySlotDeltaCum_mono {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserCum c_cur c_cur' c_dec c_dec' c_tr c_tr' c_push c_push'
     c_td ikmCap ikmCap' : Nat)
    (hcur : c_cur ≤ c_cur') (hdec : c_dec ≤ c_dec')
    (htr : c_tr ≤ c_tr') (hpush : c_push ≤ c_push') (hikm : ikmCap ≤ ikmCap') :
    w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap ≤
      w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum
        c_cur' c_dec' c_tr' c_push' c_td ikmCap' := by
  unfold w4DecryptPrekeySlotDeltaCum
  dsimp only
  exact slotCum_mono_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hcur hdec htr hpush (w4InitBobOuterCum_mono hikm)

private theorem w4DecryptPrekeySlotRawPeak_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserLive deserPeak p_cur p_cur' p_dec p_dec' p_tr p_tr' l_td p_td : Nat)
    (hcur : p_cur ≤ p_cur') (hdec : p_dec ≤ p_dec') (htr : p_tr ≤ p_tr') :
    w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td ≤
      w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak
        p_cur' p_dec' p_tr' l_td p_td := by
  unfold w4DecryptPrekeySlotRawPeak
  dsimp only
  exact seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
    (seqPeak_mono
      (max_mono (Nat.add_le_add_left hcur _)
        (max_mono (Nat.add_le_add hdec htr) (Nat.le_refl _)))
      (Nat.le_refl _) (Nat.le_refl _))

private theorem w4DecryptPrekeySlotMaxReq_mono {α : Type} (P : W4DecryptPrekeySlotParams α)
    (cap maxEntries deserMaxReq r_cur r_cur' r_dec r_dec' r_tr r_tr' r_push r_push'
     r_td ikmCap ikmCap' : Nat)
    (hcur : r_cur ≤ r_cur') (hdec : r_dec ≤ r_dec')
    (htr : r_tr ≤ r_tr') (hpush : r_push ≤ r_push') (hikm : ikmCap ≤ ikmCap') :
    w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap ≤
      w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq
        r_cur' r_dec' r_tr' r_push' r_td ikmCap' := by
  unfold w4DecryptPrekeySlotMaxReq
  dsimp only
  exact max_mono (Nat.le_refl _)
    (max_mono
      (max_mono (max_mono (Nat.le_refl _) hcur) (max_mono hdec htr))
      (max_mono (max_mono (Nat.le_refl _) hpush)
        (max_mono (Nat.le_refl _) (max_mono (max_mono hikm (Nat.le_refl _)) (Nat.le_refl _)))))

private theorem pathB_cum_le
    (cL c32 c16 cSeg cLoop cSer cPush cBob0 cSpqr cP3 cSt0 mSt : Nat)
    (hSt : cSt0 ≤ mSt) :
    (cL + c32) + ((cLoop + (cSer + cPush)) + (cP3 + (c32 + cSt0))) ≤
      (cL + c32 + (2 * 40 + 9539)) +
        ((cSeg + 0 + 9923) + cLoop + 5 * c16 + (cSer + cPush + cBob0 + cSpqr) + 9923) +
        cP3 + (c32 + c32 + c16 + mSt) := by
  omega

private theorem pathB_live_le
    (lP1 l16 lSer lSpqr l_td l32 lSt0 mSt : Nat) (hSt : lSt0 ≤ mSt) :
    lP1 + (lSer + (l_td + (l32 + lSt0))) ≤
      lP1 + (5 * l16 + lSer + lSpqr) + l_td + (l32 + l32 + l16 + mSt) := by
  omega

private theorem pathB_maxReq_le
    (rL r32 r16 rSeg r_dec r_tr rSer r_push r_td rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max (max r_dec r_tr) (max rSer r_push))
        (max (max r_td 192) (max r32 rSt0))) ≤
    max (max rL (max r32 r16))
      (max (max (max rSeg 0) (max r_dec r_tr))
        (max (max rSer r_push)
          (max (max r_td 192) (max (max 0 4224) (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 r16))
    (max (max (max rSeg 0) (max r_dec r_tr))
      (max (max rSer r_push)
        (max (max r_td 192) (max (max 0 4224) (max rSt0 rSt1)))))
  have hA : max rL (max r32 r16) ≤ T := Nat.le_max_left _ _
  have hB : max (max (max rSeg 0) (max r_dec r_tr))
      (max (max rSer r_push)
        (max (max r_td 192) (max (max 0 4224) (max rSt0 rSt1)))) ≤ T := Nat.le_max_right _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have hdt : max r_dec r_tr ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) hB)
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hsp : max rSer r_push ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htd : max r_td 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRR))
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hdt, hsp⟩,
       Nat.max_le.mpr ⟨htd, Nat.max_le.mpr ⟨hr32, hrSt0⟩⟩⟩⟩

private theorem pathA_cum_le
    (cL c32 c16 cSeg cSer cBob cSpqr cP3 cSt0 mSt : Nat) (hSt : cSt0 ≤ mSt) :
    (cL + c32) + ((5 * c16 + cBob + cSpqr + 9923) + (cP3 + (c32 + c32 + c16 + cSt0))) ≤
      (cL + c32 + (2 * 40 + 9539)) +
        ((cSeg + 0 + 9923) + 4 * (0 + 0) + 5 * c16 + (cSer + 0 + cBob + cSpqr) + 9923) +
        cP3 + (c32 + c32 + c16 + mSt) := by
  omega

private theorem pathA_live_le
    (lP1 l16 lSer lSpqr l_td l32 lSt0 mSt : Nat) (hSt : lSt0 ≤ mSt) :
    lP1 + ((5 * l16 + lSpqr) + (l_td + (l32 + l32 + l16 + lSt0))) ≤
      lP1 + (5 * l16 + lSer + lSpqr) + l_td + (l32 + l32 + l16 + mSt) := by
  omega

private theorem pathA_maxReq_le
    (rL r32 r16 rSeg rSer r_td ikmCap rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max (max r16 (max ikmCap 4224))
        (max (max r_td 192) (max (max r32 r32) (max r16 rSt0)))) ≤
    max (max rL (max r32 r16))
      (max (max (max rSeg 0) (max 0 0))
        (max (max rSer 0)
          (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 r16))
    (max (max (max rSeg 0) (max 0 0))
      (max (max rSer 0)
        (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1)))))
  have hA : max rL (max r32 r16) ≤ T := Nat.le_max_left _ _
  have hB : max (max (max rSeg 0) (max 0 0))
      (max (max rSer 0)
        (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1)))) ≤ T :=
    Nat.le_max_right _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr3216 : max r32 r16 ≤ T := Nat.le_trans (Nat.le_max_right _ _) hA
  have hr32 : r32 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr3216
  have hr16 : r16 ≤ T := Nat.le_trans (Nat.le_max_right _ _) hr3216
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htd : max r_td 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt0 : rSt0 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr16, hikm⟩,
       Nat.max_le.mpr ⟨htd,
         Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt0⟩⟩⟩⟩⟩

private theorem pathC_cum_le
    (cL c32 cP2 cP3 c16 cSt1 mSt : Nat) (hSt : cSt1 ≤ mSt) :
    (cL + c32) + (cP2 + (cP3 + (c32 + c32 + c16 + cSt1))) ≤
      (cL + c32 + (2 * 40 + 9539)) + cP2 + cP3 + (c32 + c32 + c16 + mSt) := by
  omega

private theorem pathC_live_le
    (lP1 l16 lSer lSpqr l_td l32 lSt1 mSt : Nat) (hSt : lSt1 ≤ mSt) :
    lP1 + ((5 * l16 + (lSer + lSpqr)) + (l_td + (l32 + l32 + l16 + lSt1))) ≤
      lP1 + (5 * l16 + lSer + lSpqr) + l_td + (l32 + l32 + l16 + mSt) := by
  omega

private theorem pathC_maxReq_le
    (rL r32 r16 rSeg r_cur r_dec r_tr rSer r_push r_td ikmCap rSt0 rSt1 : Nat) :
    max (max rL r32)
      (max
        (max (max (max rSeg r_cur) (max r_dec r_tr))
          (max (max rSer r_push) (max r16 (max ikmCap 4224))))
        (max (max r_td 192) (max (max r32 r32) (max r16 rSt1)))) ≤
    max (max rL (max r32 r16))
      (max (max (max rSeg r_cur) (max r_dec r_tr))
        (max (max rSer r_push)
          (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1))))) := by
  let T := max (max rL (max r32 r16))
    (max (max (max rSeg r_cur) (max r_dec r_tr))
      (max (max rSer r_push)
        (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1)))))
  have hA : max rL (max r32 r16) ≤ T := Nat.le_max_left _ _
  have hB : max (max (max rSeg r_cur) (max r_dec r_tr))
      (max (max rSer r_push)
        (max (max r_td 192) (max (max ikmCap 4224) (max rSt0 rSt1)))) ≤ T := Nat.le_max_right _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr3216 : max r32 r16 ≤ T := Nat.le_trans (Nat.le_max_right _ _) hA
  have hr32 : r32 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hr3216
  have hr16 : r16 ≤ T := Nat.le_trans (Nat.le_max_right _ _) hr3216
  have hBL : max (max rSeg r_cur) (max r_dec r_tr) ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) hB
  have hBR := Nat.le_trans (Nat.le_max_right _ _) hB
  have hsp : max rSer r_push ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBR
  have hBRR := Nat.le_trans (Nat.le_max_right _ _) hBR
  have htd : max r_td 192 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRR
  have hBRRR := Nat.le_trans (Nat.le_max_right _ _) hBRR
  have hikm : max ikmCap 4224 ≤ T := Nat.le_trans (Nat.le_max_left _ _) hBRRR
  have hrSt1 : rSt1 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hBRRR)
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hrL, hr32⟩,
     Nat.max_le.mpr
       ⟨Nat.max_le.mpr ⟨hBL, Nat.max_le.mpr ⟨hsp, Nat.max_le.mpr ⟨hr16, hikm⟩⟩⟩,
        Nat.max_le.mpr ⟨htd,
          Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hr32, hr32⟩, Nat.max_le.mpr ⟨hr16, hrSt1⟩⟩⟩⟩⟩

private theorem untr_maxReq_le
    (rL r32 r16 rRest1 rRest2 r_td rRest3 : Nat) :
    max rL (max r32 40) ≤
      max (max rL (max r32 r16))
        (max rRest1 (max rRest2 (max (max r_td 192) rRest3))) := by
  let T := max (max rL (max r32 r16))
    (max rRest1 (max rRest2 (max (max r_td 192) rRest3)))
  have hA : max rL (max r32 r16) ≤ T := Nat.le_max_left _ _
  have hrL : rL ≤ T := Nat.le_trans (Nat.le_max_left _ _) hA
  have hr32 : r32 ≤ T :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hA)
  have h192 : 192 ≤ T :=
    Nat.le_trans (Nat.le_max_right _ _)
      (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))
  exact Nat.max_le.mpr ⟨hrL, Nat.max_le.mpr ⟨hr32, Nat.le_trans (by decide : 40 ≤ 192) h192⟩⟩

private theorem zero_or_max4_le (x : Nat) :
    max 0 (max (max x x) (max x x)) ≤ x := by
  omega

private theorem slot_final_peak_le (rp l : Nat) :
    max 0 (max (max rp rp) (max rp rp)) ≤ max rp l :=
  Nat.le_trans (zero_or_max4_le rp) (Nat.le_max_left rp l)

theorem w4DecryptPrekeyPathB_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall192 : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push c_td l_td p_td r_td : Nat}
    {l_dec : α → Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec M (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W4DecryptPrekeyPathBEnv P)
      (w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum 0 c_dec c_tr c_push c_td 0)
      (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)
      (w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak 0 p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq 0 r_dec r_tr r_push r_td 0) := by
  dsimp only
  have hP1 := w4StageP1OkCli_phaseCredit hM hdcSess hdcPeers hdir hpeer hfileCap hdeser
  have hP2 := w4StageP2Matched_phaseCredit hM P.g_arch P.r_arch hlen4 hl_le_p hDec hTrial hDrop hPush
  have hP3 := w4StageP3_small_phaseCredit hM hsmall192 hTd
  have hP4 := w4StageP4MatchedCli_phaseCredit hM P.g_out0 P.r_out0 hdcPeers hdcSess
    hdir hpeer hfileCap
  have h34 := hP3.seq hP4
  have h24 := hP2.seq h34
  refine (hP1.seq h24).mono ?_ ?_ ?_ ?_
  · unfold w4DecryptPrekeySlotDeltaCum
    dsimp only
    exact pathB_cum_le _ _ _ _ _ _ _ _ _ _ _ _ (Nat.le_max_left _ _)
  · unfold w4DecryptPrekeySlotDeltaLive
    dsimp only
    exact pathB_live_le _ _ _ _ _ _ _ _ (Nat.le_max_left _ _)
  · unfold w4DecryptPrekeySlotRawPeak
    dsimp only
    have hpOver0 : max (recordSerializePeak M P.g_arch P.r_arch)
        (recordSerializeOutLarge M P.g_arch P.r_arch) ≤
        max (recordSerializePeak M P.g_arch P.r_arch)
          (recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitPeak 32) :=
      max_mono (Nat.le_refl _) (Nat.le_add_right _ _)
    have hlP2 : recordSerializeOutLarge M P.g_arch P.r_arch ≤
        5 * w4BoxedStepLive 16 (smallStorePollDeltaLive (max maxVal fileCap) maxEntries) +
          (recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitLive 32) :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    exact fourStagePeak_mono
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
      (Nat.le_refl _)
      (le_max_right_of_le
        (max_mono (Nat.le_refl _)
          (Nat.le_trans hpOver0 (le_fiveStepPeak_inner _ _ _ _))))
      hlP2
      (Nat.le_refl _)
      (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (le_twoStepPeak_left _ _ _ _ _ _))
  · unfold w4DecryptPrekeySlotMaxReq
    dsimp only
    exact pathB_maxReq_le _ _ _ _ _ _ _ _ _ _ _

theorem w4DecryptPrekeyPathA_small_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td ikmCap : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W4DecryptPrekeyPathAEnv P)
      (w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum 0 0 0 0 c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)
      (w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak 0 0 0 l_td p_td)
      (w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq 0 0 0 0 r_td ikmCap) := by
  dsimp only
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hP1 := w4StageP1OkCli_phaseCredit hM hdcSess hdcPeers hdir hpeer hfileCap hdeser
  have hP2 := w4StageP2PathACli_small_phaseCredit hM P.hasOpk P.spkId P.kpkId P.opkId
    P.F P.x_spqr hdcSpk hdcKpk hdcOpk hdcOwn hdir hkeyName hregName
    hold hnew hSmall hspqrKey hfileCap
  have hP3 := w4StageP3_small_phaseCredit hM hSm192 hTd
  have hP4 := w4StageP4PathACli_phaseCredit hM P.hasOpk P.opkId P.g_out0 P.r_out0
    hdcPeers hdcKpk hdcOpk hdcSess hdir hpeer hkpkMark hfileCap
  have h34 := hP3.seq hP4
  have h24 := hP2.seq h34
  refine (hP1.seq h24).mono ?_ ?_ ?_ ?_
  · unfold w4DecryptPrekeySlotDeltaCum
    dsimp only
    exact pathA_cum_le _ _ _ _ _ _ _ _ _ _ (Nat.le_max_left _ _)
  · unfold w4DecryptPrekeySlotDeltaLive
    dsimp only
    exact pathA_live_le _ _ _ _ _ _ _ _ (Nat.le_max_left _ _)
  · unfold w4DecryptPrekeySlotRawPeak
    dsimp only
    have hpOver : w4SpqrInitPeak 32 ≤
        max (recordSerializePeak M P.g_arch P.r_arch)
          (recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitPeak 32) :=
      Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _)
    have hlOver : w4SpqrInitLive 32 ≤
        recordSerializeOutLarge M P.g_arch P.r_arch + w4SpqrInitLive 32 :=
      Nat.le_add_left _ _
    exact fourStagePeak_mono
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
      (Nat.le_refl _)
      (le_max_right2 (fiveStepPeak_mono (seqPeak_mono hpOver hlOver (Nat.le_refl _))))
      (Nat.add_le_add_left hlOver _)
      (Nat.le_refl _)
      (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
          (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))))
  · unfold w4DecryptPrekeySlotMaxReq
    dsimp only
    exact pathA_maxReq_le _ _ _ _ _ _ _ _ _

theorem w4DecryptPrekeyPathC_small_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td ikmCap : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec M P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec M (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W4DecryptPrekeyPathCEnv P)
      (w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)
      (w4DecryptPrekeySlotRawPeak M P cap maxEntries deserLive deserPeak p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap) := by
  dsimp only
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hP1 := w4StageP1OkCli_phaseCredit hM hdcSess hdcPeers hdir hpeer hfileCap hdeser
  have hP2 := w4StageP2PathCCli_small_phaseCredit hM P.G_cur P.st_cur P.g_arch P.r_arch
    P.hasOpk P.spkId P.kpkId P.opkId P.F P.x_spqr
    hCurTrial hlen4 hl_le_p hDec hTrial hDrop hPush
    hdcSpk hdcKpk hdcOpk hdcOwn hdir hkeyName hregName
    hold hnew hSmall hspqrKey hfileCap
  have hP3 := w4StageP3_small_phaseCredit hM hSm192 hTd
  have hP4 := w4StageP4PathCCli_phaseCredit hM P.hasOpk P.opkId P.G_out1 P.sess_out1 P.enc_prev1
    hdcPeers hdcKpk hdcOpk hdcSess hdir hpeer hkpkMark hfileCap
  have h34 := hP3.seq hP4
  have h24 := hP2.seq h34
  refine (hP1.seq h24).mono ?_ ?_ ?_ ?_
  · unfold w4DecryptPrekeySlotDeltaCum
    dsimp only
    exact pathC_cum_le _ _ _ _ _ _ _ (Nat.le_max_right _ _)
  · unfold w4DecryptPrekeySlotDeltaLive
    dsimp only
    exact pathC_live_le _ _ _ _ _ _ _ _ (Nat.le_max_right _ _)
  · unfold w4DecryptPrekeySlotRawPeak
    dsimp only
    exact fourStagePeak_mono
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_left _ _))
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
        (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _)
          (seqPeak_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_max_right _ _))))
  · unfold w4DecryptPrekeySlotMaxReq
    dsimp only
    exact pathC_maxReq_le _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Small-regime 4-arm `PhaseCreditSpec` for `W4DecryptPrekeySlotEnv P` (`max ikmCap 1569 ≤ smallMaxReq M`).
-/
theorem w4DecryptPrekeySlot_small_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W4DecryptPrekeySlotParams α)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td ikmCap : Nat}
    {l_dec : α → Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSpk : DirDomainCaps maxDir maxEntries maxVal P.spkDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal P.kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal P.opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec M P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec M (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeySlotDeltaCum P cap maxEntries deserCum c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P cap maxEntries deserLive l_td)
      (w4DecryptPrekeySlotDeltaPeak M P cap maxEntries deserLive deserPeak
        p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P cap maxEntries deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap) := by
  dsimp only
  have hSm40 : 40 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 40 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hUntr0 := w4StageP1UntrustedCli_small_phaseCredit hM hSm40 hdcSess hdcPeers
    hdir hpeer hfileCap hdeser
  have hUntr : PhaseCreditSpec M
      (W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (w4DecryptPrekeySlotDeltaCum P (max maxVal fileCap) maxEntries deserCum
        c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P (max maxVal fileCap) maxEntries deserLive l_td)
      (w4DecryptPrekeySlotRawPeak M P (max maxVal fileCap) maxEntries deserLive deserPeak
        p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P (max maxVal fileCap) maxEntries deserMaxReq
        r_cur r_dec r_tr r_push r_td ikmCap) := by
    refine hUntr0.mono ?_ ?_ ?_ ?_
    · unfold w4DecryptPrekeySlotDeltaCum
      dsimp only
      exact Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · unfold w4DecryptPrekeySlotDeltaLive
      dsimp only
      exact Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · unfold w4DecryptPrekeySlotRawPeak
      dsimp only
      exact Nat.le_max_left _ _
    · unfold w4DecryptPrekeySlotMaxReq
      dsimp only
      exact untr_maxReq_le _ _ _ _ _ _ _
  have hB := (w4DecryptPrekeyPathB_phaseCredit hM hSm192 P hdcPeers hdcSess hdir hpeer
    hfileCap hdeser hlen4 hl_le_p hDec hTrial hDrop hPush hTd).mono
    (w4DecryptPrekeySlotDeltaCum_mono P (max maxVal fileCap) maxEntries deserCum
      0 c_cur c_dec c_dec c_tr c_tr c_push c_push c_td 0 ikmCap
      (Nat.zero_le _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.zero_le _))
    (Nat.le_refl _)
    (w4DecryptPrekeySlotRawPeak_mono M P (max maxVal fileCap) maxEntries deserLive deserPeak
      0 p_cur p_dec p_dec p_tr p_tr l_td p_td
      (Nat.zero_le _) (Nat.le_refl _) (Nat.le_refl _))
    (w4DecryptPrekeySlotMaxReq_mono P (max maxVal fileCap) maxEntries deserMaxReq
      0 r_cur r_dec r_dec r_tr r_tr r_push r_push r_td 0 ikmCap
      (Nat.zero_le _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.zero_le _))
  have hA := (w4DecryptPrekeyPathA_small_phaseCredit hM P hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk
    hdcSess hdir hpeer hkeyName hregName hkpkMark hold hnew hSmall hspqrKey hfileCap hdeser hTd).mono
    (w4DecryptPrekeySlotDeltaCum_mono P (max maxVal fileCap) maxEntries deserCum
      0 c_cur 0 c_dec 0 c_tr 0 c_push c_td ikmCap ikmCap
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _))
    (Nat.le_refl _)
    (w4DecryptPrekeySlotRawPeak_mono M P (max maxVal fileCap) maxEntries deserLive deserPeak
      0 p_cur 0 p_dec 0 p_tr l_td p_td
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
    (w4DecryptPrekeySlotMaxReq_mono P (max maxVal fileCap) maxEntries deserMaxReq
      0 r_cur 0 r_dec 0 r_tr 0 r_push r_td ikmCap ikmCap
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _))
  have hC := w4DecryptPrekeyPathC_small_phaseCredit hM P hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk
    hdcSess hdir hpeer hkeyName hregName hkpkMark hold hnew hSmall hspqrKey hfileCap hdeser
    hCurTrial hlen4 hl_le_p hDec hTrial hDrop hPush hTd
  have h4 := phaseCreditSpec_or4 (fun _ h => h) hUntr hB hA hC
  have hSeq := phaseCreditSpec_seq_freeOnly_exact hM h4
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  refine (hFree.or hSeq).mono ?_ ?_ ?_ ?_
  · exact zero_or_max4_le _
  · exact zero_or_max4_le _
  · unfold w4DecryptPrekeySlotDeltaPeak
    exact slot_final_peak_le _ _
  · exact zero_or_max4_le _

/-- Freshly opened CLI `StoresGhost.opened` specialization of `w4DecryptPrekeySlot_small_phaseCredit`.
-/
theorem w4DecryptPrekeySlot_opened_small_phaseCredit {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W4DecryptPrekeySlotParams α)
    {fileCap deserCum deserLive deserPeak deserMaxReq
     c_cur p_cur r_cur c_dec p_dec r_dec c_tr p_tr r_tr c_push r_push
     c_td l_td p_td r_td ikmCap : Nat}
    {l_dec : α → Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSpk : P.spkDir = StoresGhost.opened.signed)
    (hKpk : P.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            P.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hOpk : P.opkDir = StoresGhost.opened.oneTime)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hkpkMark : P.kpkMarkName.length ≤ 64)
    (hold : P.x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hCurTrial : PhaseCreditSpec M P.CurTrialFailEnv c_cur 0 p_cur r_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hl_le_p : ∀ x ∈ P.archivedTrials, l_dec x ≤ p_dec)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.DecEnv x) c_dec (l_dec x) p_dec r_dec)
    (hTrial : ∀ x ∈ P.archivedTrials, PhaseCreditSpec M (P.TrialEnv x) c_tr 0 p_tr r_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, DeallocCreditSpec M (P.DropEnv x) (l_dec x))
    (hPush : PhaseCreditSpec M P.VecPushEnv c_push 0 0 r_push)
    (hTd : PhaseCreditSpec M P.TryDecEnv c_td l_td p_td r_td) :
    PhaseCreditSpec M (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeySlotDeltaCum P fileCap 0 deserCum c_cur c_dec c_tr c_push c_td ikmCap)
      (w4DecryptPrekeySlotDeltaLive M P fileCap 0 deserLive l_td)
      (w4DecryptPrekeySlotDeltaPeak M P fileCap 0 deserLive deserPeak
        p_cur p_dec p_tr l_td p_td)
      (w4DecryptPrekeySlotMaxReq P fileCap 0 deserMaxReq r_cur r_dec r_tr r_push r_td ikmCap) := by
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
  have h := w4DecryptPrekeySlot_small_phaseCredit hM P
    hdcOwn hdcPeers hdcSpk hdcKpk hdcOpk hdcSess (by decide)
    hpeer hkeyName hregName hkpkMark hold hnew hSmall hspqrKey
    hfileCap hdeser hCurTrial hlen4 hl_le_p hDec hTrial hDrop hPush hTd
  simpa only [Nat.zero_max] using h

/-! ## 5. Outer `SlotW4` / `R3b` Wire and Slot Composition -/

/-- Outer `R3b` / `SlotW4` envelope (`PksmTryFromBoundedEnv x_pksm → DecPkEnv → FreeOnlyEvs`). -/
def W4SlotR3bEnv (x_pksm : PksmGhost) (DecPkEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (PksmTryFromBoundedEnv x_pksm)
    (fun evs2 => FreeOnlyEvs evs2 ∨ SeqEnv DecPkEnv FreeOnlyEvs evs2) evs

def w4SlotR3bDeltaCum (x_pksm : PksmGhost) (decCum : Nat) : Nat :=
  pksmTryFromDeltaCum x_pksm + decCum

def w4SlotR3bDeltaLive (x_pksm : PksmGhost) (decLive : Nat) : Nat :=
  pksmTryFromDeltaLive x_pksm + decLive

def w4SlotR3bDeltaPeak (x_pksm : PksmGhost) (decLive decPeak : Nat) : Nat :=
  max
    (max (pksmTryFromDeltaPeak x_pksm) (pksmTryFromDeltaLive x_pksm + decPeak))
    (w4SlotR3bDeltaLive x_pksm decLive)

def w4SlotR3bMaxReq (x_pksm : PksmGhost) (decMaxReq : Nat) : Nat :=
  max (pksmTryFromMaxReq x_pksm) decMaxReq

theorem w4SlotR3b_live_le_peak (x_pksm : PksmGhost) (decLive decPeak : Nat) :
    w4SlotR3bDeltaLive x_pksm decLive ≤ w4SlotR3bDeltaPeak x_pksm decLive decPeak :=
  Nat.le_max_right _ _

private theorem r3b_peak_le (p1 l1 p2 l2 : Nat) :
    max 0 (max p1 (l1 + max 0 p2)) ≤ max (max p1 (l1 + p2)) (l1 + l2) := by
  simp only [Nat.zero_max]
  exact Nat.le_max_left _ _

/-- Outer `SlotW4` / `R3b` `PhaseCreditSpec` composing `WirePksmTryFromPeakSpec.pksmTryFrom_phaseCredit` with `DecPkEnv`.
-/
theorem w4SlotR3b_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x_pksm : PksmGhost)
    {DecPkEnv : List AllocEvent → Prop} {decCum decLive decPeak decMaxReq : Nat}
    (hDec : PhaseCreditSpec M DecPkEnv decCum decLive decPeak decMaxReq) :
    PhaseCreditSpec M (W4SlotR3bEnv x_pksm DecPkEnv)
      (w4SlotR3bDeltaCum x_pksm decCum)
      (w4SlotR3bDeltaLive x_pksm decLive)
      (w4SlotR3bDeltaPeak x_pksm decLive decPeak)
      (w4SlotR3bMaxReq x_pksm decMaxReq) := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  have hPksm := pksmTryFrom_phaseCredit hM hLow x_pksm
  have hDecFree := phaseCreditSpec_seq_freeOnly_exact hM hDec
  have hTail := hFree.or hDecFree
  have hSeq := hPksm.seq hTail
  refine (hFree.or hSeq).mono ?_ ?_ ?_ ?_
  · unfold w4SlotR3bDeltaCum
    simp only [Nat.zero_max]
    exact Nat.le_refl _
  · unfold w4SlotR3bDeltaLive
    simp only [Nat.zero_max]
    exact Nat.le_refl _
  · unfold w4SlotR3bDeltaPeak w4SlotR3bDeltaLive
    exact r3b_peak_le _ _ _ _
  · unfold w4SlotR3bMaxReq
    simp only [Nat.zero_max]
    exact Nat.le_refl _

theorem w4SlotR3b_fine_phaseCredit (x_pksm : PksmGhost)
    {DecPkEnv : List AllocEvent → Prop} {decCum decLive decPeak decMaxReq : Nat}
    (hDec : PhaseCreditSpec fineCostModel DecPkEnv decCum decLive decPeak decMaxReq) :
    PhaseCreditSpec fineCostModel (W4SlotR3bEnv x_pksm DecPkEnv)
      (w4SlotR3bDeltaCum x_pksm decCum)
      (w4SlotR3bDeltaLive x_pksm decLive)
      (w4SlotR3bDeltaPeak x_pksm decLive decPeak)
      (w4SlotR3bMaxReq x_pksm decMaxReq) :=
  w4SlotR3b_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps x_pksm hDec

/-!
## 6. Widened Binary-Complete Stage and 4-Arm Slot Envelopes

Binary-complete widenings covering Stage P3 `SegCloneEnv` and `17`-byte `"decryption failed"` error
tails (`W4ErrTailWideEnv`, `W4StageP3WideEnv`), Stage P2 Path B `PublicKey::serialize` and mismatch
strings (`W4StageP2MatchedWideEnv`), and early-reject prefix exits across Stages P2–P4
(`OptStageEnv`, `W4DecryptPrekeySplitWideSlotEnv`).
-/

section WidenedBinaryCompleteEnvelopes

open CryptoVerification.SignalSession.Cli (addressText)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BobSessionBuildEnv W4PqxdhAcceptEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromFEnv FromMEnv FromVPostTdEnv SegTailEnv)

/-! ### 6.1 Optional-Step Combinator (`OptStageEnv`) -/

/-- Optional stage/step wrapper (`FreeOnlyEvs ∨ E`). -/
def OptStageEnv (E : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ E evs

theorem optStageEnv_nil (E : List AllocEvent → Prop) : OptStageEnv E [] :=
  Or.inl fun _ h => nomatch h

theorem optStageEnv_of_freeOnly {E : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) : OptStageEnv E evs :=
  Or.inl h

theorem optStageEnv_of_self {E : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : E evs) : OptStageEnv E evs :=
  Or.inr h

theorem seqEnv_freeOnly_to_opt {A B : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv A FreeOnlyEvs evs) : SeqEnv A (OptStageEnv B) evs :=
  SeqCreditKit.SeqEnv.mono (fun _ ha => ha) (fun _ hf => Or.inl hf) h

theorem seqEnv_freeOnly_to_seq_opt {A B Rest : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv A FreeOnlyEvs evs) : SeqEnv A (SeqEnv (OptStageEnv B) Rest) evs :=
  SeqCreditKit.SeqEnv.mono (fun _ ha => ha) (fun _ hf => Or.inl (Or.inl hf)) h

theorem phaseCredit_optStageEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (OptStageEnv E) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).or h).mono
    (Nat.zero_max c ▸ Nat.le_refl c)
    (Nat.zero_max l ▸ Nat.le_refl l)
    (Nat.zero_max p ▸ Nat.le_refl p)
    (Nat.zero_max r ▸ Nat.le_refl r)

/-! ### 6.2 Widened Error-Return Tail (`W4ErrTailWideEnv`) -/

/-- Widened stage error tail covering `W4ErrTailEnv`, `FromFEnv`, and `FromMEnv`. -/
def W4ErrTailWideEnv (evs : List AllocEvent) : Prop :=
  W4ErrTailEnv evs ∨ FromFEnv evs ∨ FromMEnv evs

theorem w4ErrTailWideEnv_of_w4ErrTailEnv {evs : List AllocEvent}
    (h : W4ErrTailEnv evs) : W4ErrTailWideEnv evs :=
  Or.inl h

theorem w4ErrTailWideEnv_of_freeOnly {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) : W4ErrTailWideEnv evs :=
  Or.inl (Or.inl h)

theorem w4ErrTailWideEnv_of_fromFEnv {evs : List AllocEvent}
    (h : FromFEnv evs) : W4ErrTailWideEnv evs :=
  Or.inr (Or.inl h)

theorem w4ErrTailWideEnv_of_fromMEnv {evs : List AllocEvent}
    (h : FromMEnv evs) : W4ErrTailWideEnv evs :=
  Or.inr (Or.inr h)

theorem w4ErrTailWideEnv_of_fromVPostTdEnv {evs : List AllocEvent}
    (h : FromVPostTdEnv evs) : W4ErrTailWideEnv evs := by
  rcases h with hf | hm
  · exact Or.inl (Or.inl hf)
  · exact Or.inr (Or.inr hm)

/-- Widened failed cloned-session `try_decrypt_pq` trial on Stage P2 Path C. -/
def W4TryDecryptCloneFailWideEnv
    (CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (ConcatEnv (ConcatEnv CloneEnv TrialFailEnv) DropCloneEnv)
    W4ErrTailWideEnv evs

theorem w4TryDecryptCloneFailWideEnv_of_narrow
    {CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : W4TryDecryptCloneFailEnv CloneEnv TrialFailEnv DropCloneEnv evs) :
    W4TryDecryptCloneFailWideEnv CloneEnv TrialFailEnv DropCloneEnv evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hc => hc) (fun _ ht => Or.inl (Or.inr ht)) h

/-! ### 6.3 Widened Stage P2 (`Matched`, `PathA`, `PathC`) Envelopes -/

/-- Post-`PublicKey::serialize` optional mismatch/error-string tail on Stage P2 Path B. -/
def W4StageP2MatchedErrStrEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (· = rustAllocEvents 70 1) FreeOnlyEvs evs ∨
  SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs evs

/-- Stage P2 Path B direct-match / mismatch check prefix. -/
def W4StageP2MatchedCheckEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (· = rustAllocEvents 33 1)
    (SeqEnv (· = rustDeallocEvents 33 1) W4StageP2MatchedErrStrEnv) evs

theorem w4StageP2MatchedCheckEnv_nil : W4StageP2MatchedCheckEnv [] :=
  Or.inl fun _ h => nomatch h

theorem w4StageP2MatchedCheckEnv_of_freeOnly {evs : List AllocEvent}
    (h : FreeOnlyEvs evs) : W4StageP2MatchedCheckEnv evs :=
  Or.inl h

theorem w4StageP2MatchedCheckEnv_of_bridge33 {evs : List AllocEvent}
    (h : SeqEnv (· = rustAllocEvents 33 1) (SeqEnv (· = rustDeallocEvents 33 1) FreeOnlyEvs) evs) :
    W4StageP2MatchedCheckEnv evs :=
  Or.inr (SeqCreditKit.SeqEnv.mono (fun _ ha => ha)
    (fun _ hd => SeqCreditKit.SeqEnv.mono (fun _ hfree => hfree) (fun _ hf => Or.inl hf) hd) h)

theorem w4StageP2MatchedCheckEnv_of_mismatch70 {evs : List AllocEvent}
    (h : SeqEnv (· = rustAllocEvents 33 1)
      (SeqEnv (· = rustDeallocEvents 33 1)
        (SeqEnv (· = rustAllocEvents 70 1) FreeOnlyEvs)) evs) :
    W4StageP2MatchedCheckEnv evs :=
  Or.inr (SeqCreditKit.SeqEnv.mono (fun _ ha => ha)
    (fun _ hd => SeqCreditKit.SeqEnv.mono (fun _ hfree => hfree)
      (fun _ h70 => Or.inr (Or.inl h70)) hd) h)

theorem w4StageP2MatchedCheckEnv_of_err14 {evs : List AllocEvent}
    (h : SeqEnv (· = rustAllocEvents 33 1)
      (SeqEnv (· = rustDeallocEvents 33 1)
        (SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs)) evs) :
    W4StageP2MatchedCheckEnv evs :=
  Or.inr (SeqCreditKit.SeqEnv.mono (fun _ ha => ha)
    (fun _ hd => SeqCreditKit.SeqEnv.mono (fun _ hfree => hfree)
      (fun _ h14 => Or.inr (Or.inr h14)) hd) h)

/-- Widened Stage P2 Path B (`Matched`) envelope. -/
def W4StageP2MatchedWideEnv {α : Type}
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (VecPushEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv W4StageP2MatchedCheckEnv
    (OptStageEnv (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)) evs

theorem w4StageP2MatchedWideEnv_of_check {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : W4StageP2MatchedCheckEnv evs) :
    W4StageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv evs :=
  Or.inl h

theorem w4StageP2MatchedWideEnv_of_narrow {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv evs) :
    W4StageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv evs :=
  Or.inr ⟨[], evs, rfl, w4StageP2MatchedCheckEnv_nil, Or.inr h⟩

/-- `9`-allocation responder session-build envelope (`≤ 9` small ops `≤ 68` B + `FreeOnlyEvs`). -/
def W4BobSessionBuildEnv9 : List AllocEvent → Prop :=
  SeqEnv (W4InitBobPeak.W4BoundedEvs 9 68) FreeOnlyEvs

def w4InitBobOuterCum9 (ikmCap : Nat) : Nat :=
  W4InitBobPeak.w4PqxdhAcceptCum ikmCap + 87075

theorem w4BobSessionBuildEnv_sub_env9 {evs : List AllocEvent}
    (h : W4BobSessionBuildEnv evs) : W4BobSessionBuildEnv9 evs :=
  SeqCreditKit.SeqEnv.mono
    (fun _ hb => ⟨Nat.le_trans hb.1 (by decide), hb.2⟩)
    (fun _ hf => hf) h

theorem phaseCredit_w4BobSessionBuild9_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall68 : 68 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M W4BobSessionBuildEnv9 87075 0 0 68 :=
  (phaseCreditSpec_seq_freeOnly_exact hM
    (W4InitBobPeak.phaseCredit_w4BoundedEvs_small hM 9 68 hSmall68)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 68)

theorem w4InitBobOuterCum_le_9 (ikmCap : Nat) :
    w4InitBobOuterCum ikmCap ≤ w4InitBobOuterCum9 ikmCap := by
  unfold w4InitBobOuterCum w4InitBobOuterCum9
  omega

/-- Widened `initialize_bob_session` envelope over `W4BobSessionBuildEnv9` with early error exit after `W4PqxdhAcceptEnv`.
-/
def W4InitBobWideEnv (x_res : DoReserveCall) (hasOpk : Bool)
    (E_spqrInit : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4PqxdhAcceptEnv x_res hasOpk)
    (OptStageEnv (SeqEnv E_spqrInit (OptStageEnv W4BobSessionBuildEnv9))) evs

abbrev W4InitBobSpqrWideEnv (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) (evs : List AllocEvent) : Prop :=
  W4InitBobWideEnv x_res hasOpk (InitialStateEnv F x_spqr) evs

theorem w4InitBobWideEnv_of_narrow {x_res : DoReserveCall} {hasOpk : Bool}
    {E_spqrInit : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : W4InitBobPeak.W4InitBobEnv x_res hasOpk E_spqrInit evs) :
    W4InitBobWideEnv x_res hasOpk E_spqrInit evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hp => hp)
    (fun _ hs => Or.inr
      (SeqCreditKit.SeqEnv.mono (fun _ hq => hq)
        (fun _ hb => Or.inr (w4BobSessionBuildEnv_sub_env9 hb)) hs)) h

/-- Widened `Over`-path responder initialization envelope. -/
def W4StageP2OverBobWideEnv
    (SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop)
    (x_res : DoReserveCall) (hasOpk : Bool)
    (E_spqrInit : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (PromoteStateArchiveEnv SerializeArchivedEnv VecPushEnv))
    (OptStageEnv (W4InitBobWideEnv x_res hasOpk E_spqrInit)) evs

theorem w4StageP2OverBobWideEnv_of_narrow
    {SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop}
    {x_res : DoReserveCall} {hasOpk : Bool}
    {E_spqrInit : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : W4StageP2OverBobEnv SerializeArchivedEnv VecPushEnv x_res hasOpk E_spqrInit evs) :
    W4StageP2OverBobWideEnv SerializeArchivedEnv VecPushEnv x_res hasOpk E_spqrInit evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hp => Or.inr hp)
    (fun _ hb => Or.inr (w4InitBobWideEnv_of_narrow hb)) h

/-- Widened Stage P2 Path A (`0`-prev) CLI envelope wrapping each step in `OptStageEnv`. -/
def W4StageP2PathACliWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files spkDir (keyName spkId)))
    (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files kpkDir (keyName kpkId)))
      (SeqEnv
        (OptStageEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = [])))
        (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files ownDir ownKeyName))
          (SeqEnv (OptStageEnv (W4InitBobSpqrWideEnv F x_res hasOpk x_spqr))
            (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName))
              W4ErrTailWideEnv))))) evs

theorem w4StageP2PathACliWideEnv_of_narrow
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    {spkId kpkId opkId : BitVec 32}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_res : DoReserveCall} {x_spqr : InitialStateGhost}
    {evs : List AllocEvent}
    (h : W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir
      spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr evs) :
    W4StageP2PathACliWideEnv hasOpk rd files spkDir kpkDir opkDir ownDir
      spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr evs :=
  SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x)
    (fun _ x => SeqCreditKit.SeqEnv.mono (fun _ y => Or.inr y)
      (fun _ y => SeqCreditKit.SeqEnv.mono (fun _ z => Or.inr z)
        (fun _ z => SeqCreditKit.SeqEnv.mono (fun _ w => Or.inr w)
          (fun _ w => SeqCreditKit.SeqEnv.mono
            (fun _ u => Or.inr (w4InitBobWideEnv_of_narrow u))
            (fun _ u => SeqCreditKit.SeqEnv.mono (fun _ v => Or.inr v)
              (fun _ t => Or.inl t) u) w) z) y) x) h

/-- Widened Stage P2 Path C (`Over` / `prev1`) CLI envelope. -/
def W4StageP2PathCCliWideEnv {α : Type}
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (CurTrialFailEnv : List AllocEvent → Prop)
    (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (VecPushEnv : List AllocEvent → Prop)
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (OptStageEnv
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur)))
    (SeqEnv
      (OptStageEnv (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs))
      (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files spkDir (keyName spkId)))
        (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files kpkDir (keyName kpkId)))
          (SeqEnv
            (OptStageEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = [])))
            (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files ownDir ownKeyName))
              (SeqEnv
                (OptStageEnv
                  (W4StageP2OverBobWideEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
                    x_res hasOpk (InitialStateEnv F x_spqr)))
                (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 16 rd files ownDir ownRegName))
                  W4ErrTailWideEnv))))))) evs

theorem w4StageP2PathCCliWideEnv_of_narrow {α : Type}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {spkDir kpkDir opkDir ownDir : DirGhost}
    {spkId kpkId opkId : BitVec 32}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_res : DoReserveCall} {x_spqr : InitialStateGhost}
    {evs : List AllocEvent}
    (h : W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
      g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
      spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr evs) :
    W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
      g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
      spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr evs :=
  SeqCreditKit.SeqEnv.mono
    (fun _ e1 => e1.elim Or.inl (fun hc => Or.inr (w4TryDecryptCloneFailWideEnv_of_narrow hc)))
    (fun _ x => SeqCreditKit.SeqEnv.mono (fun _ e2 => e2)
      (fun _ y => SeqCreditKit.SeqEnv.mono (fun _ z => Or.inr z)
        (fun _ z => SeqCreditKit.SeqEnv.mono (fun _ w => Or.inr w)
          (fun _ w => SeqCreditKit.SeqEnv.mono (fun _ u => Or.inr u)
            (fun _ u => SeqCreditKit.SeqEnv.mono (fun _ v => Or.inr v)
              (fun _ v => SeqCreditKit.SeqEnv.mono
                (fun _ ob => Or.inr (w4StageP2OverBobWideEnv_of_narrow ob))
                (fun _ r => SeqCreditKit.SeqEnv.mono (fun _ s => Or.inr s)
                  (fun _ t => Or.inl t) r) v) u) w) z) y) x) h

/-! ### 6.4 Widened Stage P3 (`W4StageP3WideEnv`) -/

/-- Widened Stage P3 envelope (`CloneEnv → OptStageEnv TryDecEnv → W4ErrTailWideEnv`). -/
def W4StageP3WideEnv (CloneEnv TryDecEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv CloneEnv (SeqEnv (OptStageEnv TryDecEnv) W4ErrTailWideEnv) evs

theorem w4StageP3WideEnv_of_okPrefix {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SeqEnv CloneEnv (SeqEnv TryDecEnv FreeOnlyEvs) evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hc => hc)
    (fun _ ht => SeqCreditKit.SeqEnv.mono (fun _ hd => Or.inr hd)
      (fun _ hf => w4ErrTailWideEnv_of_freeOnly hf) ht) h

theorem w4StageP3WideEnv_of_err {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SeqEnv CloneEnv (SeqEnv TryDecEnv FromVPostTdEnv) evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hc => hc)
    (fun _ ht => SeqCreditKit.SeqEnv.mono (fun _ hd => Or.inr hd)
      (fun _ hv => w4ErrTailWideEnv_of_fromVPostTdEnv hv) ht) h

theorem w4StageP3WideEnv_of_verNe {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SeqEnv CloneEnv FromMEnv evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hc => hc)
    (fun e2 hm => Or.inr ⟨[], e2, rfl, optStageEnv_nil TryDecEnv, Or.inr (Or.inr hm)⟩) h

theorem w4StageP3WideEnv_of_fromF {CloneEnv TryDecEnv : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SeqEnv CloneEnv FromFEnv evs) :
    W4StageP3WideEnv CloneEnv TryDecEnv evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hc => hc)
    (fun e2 hf => Or.inr ⟨[], e2, rfl, optStageEnv_nil TryDecEnv, Or.inr (Or.inl hf)⟩) h

/-! ### 6.5 Widened Stage P4 Early-Reject Envelopes -/

/-- Widened Stage P4 Path B (`Matched`) CLI envelope. -/
def W4StageP4MatchedCliWideEnv (rd : ReadRule) (files : FsFiles)
    (peersDir sessDir : DirGhost) (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)))
    (SeqEnv (OptStageEnv (W4SessStoreStepEnv sessDir peer g_rec r_rec)) FreeOnlyEvs) evs

theorem w4StageP4MatchedCliWideEnv_of_narrow
    {rd : ReadRule} {files : FsFiles} {peersDir sessDir : DirGhost} {peer : AddrGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec evs) :
    W4StageP4MatchedCliWideEnv rd files peersDir sessDir peer g_rec r_rec evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs)
    (fun _ hst => SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x) (fun _ hf => hf) hst) h

theorem w4StageP4MatchedCliWideEnv_of_saveErr
    {rd : ReadRule} {files : FsFiles} {peersDir sessDir : DirGhost} {peer : AddrGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)) FreeOnlyEvs evs) :
    W4StageP4MatchedCliWideEnv rd files peersDir sessDir peer g_rec r_rec evs :=
  seqEnv_freeOnly_to_seq_opt (SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs) (fun _ hf => hf) h)

/-- Widened Stage P4 Path A (`0`-prev) CLI envelope. -/
def W4StageP4PathACliWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)))
    (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName))
      (SeqEnv
        (OptStageEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = [])))
        (SeqEnv (OptStageEnv (W4SessStoreStepEnv sessDir peer g_rec r_rec)) FreeOnlyEvs))) evs

theorem w4StageP4PathACliWideEnv_of_narrow
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId g_rec r_rec evs) :
    W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId g_rec r_rec evs :=
  SeqCreditKit.SeqEnv.mono (fun _ s1 => Or.inr s1)
    (fun _ x => SeqCreditKit.SeqEnv.mono (fun _ s2 => Or.inr s2)
      (fun _ y => SeqCreditKit.SeqEnv.mono (fun _ s3 => Or.inr s3)
        (fun _ z => SeqCreditKit.SeqEnv.mono (fun _ s4 => Or.inr s4) (fun _ hf => hf) z) y) x) h

theorem w4StageP4PathACliWideEnv_of_saveErr
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)) FreeOnlyEvs evs) :
    W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId g_rec r_rec evs :=
  seqEnv_freeOnly_to_seq_opt (SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs) (fun _ hf => hf) h)

theorem w4StageP4PathACliWideEnv_of_markErr
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName) FreeOnlyEvs) evs) :
    W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId g_rec r_rec evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs)
    (fun _ hm => seqEnv_freeOnly_to_seq_opt
      (SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x) (fun _ hf => hf) hm)) h

theorem w4StageP4PathACliWideEnv_of_removeErr
    {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName)
        (SeqEnv (W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId)) FreeOnlyEvs)) evs) :
    W4StageP4PathACliWideEnv true rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId g_rec r_rec evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs)
    (fun _ hm => SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x)
      (fun _ hr => seqEnv_freeOnly_to_seq_opt
        (SeqCreditKit.SeqEnv.mono (fun _ y => Or.inr y) (fun _ hf => hf) hr)) hm) h

/-- Widened Stage P4 Path C (`prev1`) CLI envelope. -/
def W4StageP4PathCCliWideEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)))
    (SeqEnv (OptStageEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName))
      (SeqEnv
        (OptStageEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = [])))
        (SeqEnv (OptStageEnv (W4SessStorePrev1StepEnv sessDir peer G sess enc)) FreeOnlyEvs))) evs

theorem w4StageP4PathCCliWideEnv_of_narrow
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId G sess enc evs) :
    W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId G sess enc evs :=
  SeqCreditKit.SeqEnv.mono (fun _ s1 => Or.inr s1)
    (fun _ x => SeqCreditKit.SeqEnv.mono (fun _ s2 => Or.inr s2)
      (fun _ y => SeqCreditKit.SeqEnv.mono (fun _ s3 => Or.inr s3)
        (fun _ z => SeqCreditKit.SeqEnv.mono (fun _ s4 => Or.inr s4) (fun _ hf => hf) z) y) x) h

theorem w4StageP4PathCCliWideEnv_of_saveErr
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)) FreeOnlyEvs evs) :
    W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId G sess enc evs :=
  seqEnv_freeOnly_to_seq_opt (SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs) (fun _ hf => hf) h)

theorem w4StageP4PathCCliWideEnv_of_markErr
    {hasOpk : Bool} {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName) FreeOnlyEvs) evs) :
    W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId G sess enc evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs)
    (fun _ hm => seqEnv_freeOnly_to_seq_opt
      (SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x) (fun _ hf => hf) hm)) h

theorem w4StageP4PathCCliWideEnv_of_removeErr
    {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} {opkId : BitVec 32}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName)
        (SeqEnv (W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId)) FreeOnlyEvs)) evs) :
    W4StageP4PathCCliWideEnv true rd files peersDir kpkDir opkDir sessDir peer
      kpkName opkId G sess enc evs :=
  SeqCreditKit.SeqEnv.mono (fun _ hs => Or.inr hs)
    (fun _ hm => SeqCreditKit.SeqEnv.mono (fun _ x => Or.inr x)
      (fun _ hr => seqEnv_freeOnly_to_seq_opt
        (SeqCreditKit.SeqEnv.mono (fun _ y => Or.inr y) (fun _ hf => hf) hr)) hm) h

/-! ### 6.6 Widened 4-Arm `W4DecryptPrekeySplitWideSlotEnv` -/

/-- Widened Path B (`Matched`) Stages P1 → P2 → P3 → P4 envelope parameterized by `CloneB`. -/
def W4DecryptPrekeyPathBWideEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneB : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (OptStageEnv
        (W4StageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          P.g_arch P.r_arch P.VecPushEnv))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv CloneB P.TryDecEnv))
        (OptStageEnv
          (W4StageP4MatchedCliWideEnv P.rd P.files P.peersDir P.sessDir P.peer
            P.g_out0 P.r_out0)))) evs

/-- Widened Path A (`0`-prev) Stages P1 → P2 → P3 → P4 envelope parameterized by `CloneAC` and `TryDecAC`.
-/
def W4DecryptPrekeyPathAWideEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (OptStageEnv
        (W4StageP2PathACliWideEnv P.hasOpk P.rd P.files P.spkDir P.kpkDir P.opkDir P.ownDir
          P.spkId P.kpkId P.opkId P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv CloneAC TryDecAC))
        (OptStageEnv
          (W4StageP4PathACliWideEnv P.hasOpk P.rd P.files P.peersDir P.kpkDir P.opkDir P.sessDir
            P.peer P.kpkMarkName P.opkId P.g_out0 P.r_out0)))) evs

/-- Widened Path C (`prev1`) Stages P1 → P2 → P3 → P4 envelope parameterized by `CloneAC` and `TryDecAC`.
-/
def W4DecryptPrekeyPathCWideEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
    (SeqEnv
      (OptStageEnv
        (W4StageP2PathCCliWideEnv P.G_cur P.st_cur P.CurTrialFailEnv P.DecEnv P.TrialEnv P.DropEnv
          P.archivedTrials P.g_arch P.r_arch P.VecPushEnv P.hasOpk P.rd P.files
          P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
          P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv CloneAC TryDecAC))
        (OptStageEnv
          (W4StageP4PathCCliWideEnv P.hasOpk P.rd P.files P.peersDir P.kpkDir P.opkDir P.sessDir
            P.peer P.kpkMarkName P.opkId P.G_out1 P.sess_out1 P.enc_prev1)))) evs

/-- Widened 4-arm W4 `decrypt_prekey` (`process_prekey`) slot envelope splitting `CloneB` (Path B) and `CloneAC` (Paths A & C).
-/
def W4DecryptPrekeySplitWideSlotEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneB CloneAC TryDecAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
      W4DecryptPrekeyPathBWideEnv P CloneB e ∨
      W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e ∨
      W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e)
    FreeOnlyEvs evs

abbrev W4DecryptPrekeyWideSlotEnv {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneB CloneAC : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC P.TryDecEnv evs

theorem w4DecryptPrekeyPathBWideEnv_of_p2Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneB : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          P.g_arch P.r_arch P.VecPushEnv)
        FreeOnlyEvs) evs) :
    W4DecryptPrekeyPathBWideEnv P CloneB evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => seqEnv_freeOnly_to_seq_opt
      (SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2) (fun _ hf => hf) h2)) h

theorem w4DecryptPrekeyPathAWideEnv_of_p2Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2PathACliWideEnv P.hasOpk P.rd P.files P.spkDir P.kpkDir P.opkDir P.ownDir
          P.spkId P.kpkId P.opkId P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
        FreeOnlyEvs) evs) :
    W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => seqEnv_freeOnly_to_seq_opt
      (SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2) (fun _ hf => hf) h2)) h

theorem w4DecryptPrekeyPathCWideEnv_of_p2Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2PathCCliWideEnv P.G_cur P.st_cur P.CurTrialFailEnv P.DecEnv P.TrialEnv P.DropEnv
          P.archivedTrials P.g_arch P.r_arch P.VecPushEnv P.hasOpk P.rd P.files
          P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
          P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
        FreeOnlyEvs) evs) :
    W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => seqEnv_freeOnly_to_seq_opt
      (SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2) (fun _ hf => hf) h2)) h

theorem w4DecryptPrekeyPathBWideEnv_of_p3Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneB : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          P.g_arch P.r_arch P.VecPushEnv)
        (SeqEnv (W4StageP3WideEnv CloneB P.TryDecEnv) FreeOnlyEvs)) evs) :
    W4DecryptPrekeyPathBWideEnv P CloneB evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2)
      (fun _ h3 => seqEnv_freeOnly_to_opt
        (SeqCreditKit.SeqEnv.mono (fun _ hp3 => Or.inr hp3) (fun _ hf => hf) h3)) h2) h

theorem w4DecryptPrekeyPathAWideEnv_of_p3Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2PathACliWideEnv P.hasOpk P.rd P.files P.spkDir P.kpkDir P.opkDir P.ownDir
          P.spkId P.kpkId P.opkId P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
        (SeqEnv (W4StageP3WideEnv CloneAC TryDecAC) FreeOnlyEvs)) evs) :
    W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2)
      (fun _ h3 => seqEnv_freeOnly_to_opt
        (SeqCreditKit.SeqEnv.mono (fun _ hp3 => Or.inr hp3) (fun _ hf => hf) h3)) h2) h

theorem w4DecryptPrekeyPathCWideEnv_of_p3Exit {α : Type} (P : W4DecryptPrekeySlotParams α)
    (CloneAC TryDecAC : List AllocEvent → Prop) {evs : List AllocEvent}
    (h : SeqEnv (W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer)
      (SeqEnv
        (W4StageP2PathCCliWideEnv P.G_cur P.st_cur P.CurTrialFailEnv P.DecEnv P.TrialEnv P.DropEnv
          P.archivedTrials P.g_arch P.r_arch P.VecPushEnv P.hasOpk P.rd P.files
          P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
          P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
        (SeqEnv (W4StageP3WideEnv CloneAC TryDecAC) FreeOnlyEvs)) evs) :
    W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC evs :=
  SeqCreditKit.SeqEnv.mono (fun _ h1 => h1)
    (fun _ h2 => SeqCreditKit.SeqEnv.mono (fun _ hp2 => Or.inr hp2)
      (fun _ h3 => seqEnv_freeOnly_to_opt
        (SeqCreditKit.SeqEnv.mono (fun _ hp3 => Or.inr hp3) (fun _ hf => hf) h3)) h2) h

/-- Allocating non-vacuity witness for `W4DecryptPrekeySplitWideSlotEnv`. -/
theorem w4DecryptPrekeySplitWideSlotEnv_nonvacuous_alloc {α : Type}
    (P : W4DecryptPrekeySlotParams α) (CloneB CloneAC TryDecAC : List AllocEvent → Prop)
    {evs₁ : List AllocEvent}
    (hP1 : W4StageP1OkCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer evs₁) :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ (.alloc 33 ∈ evs) ∧
      W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC evs := by
  refine ⟨evs₁ ++ [.alloc 33, .free 1 33], ?_, ?_, ?_⟩
  · intro hnil
    have hmem : AllocEvent.alloc 33 ∈ evs₁ ++ [.alloc 33, .free 1 33] :=
      List.mem_append.mpr (Or.inr List.mem_cons_self)
    rw [hnil] at hmem
    nomatch hmem
  · exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  · refine Or.inr (Or.inl (Or.inr (Or.inl ?_)))
    refine Or.inr ⟨evs₁, [.alloc 33, .free 1 33], rfl, hP1, Or.inl (Or.inr ?_)⟩
    refine w4StageP2MatchedWideEnv_of_check (w4StageP2MatchedCheckEnv_of_bridge33 ?_)
    exact Or.inr ⟨[.alloc 33], [.free 1 33], rfl, rfl, Or.inl rfl⟩

end WidenedBinaryCompleteEnvelopes

end LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
