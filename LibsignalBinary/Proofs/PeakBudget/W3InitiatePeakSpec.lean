/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateHelpers
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak

/-!
# Peak Live-Heap Interface for W3 `process_prekey_bundle`

Symbolic `(M : AllocCostModel) [HasFineReallocCredit M]` `PhaseCreditSpec` bounds in binary execution
order for `signal_session_handshake::initiate` (`process_prekey_bundle`, Stages 1–5): boxed-future
CLI store steps (`W3BoxedStoreStepEnv`), Stage 4 `StepSpqr` integration, and end-to-end 5-stage
`W3InitiateSlotEnv` theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps addressText_length_le dirDomainCaps_opened_own
   dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   boxAlloc_phaseCredit
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessLoadPoll_phaseCredit
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   sessStorePoll_phaseCredit
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq
   smallStorePoll_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (initialState_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateAffinePeak
  (phaseCreditSpec_w3InitiateFull_aff phaseCreditSpec_w3Stage1_aff
   phaseCreditSpec_w3Stage2_aff phaseCreditSpec_w3Stage3_aff
   phaseCreditSpec_w3Stage4_aff phaseCreditSpec_w3Stage5_aff
   w3InitiateNativeAffLive)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (W3BoundedEvs W3InitiateFullEnv W3Stage1Env W3Stage23BracketEnv W3Stage2Env
   W3Stage4Env W3Stage5Env
   phaseCreditSpec_seq_freeOnly phaseCreditSpec_w3InitiateFull_small
   phaseCreditSpec_w3Stage1_small phaseCreditSpec_w3Stage23_bracket_aff
   phaseCreditSpec_w3Stage2_small phaseCreditSpec_w3Stage3_small
   phaseCreditSpec_w3Stage4_small phaseCreditSpec_w3Stage5_small
   w3InitiateNativeSmallCum)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

/-! ## 1. CLI Boxed-Future Async Store-Step Wrappers -/

/-- Boxed-future async store step (`BoxAllocEnv boxSz` → `E_poll` → `FreeOnlyEvs`). -/
def W3BoxedStoreStepEnv (boxSz : Nat) (E_poll : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll FreeOnlyEvs) evs

def w3BoxedStepCum (boxSz pollCum : Nat) : Nat := (2 * boxSz + 9539) + pollCum
def w3BoxedStepLive (boxSz pollLive : Nat) : Nat := (boxSz + 8195) + pollLive
def w3BoxedStepPeak (boxSz pollPeak : Nat) : Nat := (boxSz + 8195) + pollPeak
def w3BoxedStepMaxReq (boxSz pollMaxReq : Nat) : Nat := max boxSz pollMaxReq

theorem w3BoxedStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {E_poll : List AllocEvent → Prop}
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M (W3BoxedStoreStepEnv boxSz E_poll)
      (w3BoxedStepCum boxSz c_p)
      (w3BoxedStepLive boxSz l_p)
      (w3BoxedStepPeak boxSz p_p)
      (w3BoxedStepMaxReq boxSz r_p) := by
  have hbox := boxAlloc_phaseCredit hM boxSz
  have hpollF := phaseCreditSpec_seq_freeOnly hM hpoll
  exact (hbox.seq hpollF).mono
    (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩)
    (Nat.le_refl _)

/-- Small-store async step (`idTrust`, `idKeyPair`, `idRegId`, `idSave`). -/
def W3SmallStoreStepEnv (boxSz : Nat) (rd : ReadRule) (files : FsFiles)
    (dir : DirGhost) (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  W3BoxedStoreStepEnv boxSz (CliSmallStorePollEnv rd files dir name) evs

theorem w3SmallStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W3SmallStoreStepEnv boxSz rd files dir name)
      (w3BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (w3BoxedStepLive boxSz (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (w3BoxedStepPeak boxSz (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
      (w3BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w3BoxedStoreStep_phaseCredit hM boxSz (smallStorePoll_phaseCredit hM hdc hdir hname hcap)

/-- Stage 1 `load_session` async step. -/
def W3SessLoadStepEnv (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (sessDir : DirGhost) (peer : AddrGhost)
    (evs : List AllocEvent) : Prop :=
  W3BoxedStoreStepEnv 24 (CliSessLoadPollEnv rd DeserEnv files sessDir peer) evs

theorem w3SessLoadStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M (W3SessLoadStepEnv rd DeserEnv files sessDir peer)
      (w3BoxedStepCum 24 (sessLoadPollDeltaCum (max maxVal fileCap) deserCum))
      (w3BoxedStepLive 24 (sessLoadPollDeltaLive (max maxVal fileCap) deserLive))
      (w3BoxedStepPeak 24 (sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak))
      (w3BoxedStepMaxReq 24 (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq)) :=
  w3BoxedStoreStep_phaseCredit hM 24 (sessLoadPoll_phaseCredit hM hdc hdir hpeer hcap hdeser)

/-- Stage 5 `store_session` async step (`0`-prev). -/
def W3SessStoreStepEnv (sessDir : DirGhost) (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  W3BoxedStoreStepEnv 32 (CliSessStorePollEnv sessDir peer g_rec r_rec) evs

theorem w3SessStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M (W3SessStoreStepEnv sessDir peer g_rec r_rec)
      (w3BoxedStepCum 32 (sessStorePollDeltaCum (recordSerializeCum g_rec r_rec) maxEntries))
      (w3BoxedStepLive 32 (sessStorePollDeltaLive (recordSerializeOutLarge M g_rec r_rec) maxEntries))
      (w3BoxedStepPeak 32 (sessStorePollDeltaPeak (recordSerializePeak M g_rec r_rec) maxEntries))
      (w3BoxedStepMaxReq 32 (sessStorePollMaxReq (recordSerializeMaxReq g_rec r_rec) maxEntries)) :=
  w3BoxedStoreStep_phaseCredit hM 32 (sessStorePoll_phaseCredit hM hdc hpeer)

/-! ## 2. Stage 4 `StepSpqr` Integration -/

/-- Stage 4 envelope (`create_chain` → `InitialStateEnv F x_spqr` → `SessionState` construction). -/
def W3Stage4SpqrEnv (F : ShaCompress) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent) : Prop :=
  W3Stage4Env (InitialStateEnv F x_spqr) evs

def w3SpqrInitReq (authKeyLen : Nat) : Nat := 4 * authKeyLen + 4096
def w3SpqrInitCum (authKeyLen : Nat) : Nat := 128 * (2 * w3SpqrInitReq authKeyLen + 9539)
def w3SpqrInitLive (authKeyLen : Nat) : Nat := 128 * (w3SpqrInitReq authKeyLen + 8195)
def w3SpqrInitPeak (authKeyLen : Nat) : Nat := 128 * (w3SpqrInitReq authKeyLen + 8195)

theorem w3Stage4Spqr_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x_spqr : InitialStateGhost) :
    let k := x_spqr.p.authKey.length
    PhaseCreditSpec M (W3Stage4SpqrEnv F x_spqr)
      ((2 * 33 + 9539) + w3SpqrInitCum k + 13 * (2 * 416 + 9539))
      ((33 + 8195) + w3SpqrInitLive k + 13 * (416 + 8195))
      ((33 + 8195) + max (w3SpqrInitPeak k) (w3SpqrInitLive k + 13 * (416 + 8195)))
      (max 416 (w3SpqrInitReq k)) :=
  phaseCreditSpec_w3Stage4_aff hM (initialState_phaseCreditSpec hM F x_spqr)

theorem w3SpqrInit32_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hkey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec M (InitialStateEnv F x_spqr)
      (w3SpqrInitCum 32) (w3SpqrInitLive 32) (w3SpqrInitPeak 32) 4224 := by
  have h0 := initialState_phaseCreditSpec hM F x_spqr
  have hreq : w3SpqrInitReq x_spqr.p.authKey.length ≤ w3SpqrInitReq 32 := by
    dsimp [w3SpqrInitReq]; omega
  have hcum : w3SpqrInitCum x_spqr.p.authKey.length ≤ w3SpqrInitCum 32 :=
    Nat.mul_le_mul_left 128 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hreq) 9539)
  have hlive : w3SpqrInitLive x_spqr.p.authKey.length ≤ w3SpqrInitLive 32 :=
    Nat.mul_le_mul_left 128 (Nat.add_le_add_right hreq 8195)
  exact h0.mono hcum hlive hlive hreq

/-- `32`-byte root-key specialization (`x_spqr.p.authKey.length ≤ 32`) for `W3Stage4SpqrEnv`. -/
theorem w3Stage4Spqr32_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hkey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec M (W3Stage4SpqrEnv F x_spqr)
      ((2 * 33 + 9539) + w3SpqrInitCum 32 + 13 * (2 * 416 + 9539))
      ((33 + 8195) + w3SpqrInitLive 32 + 13 * (416 + 8195))
      ((33 + 8195) + (w3SpqrInitLive 32 + 13 * (416 + 8195)))
      4224 := by
  have hspqr := w3SpqrInit32_phaseCredit hM F x_spqr hkey
  exact (phaseCreditSpec_w3Stage4_aff hM hspqr).mono
    (Nat.le_refl _)
    (Nat.le_refl _)
    (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩) _)
    (by decide)

theorem w3Stage4Spqr32_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 416 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hkey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec M (W3Stage4SpqrEnv F x_spqr)
      ((2 * 33 + 9539) + w3SpqrInitCum 32 + 13 * (2 * 416 + 9539))
      (w3SpqrInitLive 32)
      (w3SpqrInitPeak 32)
      4224 := by
  have hspqr := w3SpqrInit32_phaseCredit hM F x_spqr hkey
  exact (phaseCreditSpec_w3Stage4_small hM hsmall hspqr).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_of_eq (Nat.max_self _)) (by decide)

/-! ## 3. End-to-End 5-Stage `W3InitiateSlotEnv` Peak Bounds -/

/-- Bundled arguments for a W3 `process_prekey_bundle` CLI slot invocation across Stages 1–5. -/
structure W3InitiateSlotParams where
  rd : ReadRule
  DeserEnv : List (BitVec 8) → List AllocEvent → Prop
  files : FsFiles
  ownDir : DirGhost
  peersDir : DirGhost
  sessDir : DirGhost
  peer : AddrGhost
  ownKeyName : List (BitVec 8)
  ownRegName : List (BitVec 8)
  F : ShaCompress
  x_spqr : InitialStateGhost
  g_rec : RecordGhost
  r_rec : SessionRecord (List (BitVec 8))

/-- 5-stage `process_prekey_bundle` (`initiate`) allocation envelope (`Stage 1 → ... → Stage 5`). -/
def W3InitiateSlotEnv (P : W3InitiateSlotParams) (evs : List AllocEvent) : Prop :=
  W3InitiateFullEnv
    (W3SmallStoreStepEnv 32 P.rd P.files P.peersDir (addressText P.peer.val))
    (W3SessLoadStepEnv P.rd P.DeserEnv P.files P.sessDir P.peer)
    (W3SmallStoreStepEnv 16 P.rd P.files P.ownDir P.ownKeyName)
    (InitialStateEnv P.F P.x_spqr)
    (W3SmallStoreStepEnv 16 P.rd P.files P.ownDir P.ownRegName)
    (W3SmallStoreStepEnv 32 P.rd P.files P.peersDir (addressText P.peer.val))
    (W3SessStoreStepEnv P.sessDir P.peer P.g_rec P.r_rec)
    P.peer.name.bytes.length
    evs

def w3InitiateSlotDeltaCum (fileCap maxEntries deserCum serCum : Nat) : Nat :=
  w3InitiateNativeSmallCum +
  w3BoxedStepCum 32 (smallStorePollDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 24 (sessLoadPollDeltaCum fileCap deserCum) +
  w3BoxedStepCum 16 (smallStorePollDeltaCum fileCap maxEntries) +
  w3SpqrInitCum 32 +
  w3BoxedStepCum 16 (smallStorePollDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 32 (smallStorePollDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 32 (sessStorePollDeltaCum serCum maxEntries)

def w3InitiateSlotDeltaLive (fileCap maxEntries deserLive serLive : Nat) : Nat :=
  w3InitiateNativeAffLive +
  w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 24 (sessLoadPollDeltaLive fileCap deserLive) +
  w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
  w3SpqrInitLive 32 +
  w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (sessStorePollDeltaLive serLive maxEntries)

def w3InitiateSlotSmallDeltaLive (fileCap maxEntries deserLive serLive : Nat) : Nat :=
  w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 24 (sessLoadPollDeltaLive fileCap deserLive) +
  w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
  w3SpqrInitLive 32 +
  w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (sessStorePollDeltaLive serLive maxEntries)

def w3InitiateSlotDeltaPeak
    (fileCap maxEntries deserLive deserPeak serPeak : Nat) : Nat :=
  let l_t := w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries)
  let p_t := w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_sl := w3BoxedStepLive 24 (sessLoadPollDeltaLive fileCap deserLive)
  let p_sl := w3BoxedStepPeak 24 (sessLoadPollDeltaPeak fileCap deserPeak)
  let l_k := w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries)
  let p_k := w3BoxedStepPeak 16 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_q := w3SpqrInitLive 32
  let p_q := w3SpqrInitPeak 32
  let l_r := w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries)
  let p_r := w3BoxedStepPeak 16 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_i := w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries)
  let p_i := w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries)
  let p_ss := w3BoxedStepPeak 32 (sessStorePollDeltaPeak serPeak maxEntries)
  let l1 := l_t + ((33 + 8195) + (1569 + 8195) + l_sl)
  let p1 := max p_t (l_t + ((33 + 8195) + (1569 + 8195) + p_sl))
  let l2 := l_k + (1568 + 8195)
  let p2 := max p_k (l_k + (1568 + 8195))
  let l3 := 8 * (1569 + 8195)
  let l4 := (33 + 8195) + l_q + 13 * (416 + 8195)
  let p4 := (33 + 8195) + max p_q (l_q + 13 * (416 + 8195))
  let p5 := 4 * (68 + 8195) + max p_r (l_r + max p_i (l_i + p_ss))
  p1 + l1 + p2 + l2 + l3 + l3 + p4 + l4 + p5

def w3InitiateSlotSmallDeltaPeak
    (fileCap maxEntries deserLive deserPeak serPeak : Nat) : Nat :=
  let l_t := w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries)
  let p_t := w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_sl := w3BoxedStepLive 24 (sessLoadPollDeltaLive fileCap deserLive)
  let p_sl := w3BoxedStepPeak 24 (sessLoadPollDeltaPeak fileCap deserPeak)
  let l_k := w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries)
  let p_k := w3BoxedStepPeak 16 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_q := w3SpqrInitLive 32
  let p_q := w3SpqrInitPeak 32
  let l_r := w3BoxedStepLive 16 (smallStorePollDeltaLive fileCap maxEntries)
  let p_r := w3BoxedStepPeak 16 (smallStorePollDeltaPeak fileCap maxEntries)
  let l_i := w3BoxedStepLive 32 (smallStorePollDeltaLive fileCap maxEntries)
  let p_i := w3BoxedStepPeak 32 (smallStorePollDeltaPeak fileCap maxEntries)
  let p_ss := w3BoxedStepPeak 32 (sessStorePollDeltaPeak serPeak maxEntries)
  let l12 := l_t + l_sl + l_k
  let l14 := l12 + l_q
  max
    (max
      (max (max p_t (l_t + p_sl)) (l_t + l_sl + max p_k l_k))
      (max l12 (l12 + max p_q l_q)))
    (l14 + max p_r (l_r + max p_i (l_i + p_ss)))

def w3InitiateSlotMaxReq (fileCap maxEntries deserMaxReq serMaxReq : Nat) : Nat :=
  let r_sm32 := w3BoxedStepMaxReq 32 (smallStorePollMaxReq fileCap maxEntries)
  let r_sm16 := w3BoxedStepMaxReq 16 (smallStorePollMaxReq fileCap maxEntries)
  let r_sl := w3BoxedStepMaxReq 24 (sessLoadPollMaxReq fileCap deserMaxReq)
  let r_ss := w3BoxedStepMaxReq 32 (sessStorePollMaxReq serMaxReq maxEntries)
  max 1569 (max r_sm32 (max r_sl (max r_sm16 (max 4224 (max r_sm16 (max r_sm32 r_ss))))))

/-- Regime-free W3 `process_prekey_bundle` (`W3InitiateSlotEnv`) `PhaseCreditSpec M`. -/
theorem w3InitiateSlot_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3InitiateSlotDeltaCum cap maxEntries deserCum (recordSerializeCum P.g_rec P.r_rec))
      (w3InitiateSlotDeltaLive cap maxEntries deserLive (recordSerializeOutLarge M P.g_rec P.r_rec))
      (w3InitiateSlotDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak M P.g_rec P.r_rec))
      (w3InitiateSlotMaxReq cap maxEntries deserMaxReq (recordSerializeMaxReq P.g_rec P.r_rec)) := by
  intro cap
  have haddrLen : (addressText P.peer.val).length ≤ 64 := by
    have h51 := addressText_length_le P.peer.val
    rw [show P.peer.val.name = P.peer.name.bytes from rfl] at h51
    omega
  have htrust := w3SmallStoreStep_phaseCredit hM 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hload := w3SessLoadStep_phaseCredit hM hdcSess hdir hpeer
    (fun bs hr => hfileCap _ bs hr) hdeser
  have hkp := w3SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hspqr := w3SpqrInit32_phaseCredit hM P.F P.x_spqr hspqrKey
  have hreg := w3SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hsave := w3SmallStoreStep_phaseCredit hM 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hstore := w3SessStoreStep_phaseCredit hM P.g_rec P.r_rec hdcSess hpeer
  exact phaseCreditSpec_w3InitiateFull_aff hM hpeer htrust hload hkp hspqr hreg hsave hstore

/-- Small-regime (`1569 ≤ smallMaxReq M`) W3 `process_prekey_bundle` `PhaseCreditSpec M`. -/
theorem w3InitiateSlot_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3InitiateSlotDeltaCum cap maxEntries deserCum (recordSerializeCum P.g_rec P.r_rec))
      (w3InitiateSlotSmallDeltaLive cap maxEntries deserLive
        (recordSerializeOutLarge M P.g_rec P.r_rec))
      (w3InitiateSlotSmallDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak M P.g_rec P.r_rec))
      (w3InitiateSlotMaxReq cap maxEntries deserMaxReq (recordSerializeMaxReq P.g_rec P.r_rec)) := by
  intro cap
  have haddrLen : (addressText P.peer.val).length ≤ 64 := by
    have h51 := addressText_length_le P.peer.val
    rw [show P.peer.val.name = P.peer.name.bytes from rfl] at h51
    omega
  have htrust := w3SmallStoreStep_phaseCredit hM 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hload := w3SessLoadStep_phaseCredit hM hdcSess hdir hpeer
    (fun bs hr => hfileCap _ bs hr) hdeser
  have hkp := w3SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hspqr := w3SpqrInit32_phaseCredit hM P.F P.x_spqr hspqrKey
  have hreg := w3SmallStoreStep_phaseCredit hM 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hsave := w3SmallStoreStep_phaseCredit hM 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hstore := w3SessStoreStep_phaseCredit hM P.g_rec P.r_rec hdcSess hpeer
  exact phaseCreditSpec_w3InitiateFull_small hM hpeer hsmall htrust hload hkp hspqr hreg hsave hstore

/-- Freshly opened CLI `StoresGhost.opened` specialization of `w3InitiateSlot_phaseCredit`. -/
theorem w3InitiateSlot_opened_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (P : W3InitiateSlotParams)
    {fileCap : Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hDeserNil : ∀ bs, P.DeserEnv bs = (· = []))
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3InitiateSlotDeltaCum fileCap 0 0 (recordSerializeCum P.g_rec P.r_rec))
      (w3InitiateSlotDeltaLive fileCap 0 0 (recordSerializeOutLarge M P.g_rec P.r_rec))
      (w3InitiateSlotDeltaPeak fileCap 0 0 0 (recordSerializePeak M P.g_rec P.r_rec))
      (w3InitiateSlotMaxReq fileCap 0 0 (recordSerializeMaxReq P.g_rec P.r_rec)) := by
  have hdcOwn : DirDomainCaps 26 0 0 P.ownDir := hOwn ▸ dirDomainCaps_opened_own
  have hdcPeers : DirDomainCaps 26 0 0 P.peersDir := hPeers ▸ dirDomainCaps_opened_peers
  have hdcSess : DirDomainCaps 26 0 0 P.sessDir := hSess ▸ dirDomainCaps_opened_sess
  have hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseCreditSpec M (P.DeserEnv bs) 0 0 0 0 := by
    intro bs _
    rw [hDeserNil bs]
    exact PhaseCreditSpec.nil M
  have h := w3InitiateSlot_phaseCredit hM P hdcOwn hdcPeers hdcSess (by decide)
    hpeer hkeyName hregName hspqrKey hfileCap hdeser
  simpa only [Nat.zero_max] using h

end LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
