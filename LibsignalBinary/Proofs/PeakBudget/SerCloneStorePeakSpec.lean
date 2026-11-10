/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Peak Live-Heap Interface for `SessionRecord::serialize`, `SessionClone`, and CLI `StoreKits`

Combines:
1. `SessionStructure::clone` (`SegCloneEnv`) and `sc = 63` `dropClonedSessionEvents` cancellation
   (`SessionCloneCredit`);
2. `0`-prev and `prev1` `SessionRecord::serialize` (`RecordSerializeCancelEnv`,
   `SerializePrev1CancelEnv`, `SessionSerializeCredit`);
3. Generic `BoundedRustEvs` and `BoxAllocEnv` combinators;
4. CLI `StoreKits` poll envelopes (`CliSessLoadPollEnv`, `CliSessStorePollEnv`,
   `CliSessStorePollPrev1Env`, `CliSmallStorePollEnv`, and tight per-size-class specializations)
   and their `PhaseCreditSpec` bounds under `DirDomainCaps`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec

open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule addressText decimalText pathOf utf8)
open VerifiedLibraries.Mallocng (mallocngAlignedEffSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps addressText_length_le)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliAddrTextEnv CliDecimalEnv CliDirGetEnv CliDirPutEnv CliDirPutStrEnv CliPathEnv
   addrTextDeltaCum addrTextDeltaLive addrTextDeltaPeak addrTextMaxReq addrText_phaseCredit
   allocBytes1DeltaCum allocBytes1DeltaLive allocBytes1DeltaPeak
   decimalDeltaCum decimalDeltaLive decimalDeltaPeak decimal_phaseCredit
   dirGetRuleDeltaCum dirGetRuleDeltaLive dirGetRuleDeltaPeak dirGetRuleMaxReq dirGet_rule_phaseCredit
   dirPutDeltaCum dirPutDeltaLive dirPutDeltaPeak dirPutMaxReq dirPut_phaseCredit
   dirPutStrDeltaCum dirPutStrDeltaLive dirPutStrDeltaPeak dirPutStrMaxReq dirPutStr_phaseCredit
   growOneDirDeltaCum growOneDirDeltaLive growOneDirDeltaPeak growOneDirMaxReq
   pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq
   readFileCliIoDeltaCum readFileCliIoDeltaLive readFileCliIoDeltaPeak readFileCliIoMaxReq
   readFileRuleDeltaCum readFileRuleDeltaLive readFileRuleDeltaPeak readFileRuleMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (dropClonedSessionEvents optLargeCost optLargeCost_le_add
   segCloneCum segCloneLarge segCloneMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeCancelEnv SerializePrev1CancelEnv
   recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak
   serializePrev1Cum serializePrev1MaxReq serializePrev1OutLarge serializePrev1Peak)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## 1. Re-Exports & Generic `BoundedRustEvs` / `BoxAllocEnv` Combinators -/

export SessionCloneCredit (dropClonedSessionEvents optLargeCost)
export SessionSerializeCredit (RecordSerializeCancelEnv SerializePrev1CancelEnv)

private theorem eventStepReq_le_reqBytes_local (ev : AllocEvent) :
    eventStepReq ev ≤ ev.reqBytes := by
  cases ev with
  | alloc req => exact Nat.le_refl req
  | aligned al req =>
    simp only [eventStepReq, AllocEvent.reqBytes, mallocngAlignedEffSize]
    split <;> omega
  | free _ _ => exact Nat.zero_le 0
  | realloc _ _ newSz => exact Nat.le_refl newSz

private theorem seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : SeqCreditKit.FreeNonInc M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r where
  req_align evs hE ev hev := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.req_align evs h1 ev hev
    · rcases List.mem_append.mp hev with he1 | he2
      · exact h.req_align evs₁ h1 ev he1
      · obtain ⟨al, sz, rfl⟩ := h2 ev he2
        exact ⟨Nat.zero_le r, Nat.le_refl 16⟩
  credit_le st0 {_} hE := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.credit_le st0 h1
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hc₁, hl₁, hp₁⟩ := h.credit_le st0 h1
      obtain ⟨hc₂, hl₂, hp₂⟩ := SeqCreditKit.stepEvents_freeOnly_le hF h2 (M.stepEvents evs₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

private theorem boundedRustEvs_event_bounds {maxReq : Nat} {ev : AllocEvent}
    (hreq : ev.reqBytes ≤ maxReq)
    (hal : ∀ al r, ev = .aligned al r → al ≤ 16)
    (hre : ∀ al o n, ev = .realloc al o n → al ≤ 16) :
    eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  refine ⟨Nat.le_trans (eventStepReq_le_reqBytes_local ev) hreq, ?_⟩
  cases ev with
  | alloc _ => exact Nat.le_refl 16
  | aligned al r => exact hal al r rfl
  | free _ _ => exact Nat.le_refl 16
  | realloc al o n => exact hre al o n rfl

private theorem stepEvents_boundedRustEvs_aux {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} :
    ∀ (evs : List AllocEvent) (st0 : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + evs.length * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 + evs.length * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + evs.length * (maxReq + 8195))
  | [], st0, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | ev :: tl, st0, hAll => by
    obtain ⟨hr0, ha0⟩ := hAll ev (List.mem_cons_self ..)
    obtain ⟨hc1, hl1, hp1⟩ := hM.step_nonFree_aff st0 hr0 ha0
    obtain ⟨hc2, hl2, hp2⟩ :=
      stepEvents_boundedRustEvs_aux hM tl (M.step ev st0)
        (fun e he => hAll e (List.mem_cons_of_mem _ he))
    simp only [AllocCostModel.stepEvents_cons, List.length_cons]
    have hmul1 : (tl.length + 1) * (2 * maxReq + 9539) =
        (2 * maxReq + 9539) + tl.length * (2 * maxReq + 9539) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hmul2 : (tl.length + 1) * (maxReq + 8195) =
        (maxReq + 8195) + tl.length * (maxReq + 8195) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    refine ⟨by omega, by omega, by omega⟩

theorem boundedRustEvs_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxCount maxReq : Nat) :
    PhaseCreditSpec M (BoundedRustEvs maxCount maxReq)
      (maxCount * (2 * maxReq + 9539))
      (maxCount * (maxReq + 8195))
      (maxCount * (maxReq + 8195))
      maxReq where
  req_align := fun _ h ev hev =>
    let ⟨_, hr, ha, hre⟩ := h.2 ev hev
    boundedRustEvs_event_bounds hr ha hre
  credit_le := fun st0 {evs} h => by
    have hAll : ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 :=
      fun ev hev =>
        let ⟨_, hr, ha, hre⟩ := h.2 ev hev
        boundedRustEvs_event_bounds hr ha hre
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedRustEvs_aux hM evs st0 hAll
    have hmc1 : evs.length * (2 * maxReq + 9539) ≤ maxCount * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ h.1
    have hmc2 : evs.length * (maxReq + 8195) ≤ maxCount * (maxReq + 8195) :=
      Nat.mul_le_mul_right _ h.1
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmc1 _),
      Nat.le_trans hl (Nat.add_le_add_left hmc2 _),
      Nat.le_trans hp
        (Nat.max_le.mpr
          ⟨Nat.le_max_left _ _,
           Nat.le_trans (Nat.add_le_add_left hmc2 _) (Nat.le_max_right _ _)⟩)⟩

theorem boxAlloc_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (sz : Nat) :
    PhaseCreditSpec M (BoxAllocEnv sz) (2 * sz + 9539) (sz + 8195) (sz + 8195) sz := by
  have himp : ∀ evs, BoxAllocEnv sz evs → evs = [] ∨ evs = rustAllocEvents sz 8 := by
    intro evs h
    rcases h with ⟨_, hnil⟩ | ⟨_, halloc⟩
    · exact Or.inl hnil
    · exact Or.inr halloc
  have hopt : optLargeCost M sz ≤ sz + 8195 := by
    have h := optLargeCost_le_add hM sz
    split at h <;> omega
  have halloc : PhaseCreditSpec M (· = rustAllocEvents sz 8)
      (2 * sz + 9539) (sz + 8195) (sz + 8195) sz :=
    (SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM (req := sz) (al := 8) (by omega)).mono
      (Nat.le_refl _) hopt hopt (Nat.le_refl _)
  exact (PhaseCreditSpec.or_of_imp himp (PhaseCreditSpec.nil M) halloc).mono
    (by omega) (by omega) (by omega) (by omega)

/-! ## 2. `SessionStructure::clone` & `SessionRecord::serialize` (`0`-prev & `prev1`) -/

theorem sessionClone_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseCreditSpec M (SegCloneEnv G st)
      (segCloneCum G st) (segCloneLarge M G st) (segCloneLarge M G st) (segCloneMaxReq G st) :=
  SessionCloneCredit.PhaseCreditSpec.segClone hM G st

theorem sessionClone_drop_cancel_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hBody : PhaseCreditSpec M Body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G st) Body) (· = dropClonedSessionEvents G st))
      (segCloneCum G st + c_b)
      l_b
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) :=
  SessionCloneCredit.PhaseCreditSpec.segClone_body_drop_cancel hM G st hBody

theorem serialize_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeCancelEnv g r)
      (recordSerializeCum g r) (recordSerializeOutLarge M g r)
      (recordSerializePeak M g r) (recordSerializeMaxReq g r) :=
  SessionSerializeCredit.PhaseCreditSpec.recordSerialize_cancel hM g r

theorem serializePrev1_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1CancelEnv G sess enc)
      (serializePrev1Cum G sess enc) (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc) (serializePrev1MaxReq G sess enc) :=
  SessionSerializeCredit.PhaseCreditSpec.serializePrev1_cancel hM G sess enc

/-! ## 3. CLI `StoreKits` Poll Envelopes & `PhaseCreditSpec M` Bounds -/

/-- Parametric session-load poll envelope (`AddrText → Dir::get → DeserEnv → FreeOnlyEvs`). -/
def CliSessLoadPollEnv (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (dir : DirGhost) (peer : AddrGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliAddrTextEnv peer)
    (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir (addressText peer.val))
      (SeqEnv
        (fun evs' => evs' = [] ∨ ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
        FreeOnlyEvs))
    evs

/-- `0`-prev session-store poll envelope (`AddrText → RecordSerializeCancelEnv → Dir::put`). -/
def CliSessStorePollEnv (dir : DirGhost) (peer : AddrGhost)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliAddrTextEnv peer)
    (SeqEnv (RecordSerializeCancelEnv g r)
      (SeqEnv (CliDirPutEnv dir [] []) FreeOnlyEvs))
    evs

/-- `prev1` session-store poll envelope (`AddrText → SerializePrev1CancelEnv → Dir::put`). -/
def CliSessStorePollPrev1Env (dir : DirGhost) (peer : AddrGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliAddrTextEnv peer)
    (SeqEnv (SerializePrev1CancelEnv G sess enc)
      (SeqEnv (CliDirPutEnv dir [] []) FreeOnlyEvs))
    evs

/-- Generic small-record (`≤ 8192` B) key/identity poll envelope (`Dir::get` + small decode + drops). -/
def CliSmallStorePollEnv (rd : ReadRule) (files : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (CliDecimalEnv 0#32)
    (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
      (SeqEnv (BoundedRustEvs 32 8192)
        (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)))
    evs

def sessLoadPollDeltaCum (fileCap deserCum : Nat) : Nat :=
  max (65536 + 2 * fileCap) 8516362 + deserCum

def sessLoadPollDeltaLive (fileCap deserLive : Nat) : Nat :=
  max (32768 + fileCap) 2122265 + deserLive

def sessLoadPollDeltaPeak (fileCap deserPeak : Nat) : Nat :=
  max (max (33980 + fileCap) 3187903) (max (25113 + fileCap) 2122265 + deserPeak)

def sessLoadPollMaxReq (fileCap deserMaxReq : Nat) : Nat :=
  max (max 2097152 fileCap) deserMaxReq

private theorem addressText_peer_len_le (peer : AddrGhost)
    (hpeer : peer.name.bytes.length ≤ 40) :
    (addressText peer.val).length ≤ 64 := by
  have ha := addressText_length_le peer.val
  have hlen : peer.val.name.length ≤ 40 := hpeer
  omega

private theorem dirGet_rule_phaseCredit_64 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) {maxEntries fc : Nat}
    (hdc64 : DirDomainCaps 64 maxEntries fc dir)
    (hname : name.length ≤ 64)
    (hcap' : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fc) :
    PhaseCreditSpec M (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
      (max (40172 + 2 * fc) 8506439)
      (max (16726 + fc) 2113878)
      (max (25593 + fc) 3179516)
      (max fc 2097152) := by
  have hpc : pathDeltaCum 64 64 = 30633 := by decide
  have hpl : pathDeltaLive 64 64 = 8531 := by decide
  have hpp : pathDeltaPeak 64 64 = 17398 := by decide
  have hpr : pathMaxReq 64 64 = 336 := by decide
  refine (dirGet_rule_phaseCredit hM rd files dir name hdc64 hname hcap').mono
    ?_ ?_ ?_ ?_
  · rw [dirGetRuleDeltaCum, hpc, readFileRuleDeltaCum, allocBytes1DeltaCum, readFileCliIoDeltaCum]
    omega
  · rw [dirGetRuleDeltaLive, hpl, readFileRuleDeltaLive, allocBytes1DeltaLive, readFileCliIoDeltaLive]
    omega
  · rw [dirGetRuleDeltaPeak, hpp, readFileRuleDeltaPeak, allocBytes1DeltaPeak, readFileCliIoDeltaPeak]
    omega
  · rw [dirGetRuleMaxReq, hpr, readFileRuleMaxReq, readFileCliIoMaxReq]
    omega

theorem sessLoadPoll_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M (CliSessLoadPollEnv rd DeserEnv files dir peer)
      (sessLoadPollDeltaCum (max maxVal fileCap) deserCum)
      (sessLoadPollDeltaLive (max maxVal fileCap) deserLive)
      (sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak)
      (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq) := by
  unfold CliSessLoadPollEnv
  set fc := max maxVal fileCap
  have hname : (addressText peer.val).length ≤ 64 := addressText_peer_len_le peer hpeer
  have hcap' : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fc :=
    fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)
  have hdc64 : DirDomainCaps 64 maxEntries fc dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_max_left _ _)
  have h1 : PhaseCreditSpec M (CliAddrTextEnv peer) 9923 8387 8387 192 :=
    (addrText_phaseCredit hM peer hpeer).mono (by decide) (by decide) (by decide) (by decide)
  have h2 := dirGet_rule_phaseCredit_64 hM rd files dir (addressText peer.val) hdc64 hname hcap'
  have h3_ex : PhaseCreditSpec M
      (fun evs' => ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
      deserCum deserLive deserPeak deserMaxReq :=
    { req_align := fun evs ⟨bs, hbs, hd⟩ => (hdeser bs hbs).req_align evs hd
      credit_le := fun st0 {_} ⟨bs, hbs, hd⟩ => (hdeser bs hbs).credit_le st0 hd }
  have h3 : PhaseCreditSpec M
      (fun evs' => evs' = [] ∨ ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
      deserCum deserLive deserPeak deserMaxReq :=
    (PhaseCreditSpec.or (PhaseCreditSpec.nil M) h3_ex).mono
      (by omega) (by omega) (by omega) (by omega)
  have h3f := seq_freeOnly hM.freeNonInc h3
  have h123 := h1.seq (h2.seq h3f)
  unfold sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
  exact h123.mono (by omega) (by omega) (by omega) (by omega)

def sessStorePollDeltaCum (serCum maxEntries : Nat) : Nat :=
  32768 + serCum + 192 * max 4 (2 * maxEntries)

def sessStorePollDeltaLive (serLive maxEntries : Nat) : Nat :=
  32768 + serLive + 96 * max 4 (2 * maxEntries)

def sessStorePollDeltaPeak (serPeak maxEntries : Nat) : Nat :=
  32768 + serPeak + 96 * max 4 (2 * maxEntries)

def sessStorePollMaxReq (serMaxReq maxEntries : Nat) : Nat :=
  max serMaxReq (96 * max 4 (2 * maxEntries))

theorem sessStorePoll_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M (CliSessStorePollEnv dir peer g r)
      (sessStorePollDeltaCum (recordSerializeCum g r) maxEntries)
      (sessStorePollDeltaLive (recordSerializeOutLarge M g r) maxEntries)
      (sessStorePollDeltaPeak (recordSerializePeak M g r) maxEntries)
      (sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries) := by
  unfold CliSessStorePollEnv
  have h1 := addrText_phaseCredit hM peer hpeer
  have h2 := serialize_phaseCredit hM g r
  have h3 := PhaseCreditSpec.seq (dirPut_phaseCredit hM dir [] [] hdc)
    (PhaseCreditSpec.freeOnly hM.freeNonInc)
  have hle_ser : recordSerializeOutLarge M g r ≤ recordSerializePeak M g r := by
    unfold recordSerializeOutLarge recordSerializePeak
    cases g.cur <;> cases r.currentSession <;> simp [SessionSerializeCredit.serializeSomeOutLarge,
      SessionSerializeCredit.serializeSomePeak]
  have h123 := PhaseCreditSpec.seq h1 (PhaseCreditSpec.seq h2 h3)
  unfold sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
  unfold addrTextDeltaCum addrTextDeltaLive addrTextDeltaPeak addrTextMaxReq at h123
  unfold dirPutDeltaCum dirPutDeltaLive dirPutDeltaPeak dirPutMaxReq at h123
  unfold growOneDirDeltaCum growOneDirDeltaLive growOneDirDeltaPeak growOneDirMaxReq at h123
  have hmax2 : max 4 (2 * max 4 (2 * maxEntries)) = 2 * max 4 (2 * maxEntries) := by omega
  rw [hmax2] at h123
  exact PhaseCreditSpec.mono (by omega) (by omega) (by omega) (by omega) h123

theorem cliStorePollPrev1_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir : DirGhost} {peer : AddrGhost}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M (CliSessStorePollPrev1Env dir peer G sess enc)
      (sessStorePollDeltaCum (serializePrev1Cum G sess enc) maxEntries)
      (sessStorePollDeltaLive (serializePrev1OutLarge M G sess enc) maxEntries)
      (sessStorePollDeltaPeak (serializePrev1Peak M G sess enc) maxEntries)
      (sessStorePollMaxReq (serializePrev1MaxReq G sess enc) maxEntries) := by
  unfold CliSessStorePollPrev1Env
  have h1 := addrText_phaseCredit hM peer hpeer
  have h2 := serializePrev1_phaseCredit hM G sess enc
  have h3 := PhaseCreditSpec.seq (dirPut_phaseCredit hM dir [] [] hdc)
    (PhaseCreditSpec.freeOnly hM.freeNonInc)
  have hle_ser : serializePrev1OutLarge M G sess enc ≤ serializePrev1Peak M G sess enc := by
    unfold serializePrev1OutLarge serializePrev1Peak
    omega
  have h123 := PhaseCreditSpec.seq h1 (PhaseCreditSpec.seq h2 h3)
  unfold sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
  unfold addrTextDeltaCum addrTextDeltaLive addrTextDeltaPeak addrTextMaxReq at h123
  unfold dirPutDeltaCum dirPutDeltaLive dirPutDeltaPeak dirPutMaxReq at h123
  unfold growOneDirDeltaCum growOneDirDeltaLive growOneDirDeltaPeak growOneDirMaxReq at h123
  have hmax2 : max 4 (2 * max 4 (2 * maxEntries)) = 2 * max 4 (2 * maxEntries) := by omega
  rw [hmax2] at h123
  exact PhaseCreditSpec.mono (by omega) (by omega) (by omega) (by omega) h123

def smallStorePollDeltaCum (fileCap maxEntries : Nat) : Nat :=
  max (1048576 + 2 * fileCap) 9364784 + 192 * max 4 (2 * maxEntries)

def smallStorePollDeltaLive (fileCap maxEntries : Nat) : Nat :=
  max (589824 + fileCap) 2662943 + 96 * max 4 (2 * maxEntries)

def smallStorePollDeltaPeak (fileCap maxEntries : Nat) : Nat :=
  max 3187743 (max (589824 + fileCap) 2662943 + 96 * max 4 (2 * maxEntries))

def smallStorePollMaxReq (fileCap maxEntries : Nat) : Nat :=
  max (max 2097152 fileCap) (96 * max 4 (2 * maxEntries))

theorem smallStorePoll_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (CliSmallStorePollEnv rd files dir name)
      (smallStorePollDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries)
      (smallStorePollMaxReq (max maxVal fileCap) maxEntries) := by
  unfold CliSmallStorePollEnv
  set fc := max maxVal fileCap
  set m := max 4 (2 * maxEntries) with hm_def
  have hm4 : 4 ≤ m := Nat.le_max_left 4 (2 * maxEntries)
  have hm2 : max 4 (2 * m) = 2 * m := by omega
  have hcap' : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fc :=
    fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)
  have hdc64 : DirDomainCaps 64 maxEntries fc dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_max_left _ _)
  have h1 : PhaseCreditSpec M (CliDecimalEnv 0#32) 9603 8227 8227 32 :=
    (decimal_phaseCredit hM 0#32).mono (by decide) (by decide) (by decide) (by decide)
  have h2 := dirGet_rule_phaseCredit_64 hM rd files dir name hdc64 hname hcap'
  have h3 : PhaseCreditSpec M (BoundedRustEvs 32 8192) 829536 524384 524384 8192 :=
    (boundedRustEvs_phaseCredit hM 32 8192).mono (by decide) (by decide) (by decide) (by decide)
  have h4 : PhaseCreditSpec M (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)
      (19206 + 192 * m) (16454 + 96 * m) (16454 + 96 * m) (96 * m) := by
    refine (seq_freeOnly hM.freeNonInc (dirPutStr_phaseCredit hM dir name [] hdc64 hname)).mono
      ?_ ?_ ?_ ?_
    all_goals
      simp only [dirPutStrDeltaCum, dirPutStrDeltaLive, dirPutStrDeltaPeak, dirPutStrMaxReq,
        dirPutDeltaCum, dirPutDeltaLive, dirPutDeltaPeak, dirPutMaxReq,
        growOneDirDeltaCum, growOneDirDeltaLive, growOneDirDeltaPeak, growOneDirMaxReq,
        allocBytes1DeltaCum, allocBytes1DeltaLive, allocBytes1DeltaPeak, ← hm_def, hm2]
      omega
  have h34 : PhaseCreditSpec M
      (SeqEnv (BoundedRustEvs 32 8192) (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs))
      (848742 + 192 * m) (540838 + 96 * m) (540838 + 96 * m) (max 8192 (96 * m)) :=
    (h3.seq h4).mono (by omega) (by omega) (by omega) (Nat.le_refl _)
  have h234 : PhaseCreditSpec M
      (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
        (SeqEnv (BoundedRustEvs 32 8192) (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)))
      (max (888914 + 2 * fc) 9355181 + 192 * m)
      (max (557564 + fc) 2654716 + 96 * m)
      (max 3179516 (max (557564 + fc) 2654716 + 96 * m))
      (max (max 2097152 fc) (96 * m)) :=
    (h2.seq h34).mono (by omega) (by omega) (by omega) (by omega)
  have h1234 := h1.seq h234
  simp only [smallStorePollDeltaCum, smallStorePollDeltaLive, smallStorePollDeltaPeak,
    smallStorePollMaxReq, ← hm_def]
  exact h1234.mono (by omega) (by omega) (by omega) (by omega)

/-! ## 4. Tight Per-Size-Class `StoreKits` and `Dir` `PhaseCreditSpec` Bounds -/

section TightStorePeakSpec

open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SignalSession.Cli (GrowOneDirGhost)
open LibsignalBinary.Heap (rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents rawVecNewCap)
open LibsignalBinary.Heap.SpecBudget (cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers (
  cliIoCapEvents cliIoCapEventsGo cliIoCap_ge_4096 cliIoCap_pos cliIoReadCaps
  optLargeLive phaseCreditSpec_cliIoReadFile_tight
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  fineCostModel_freeNonInc fineCostModel_modelHyps
)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (
  fineSmallAllocCost_192 fineSmallAllocCost_le_143484
  fineSmallAllocCost_le_1607_of_le_64 fineSmallAllocCost_le_9789_of_le_192
  fineSmallAllocCost_le_9789_of_le_2048 fineSmallAllocCost_le_12410_of_le_8192
  fineSmallReallocCost_le_143484 fineSmallReallocCost_le_9789_of_le_256
  fineSmallReallocCost_le_9085_of_192_768 fineSmallReallocCost_le_16509_of_le_8192
  rustAllocTightCum rustAllocTightCum_fine_le_738 rustAllocTightCum_fine_le_143484
  segCloneTightCum tryCloneSmallDelta tryCloneSmallDelta_fine_le_143484
)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (
  recordSerializeTightCum serializePrev1TightCum
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  stepEvents_rustRealloc_large_large
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (GrowOneDirEnv)

/-- Definitional bridge (`rfl`) between `SessionCloneCredit.optLargeCost` and
`DirPeakHelpers.optLargeLive`. -/
theorem optLargeCost_eq_optLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) :
    optLargeCost M req = optLargeLive M req :=
  rfl

theorem optLargeCost_fine_of_le {req : Nat} (hle : req ≤ 135167) :
    optLargeCost fineCostModel req = 0 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq]
  simp [hle]

theorem optLargeCost_fine_of_gt {req : Nat} (hgt : 135167 < req) :
    optLargeCost fineCostModel req = HasFineReallocCredit.largeCost fineCostModel req := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq]
  have hnot : ¬ (req ≤ 135167) := Nat.not_le.mpr hgt
  simp [hnot]

theorem optLargeCost_fine_mono {a b : Nat} (hab : a ≤ b) :
    optLargeCost fineCostModel a ≤ optLargeCost fineCostModel b := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq]
  split
  · exact Nat.zero_le _
  · rename_i hna
    have hb_gt : ¬ (b ≤ 135167) := fun hble => hna (Nat.le_trans hab hble)
    simp only [hb_gt, ↓reduceIte]
    rw [fineCostModel_largeCost_eq, fineCostModel_largeCost_eq]
    exact Nat.add_le_add_right hab 8195

/-! ### Tight Symbolic Clone & Serialize Wrappers -/

theorem sessionClone_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseCreditSpec M (SegCloneEnv G st)
      (segCloneTightCum M G st) (segCloneLarge M G st)
      (segCloneLarge M G st) (segCloneMaxReq G st) :=
  SessionCloneCredit.PhaseCreditSpec.segClone_tight hM G st

theorem sessionClone_drop_cancel_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {Body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hBody : PhaseCreditSpec M Body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G st) Body) (· = dropClonedSessionEvents G st))
      (segCloneTightCum M G st + c_b)
      l_b
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) :=
  SessionCloneCredit.PhaseCreditSpec.segClone_body_drop_cancel_tight hM G st hBody

theorem serialize_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeCancelEnv g r)
      (recordSerializeTightCum M g r) (recordSerializeOutLarge M g r)
      (recordSerializePeak M g r) (recordSerializeMaxReq g r) :=
  SessionSerializeCredit.PhaseCreditSpec.recordSerialize_cancel_tight hM g r

theorem serializePrev1_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1CancelEnv G sess enc)
      (serializePrev1TightCum M G sess enc) (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc) (serializePrev1MaxReq G sess enc) :=
  SessionSerializeCredit.PhaseCreditSpec.serializePrev1_cancel_tight hM G sess enc

theorem boxAlloc_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (sz : Nat) :
    PhaseCreditSpec M (BoxAllocEnv sz)
      (tryCloneSmallDelta M sz) (optLargeCost M sz) (optLargeCost M sz) sz := by
  have himp : ∀ evs, BoxAllocEnv sz evs →
      evs = if sz = 0 then [] else rustAllocEvents sz 8 := by
    intro evs h
    rcases h with ⟨hz, hnil⟩ | ⟨hpos, halloc⟩
    · simp [hz, hnil]
    · have hnz : sz ≠ 0 := Nat.ne_of_gt hpos
      simp [hnz, halloc]
  unfold tryCloneSmallDelta
  refine (SessionCloneCredit.PhaseCreditSpec.condRustAlloc_tight hM
    (p := sz = 0) (req := sz) (al := 8) (by decide)).congr_mono himp
    (Nat.le_refl _) ?_ ?_ (by split <;> omega)
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  · split
    · exact Nat.zero_le _
    · exact Nat.le_refl _

/-! ### Self-Contained Axiom-Clean Tight `Dir` & `BoundedRustEvs` Leaf Specs on `fineCostModel` -/

/-- Tight per-bucket `cumSmall` ceiling for `allocBytes1Events bs` (`bs.length ≤ fc`) on `fineCostModel`:
`0` (`fc = 0`), `1,607` (`fc ≤ 64`), `9,789` (`fc ≤ 2,048`), `12,410` (`fc ≤ 8,192`), and
`143,484` (`fc > 8,192`, including `2 MiB`). -/
def fineAllocCapCum (fc : Nat) : Nat :=
  if fc = 0 then 0
  else if fc ≤ 64 then 1607
  else if fc ≤ 2048 then 9789
  else if fc ≤ 8192 then 12410
  else 143484

theorem tryCloneSmallDelta_fine_le_allocCapCum {len fc : Nat} (hlen : len ≤ fc) :
    tryCloneSmallDelta fineCostModel len ≤ fineAllocCapCum fc := by
  by_cases hz : len = 0
  · subst hz
    simp [tryCloneSmallDelta]
  · have hfcz : fc ≠ 0 := by omega
    unfold fineAllocCapCum
    simp only [hfcz, ↓reduceIte]
    split
    · rename_i h64
      have hl64 : len ≤ 64 := Nat.le_trans hlen h64
      unfold tryCloneSmallDelta rustAllocTightCum
      have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]
        exact Nat.le_trans hl64 (by decide)
      simp only [hz, hsm, ↓reduceIte]
      exact fineSmallAllocCost_le_1607_of_le_64 hl64
    · split
      · rename_i h2048
        have hl2048 : len ≤ 2048 := Nat.le_trans hlen h2048
        unfold tryCloneSmallDelta rustAllocTightCum
        have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]
          exact Nat.le_trans hl2048 (by decide)
        simp only [hz, hsm, ↓reduceIte]
        exact fineSmallAllocCost_le_9789_of_le_2048 hl2048
      · split
        · rename_i h8192
          have hl8192 : len ≤ 8192 := Nat.le_trans hlen h8192
          unfold tryCloneSmallDelta rustAllocTightCum
          have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
            rw [fineCostModel_smallMaxReq_eq]
            exact Nat.le_trans hl8192 (by decide)
          simp only [hz, hsm, ↓reduceIte]
          exact fineSmallAllocCost_le_12410_of_le_8192 hl8192
        · exact tryCloneSmallDelta_fine_le_143484 len

theorem allocBytes1_fine_phaseCredit_tight {bs : List (BitVec 8)} {fc : Nat}
    (hlen : bs.length ≤ fc) :
    PhaseCreditSpec fineCostModel (· = allocBytes1Events bs)
      (fineAllocCapCum fc)
      (optLargeCost fineCostModel fc)
      (optLargeCost fineCostModel fc)
      fc := by
  unfold allocBytes1Events
  have hcond := SessionCloneCredit.PhaseCreditSpec.condRustAlloc_tight fineCostModel_modelHyps
    (p := bs.length = 0) (req := bs.length) (al := 1) (by decide)
  have hc : (if bs.length = 0 then 0 else rustAllocTightCum fineCostModel bs.length) ≤
      fineAllocCapCum fc :=
    tryCloneSmallDelta_fine_le_allocCapCum hlen
  have hl : (if bs.length = 0 then 0 else optLargeCost fineCostModel bs.length) ≤
      optLargeCost fineCostModel fc := by
    split
    · exact Nat.zero_le _
    · exact optLargeCost_fine_mono hlen
  have hr : (if bs.length = 0 then 0 else bs.length) ≤ fc := by
    split
    · exact Nat.zero_le fc
    · exact hlen
  exact hcond.mono hc hl hl hr

/-- Tight `cumSmall` ceiling for `ReadFileRuleEnv` (`bs.length ≤ fc`) on `fineCostModel`:
`0` (`fc = 0`), `12,410` (`0 < fc ≤ 4,096`), and `573,818` (`fc > 4,096`, covering `cliIoReadCaps 9`
up to `2 MiB`). -/
def fineReadFileCum (fc : Nat) : Nat :=
  if fc = 0 then 0
  else if fc ≤ 4096 then 12410
  else 573818

/-- Tight `liveLarge` ceiling for `ReadFileRuleEnv` (`bs.length ≤ fc`) on `fineCostModel`:
`0` for `fc ≤ 4,096`, else `max (optLargeCost fineCostModel fc) 2,105,347`. -/
def fineReadFileLive (fc : Nat) : Nat :=
  if fc ≤ 4096 then 0
  else max (optLargeCost fineCostModel fc) 2105347

/-- Tight `peakLarge` ceiling for `ReadFileRuleEnv` (`bs.length ≤ fc`) on `fineCostModel`:
`0` for `fc ≤ 4,096`, else `max (optLargeCost fineCostModel fc) 3,162,118`. -/
def fineReadFilePeak (fc : Nat) : Nat :=
  if fc ≤ 4096 then 0
  else max (optLargeCost fineCostModel fc) 3162118

/-- Tight `maxReq` ceiling for `ReadFileRuleEnv` (`bs.length ≤ fc`) on `fineCostModel`:
`0` (`fc = 0`), `4,096` (`0 < fc ≤ 4,096`), else `max fc 2,097,152`. -/
def fineReadFileMaxReq (fc : Nat) : Nat :=
  if fc = 0 then 0
  else if fc ≤ 4096 then 4096
  else max fc 2097152

private theorem fineAllocCapCum_le_readFileCum (fc : Nat) :
    fineAllocCapCum fc ≤ fineReadFileCum fc := by
  unfold fineAllocCapCum fineReadFileCum
  split_ifs <;> omega

private theorem optLargeCost_fine_le_readFileLive (fc : Nat) :
    optLargeCost fineCostModel fc ≤ fineReadFileLive fc := by
  unfold fineReadFileLive
  split_ifs with hle
  · rw [optLargeCost_fine_of_le (Nat.le_trans hle (by decide))]
  · exact Nat.le_max_left _ _

private theorem fineReadFileLive_le_peak (fc : Nat) :
    fineReadFileLive fc ≤ fineReadFilePeak fc := by
  unfold fineReadFileLive fineReadFilePeak
  split_ifs <;> omega

private theorem le_fineReadFileMaxReq (fc : Nat) :
    fc ≤ fineReadFileMaxReq fc := by
  unfold fineReadFileMaxReq
  split_ifs <;> omega

private theorem specCliIoCap_eq_local :
    LibsignalBinary.Heap.SpecBudget.cliIoCap = DirPeakHelpers.cliIoCap :=
  rfl

private theorem specCliIoCapIdx_eq_local : ∀ (K r : Nat),
    LibsignalBinary.Heap.SpecBudget.cliIoCapIdx K r =
      DirPeakHelpers.cliIoCapIdx K r
  | 0, _ => rfl
  | K + 1, r => by
    unfold LibsignalBinary.Heap.SpecBudget.cliIoCapIdx DirPeakHelpers.cliIoCapIdx
    rw [specCliIoCap_eq_local, specCliIoCapIdx_eq_local K r]

private theorem specCliIoCapsEvents_pos_eq_local :
    ∀ {prev : Nat} (cs : List Nat), 0 < prev → (∀ c ∈ cs, 0 < c) →
      cliIoCapsEvents prev cs = cliIoCapEventsGo prev cs
  | prev, [], _, _ => by cases prev <;> rfl
  | prev, c :: cs, hprev, hcs => by
    cases prev with
    | zero => omega
    | succ _ =>
      have hc : 0 < c := hcs c List.mem_cons_self
      have hrest : ∀ x ∈ cs, 0 < x := fun x hx => hcs x (List.mem_cons_of_mem c hx)
      dsimp only [cliIoCapsEvents, cliIoCapEventsGo]
      rw [specCliIoCapsEvents_pos_eq_local cs hc hrest]

private theorem specCliIoReadSchedule_events_eq_local (K r : Nat) :
    cliIoCapsEvents 0 (cliIoReadScheduleCaps K r) =
      cliIoCapEvents (cliIoReadCaps K r) := by
  unfold cliIoReadScheduleCaps cliIoReadCaps
  rw [specCliIoCap_eq_local, specCliIoCapIdx_eq_local K r]
  split_ifs with hr
  · rfl
  · have hpos : ∀ c ∈ (List.range (DirPeakHelpers.cliIoCapIdx K r + 1)).map
        DirPeakHelpers.cliIoCap, 0 < c := by
      intro c hc
      rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
      exact cliIoCap_pos j
    cases hlist : (List.range (DirPeakHelpers.cliIoCapIdx K r + 1)).map
        DirPeakHelpers.cliIoCap with
    | nil => rfl
    | cons c0 cs =>
      rw [hlist] at hpos
      dsimp only [cliIoCapsEvents, cliIoCapEvents]
      rw [specCliIoCapsEvents_pos_eq_local cs (hpos c0 List.mem_cons_self)
        (fun x hx => hpos x (List.mem_cons_of_mem c0 hx))]

private theorem specCliIoCapIdx_eq_zero_of_le_4096 : ∀ (K : Nat) {r : Nat},
    r ≤ 4096 → LibsignalBinary.Heap.SpecBudget.cliIoCapIdx K r = 0
  | 0, _, _ => rfl
  | K + 1, r, hr => by
    unfold LibsignalBinary.Heap.SpecBudget.cliIoCapIdx
    have hle : r ≤ LibsignalBinary.Heap.SpecBudget.cliIoCap K := by
      rw [specCliIoCap_eq_local]
      exact Nat.le_trans hr (cliIoCap_ge_4096 K)
    simp only [hle, ↓reduceIte]
    exact specCliIoCapIdx_eq_zero_of_le_4096 K hr

private theorem cliIoReadSchedule9_events_of_pos_le_4096 {r : Nat}
    (hpos : 0 < r) (hr : r ≤ 4096) :
    cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 r) = rustAllocEvents 4096 1 := by
  have hnz : r ≠ 0 := Nat.ne_of_gt hpos
  unfold cliIoReadScheduleCaps
  simp only [hnz, ↓reduceIte, specCliIoCapIdx_eq_zero_of_le_4096 9 hr]
  rfl

theorem readFile_rule_fine_phaseCredit_tight
    (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8)) {fc : Nat}
    (hcap : ∀ bs, rd files path = .ok bs → bs.length ≤ fc) :
    PhaseCreditSpec fineCostModel (ReadFileRuleEnv rd files path)
      (fineReadFileCum fc)
      (fineReadFileLive fc)
      (fineReadFilePeak fc)
      (fineReadFileMaxReq fc) := by
  unfold ReadFileRuleEnv
  cases hrd : rd files path with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    dsimp only
    have hbs : bs.length ≤ fc := hcap bs hrd
    by_cases hfc0 : fc = 0
    · have hbs0 : bs.length = 0 := by omega
      refine (PhaseCreditSpec.of_eq_nil (M := fineCostModel) ?_).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      intro evs h
      rcases h with h1 | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨hgt, _⟩
      · rw [h1]; unfold allocBytes1Events; simp [hbs0]
      · exact h2
      · rw [h3]; unfold cliIoReadScheduleCaps; simp [hbs0, cliIoCapsEvents]
      · omega
    · by_cases hfc4096 : fc ≤ 4096
      · have h1 : PhaseCreditSpec fineCostModel (fun evs => evs = allocBytes1Events bs)
            12410 0 0 4096 := by
          have ha := allocBytes1_fine_phaseCredit_tight hbs
          have hl0 : optLargeCost fineCostModel fc = 0 :=
            optLargeCost_fine_of_le (Nat.le_trans hfc4096 (by decide))
          rw [hl0] at ha
          have hc : fineAllocCapCum fc ≤ 12410 := by
            unfold fineAllocCapCum; split_ifs <;> omega
          exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) hfc4096
        have h2 : PhaseCreditSpec fineCostModel
            (fun evs => (4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = [])
            12410 0 0 4096 :=
          (PhaseCreditSpec.of_eq_nil (M := fineCostModel) (fun _ h => h.2)).mono
            (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        have h3 : PhaseCreditSpec fineCostModel
            (fun evs => bs.length ≤ 2097152 ∧
              evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))
            12410 0 0 4096 := by
          by_cases hbs0 : bs.length = 0
          · refine (PhaseCreditSpec.of_eq_nil (M := fineCostModel) ?_).mono
              (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
            intro evs h
            rw [h.2]; unfold cliIoReadScheduleCaps; simp [hbs0, cliIoCapsEvents]
          · have hpos : 0 < bs.length := Nat.pos_of_ne_zero hbs0
            have hbs4096 : bs.length ≤ 4096 := Nat.le_trans hbs hfc4096
            have ha4096 := PhaseCreditSpec.rustAlloc_small fineCostModel
              (req := 4096) (al := 1) (by decide) (by decide)
              (by rw [fineCostModel_smallMaxReq_eq]; decide)
            exact ha4096.congr_mono
              (fun evs h => by
                rw [h.2, cliIoReadSchedule9_events_of_pos_le_4096 hpos hbs4096])
              (fineSmallAllocCost_le_12410_of_le_8192 (by decide))
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 4096)
        have h4 : PhaseCreditSpec fineCostModel
            (fun evs => 2097152 < bs.length ∧
              evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++
                rustDeallocEvents 2097152 1)
            12410 0 0 4096 :=
          (PhaseCreditSpec.of_eq_nil (M := fineCostModel)
            (fun _ h => absurd h.1 (by omega))).mono
            (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        refine (h1.or (h2.or (h3.or h4))).mono ?_ ?_ ?_ ?_
        all_goals
          simp only [fineReadFileCum, fineReadFileLive, fineReadFilePeak, fineReadFileMaxReq,
            hfc0, hfc4096, ↓reduceIte]
          omega
      · set L := max (optLargeCost fineCostModel fc) 2105347
        set P := max (optLargeCost fineCostModel fc) 3162118
        set R := max fc 2097152
        have h1 : PhaseCreditSpec fineCostModel (fun evs => evs = allocBytes1Events bs)
            573818 L P R := by
          have hc : fineAllocCapCum fc ≤ 573818 := by
            unfold fineAllocCapCum; split_ifs <;> omega
          exact (allocBytes1_fine_phaseCredit_tight hbs).mono
            hc (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        have h2 : PhaseCreditSpec fineCostModel
            (fun evs => (4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = [])
            573818 L P R :=
          (PhaseCreditSpec.of_eq_nil (M := fineCostModel) (fun _ h => h.2)).mono
            (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        have h3 : PhaseCreditSpec fineCostModel
            (fun evs => bs.length ≤ 2097152 ∧
              evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))
            573818 L P R := by
          have hcio := phaseCreditSpec_cliIoReadFile_tight fineCostModel_modelHyps
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            bs.length
          exact hcio.congr_mono
            (fun evs h => by
              rw [← specCliIoReadSchedule_events_eq_local 9 bs.length]
              exact h.2)
            (Nat.le_refl 573818) (Nat.le_max_right _ _)
            (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        have h4 : PhaseCreditSpec fineCostModel
            (fun evs => 2097152 < bs.length ∧
              evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++
                rustDeallocEvents 2097152 1)
            573818 L P R := by
          have hcio2 := seq_freeOnly fineCostModel_freeNonInc
            (phaseCreditSpec_cliIoReadFile_tight fineCostModel_modelHyps
              (by rw [fineCostModel_smallMaxReq_eq]; decide)
              (by rw [fineCostModel_smallMaxReq_eq]; decide)
              2097152)
          refine hcio2.congr_mono ?_
            (Nat.le_refl 573818) (Nat.le_max_right _ _)
            (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          intro evs h
          refine Or.inr ⟨_, _, h.2, specCliIoReadSchedule_events_eq_local 9 2097152, ?_⟩
          unfold FreeOnlyEvs rustDeallocEvents
          intro ev hev
          rw [List.mem_singleton] at hev
          exact ⟨1, 2097152, hev⟩
        refine (h1.or (h2.or (h3.or h4))).mono ?_ ?_ ?_ ?_
        all_goals
          simp only [fineReadFileCum, fineReadFileLive, fineReadFilePeak, fineReadFileMaxReq,
            hfc0, hfc4096, ↓reduceIte]
          omega

theorem decimal_fine_phaseCredit_tight (n : BitVec 32) :
    PhaseCreditSpec fineCostModel (CliDecimalEnv n) 738 0 0 32 := by
  have hbr2 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ cap : Nat, (decimalText n.toNat).length ≤ cap ∧ cap ≤ 32 ∧
        SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs)
      738 0 0 32 := by
    have hcapSpec : ∀ cap : Nat, cap ≤ 32 →
        PhaseCreditSpec fineCostModel (SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs)
          738 0 0 32 := by
      intro cap hcap
      have ha := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
        (req := cap) (al := 1) (by decide)
      have hc : rustAllocTightCum fineCostModel cap ≤ 738 :=
        rustAllocTightCum_fine_le_738 (Nat.le_trans hcap (by decide))
      have hl : optLargeCost fineCostModel cap = 0 :=
        optLargeCost_fine_of_le (Nat.le_trans hcap (by decide))
      rw [hl] at ha
      exact (seq_freeOnly fineCostModel_freeNonInc ha).mono hc (Nat.le_refl 0) (Nat.le_refl 0) hcap
    exact
      { req_align := fun evs ⟨cap, _, hcap, hs⟩ => (hcapSpec cap hcap).req_align evs hs
        credit_le := fun st0 {_} ⟨cap, _, hcap, hs⟩ => (hcapSpec cap hcap).credit_le st0 hs }
  unfold CliDecimalEnv
  exact ((PhaseCreditSpec.nil fineCostModel).or hbr2).mono
    (by decide) (by decide) (by decide) (by decide)

theorem addrText_fine_phaseCredit_tight (g : AddrGhost)
    (hpeer : g.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (CliAddrTextEnv g) 9789 0 0 192 := by
  have hcapSpec : ∀ cap : Nat, cap ≤ 4 * g.name.bytes.length + 32 →
      PhaseCreditSpec fineCostModel (SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs)
        9789 0 0 192 := by
    intro cap hcap
    have h192 : cap ≤ 192 := by omega
    have ha := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
      (req := cap) (al := 1) (by decide)
    have hc : rustAllocTightCum fineCostModel cap ≤ 9789 := by
      unfold rustAllocTightCum
      have hsm : cap ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]
        exact Nat.le_trans h192 (by decide)
      simp only [hsm, ↓reduceIte]
      exact fineSmallAllocCost_le_9789_of_le_192 h192
    have hl : optLargeCost fineCostModel cap = 0 :=
      optLargeCost_fine_of_le (Nat.le_trans h192 (by decide))
    rw [hl] at ha
    exact (seq_freeOnly fineCostModel_freeNonInc ha).mono hc (Nat.le_refl 0) (Nat.le_refl 0) h192
  exact
    { req_align := fun evs ⟨cap, hcap, hs⟩ => (hcapSpec cap hcap).req_align evs hs
      credit_le := fun st0 {_} ⟨cap, hcap, hs⟩ => (hcapSpec cap hcap).credit_le st0 hs }

theorem path_fine_phaseCredit_tight {dir name : List (BitVec 8)}
    (hdir : dir.length ≤ 64) (hname : name.length ≤ 64) :
    PhaseCreditSpec fineCostModel (CliPathEnv dir name) 21185 0 0 256 := by
  unfold CliPathEnv
  split
  · have hab := allocBytes1_fine_phaseCredit_tight hname
    have hl0 : optLargeCost fineCostModel 64 = 0 := optLargeCost_fine_of_le (by decide)
    rw [hl0] at hab
    exact hab.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  · rename_i hne
    have hpos0 : 0 < dir.length := List.length_pos_of_ne_nil hne
    set cap0 := dir.length
    set cap1 := reserveCap cap0 cap0 1 with hcap1_def
    set need2 := decide (cap1 - (cap0 + 1) < name.length)
    set capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1 with hcf_def
    have hc1_bounds : 8 ≤ cap1 ∧ cap1 ≤ 128 := by
      rw [hcap1_def]; unfold reserveCap; omega
    have hcf_bounds : 8 ≤ capFinal ∧ capFinal ≤ 256 := by
      rw [hcf_def]
      split
      · unfold reserveCap; omega
      · omega
    have s0 : PhaseCreditSpec fineCostModel (· = rustAllocEvents cap0 1) 1607 0 0 64 :=
      (PhaseCreditSpec.rustAlloc_small fineCostModel (by decide) hpos0
        (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
        (fineSmallAllocCost_le_1607_of_le_64 hdir) (Nat.le_refl 0) (Nat.le_refl 0) hdir
    have s1 : PhaseCreditSpec fineCostModel (· = rustReallocEvents cap0 cap1 1) 9789 0 0 128 :=
      (PhaseCreditSpec.rustRealloc_small_small fineCostModel
        (by decide) (by omega) hpos0 (by rw [fineCostModel_smallMaxReq_eq]; omega)
        (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
        (fineSmallReallocCost_le_9789_of_le_256 (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) hc1_bounds.2
    have s2 : PhaseCreditSpec fineCostModel
        (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = []))
        9789 0 0 256 := by
      split
      · exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (by decide) (by omega) (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)
          (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
          (fineSmallReallocCost_le_9789_of_le_256 hcf_bounds.2)
          (Nat.le_refl 0) (Nat.le_refl 0) hcf_bounds.2
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    exact ((s0.concat s1).concat s2).mono (by decide) (by decide) (by decide) (by decide)

theorem dirGet_rule_fine_phaseCredit_tight
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
      (21185 + fineReadFileCum (max maxVal fileCap))
      (fineReadFileLive (max maxVal fileCap))
      (fineReadFilePeak (max maxVal fileCap))
      (max 256 (fineReadFileMaxReq (max maxVal fileCap))) := by
  set fc := max maxVal fileCap
  have hhit : PhaseCreditSpec fineCostModel
      (fun evs => ∃ k v, (k, v) ∈ dir.changed ∧ k = name ∧ evs = allocBytes1Events v)
      (21185 + fineReadFileCum fc)
      (fineReadFileLive fc)
      (fineReadFilePeak fc)
      (max 256 (fineReadFileMaxReq fc)) := by
    have hvSpec : ∀ v : List (BitVec 8), v.length ≤ fc →
        PhaseCreditSpec fineCostModel (· = allocBytes1Events v)
          (21185 + fineReadFileCum fc)
          (fineReadFileLive fc)
          (fineReadFilePeak fc)
          (max 256 (fineReadFileMaxReq fc)) := fun v hv =>
      (allocBytes1_fine_phaseCredit_tight hv).mono
        (Nat.le_trans (fineAllocCapCum_le_readFileCum fc) (Nat.le_add_left _ 21185))
        (optLargeCost_fine_le_readFileLive fc)
        (Nat.le_trans (optLargeCost_fine_le_readFileLive fc) (fineReadFileLive_le_peak fc))
        (Nat.le_trans (le_fineReadFileMaxReq fc) (Nat.le_max_right 256 _))
    exact
      { req_align := fun evs ⟨k, v, hm, _, heq⟩ =>
          (hvSpec v (Nat.le_trans (hdc.changed_val_le k v hm) (Nat.le_max_left _ _))).req_align evs heq
        credit_le := fun st0 {_} ⟨k, v, hm, _, heq⟩ =>
          (hvSpec v (Nat.le_trans (hdc.changed_val_le k v hm) (Nat.le_max_left _ _))).credit_le st0 heq }
  have hp := path_fine_phaseCredit_tight hdc.path_len_le hname
  have hr := seq_freeOnly fineCostModel_freeNonInc
    (readFile_rule_fine_phaseCredit_tight rd files (pathOf dir.path name)
      (fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)))
  have hmiss : PhaseCreditSpec fineCostModel
      (SeqEnv (CliPathEnv dir.path name)
        (SeqEnv (ReadFileRuleEnv rd files (pathOf dir.path name)) FreeOnlyEvs))
      (21185 + fineReadFileCum fc)
      (fineReadFileLive fc)
      (fineReadFilePeak fc)
      (max 256 (fineReadFileMaxReq fc)) :=
    (hp.seq hr).mono
      (Nat.le_refl _)
      (Nat.le_of_eq (Nat.zero_add _))
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
      (Nat.le_refl _)
  unfold CliDirGetEnv
  exact (hhit.or hmiss).mono
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))

private theorem rustRealloc_large_large_any (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_gt : HasFineReallocCredit.smallMaxReq M < old)
    (hnew_gt : HasFineReallocCredit.smallMaxReq M < new) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (HasFineReallocCredit.largeMetaCost M)
      (HasFineReallocCredit.largeCost M new)
      (HasFineReallocCredit.largeCost M new)
      new where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte] at hev
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_rustRealloc_large_large M st0 hal hal_new hold_gt hnew_gt
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le _ _), hp⟩

/-- Tight `cumSmall` bound for `GrowOneDirEnv x` (`x.cap.toNat ≤ maxCap`) on `fineCostModel`:
`9,085` when `maxCap ≤ 8` (`new ≤ 768`, covering `maxEntries ≤ 4`), else `143,484`. -/
def fineGrowOneDirCum (maxCap : Nat) : Nat :=
  if maxCap ≤ 8 then 9085 else 143484

theorem growOneDir_fine_phaseCredit_tight {x : GrowOneDirGhost} {maxCap : Nat}
    (hcap : x.cap.toNat ≤ maxCap) :
    PhaseCreditSpec fineCostModel (GrowOneDirEnv x)
      (fineGrowOneDirCum maxCap)
      (optLargeCost fineCostModel (48 * max 4 (2 * maxCap)))
      (optLargeCost fineCostModel (48 * max 4 (2 * maxCap)))
      (48 * max 4 (2 * maxCap)) := by
  unfold GrowOneDirEnv rawVecGrowEvents rawVecNewCap
  have htop192 : 192 ≤ 48 * max 4 (2 * maxCap) :=
    Nat.le_trans (by decide : 192 ≤ 48 * 4) (Nat.mul_le_mul_left 48 (Nat.le_max_left 4 _))
  split
  · have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
      (req := 4 * 48) (al := 8) (by decide) (by decide)
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel (4 * 48) ≤
        fineGrowOneDirCum maxCap := by
      rw [show 4 * 48 = 192 by decide, fineSmallAllocCost_192]
      unfold fineGrowOneDirCum
      split <;> decide
    exact ha.mono hc (Nat.zero_le _) (Nat.zero_le _) htop192
  · rename_i hnz
    have hpos_cap : 0 < x.cap.toNat :=
      Nat.pos_of_ne_zero (fun hz => hnz (BitVec.eq_of_toNat_eq hz))
    set old := x.cap.toNat * 48
    set new := max (2 * x.cap.toNat) 4 * 48
    have hold_pos : 0 < old := Nat.mul_pos hpos_cap (by decide)
    have hnew_ge : 192 ≤ new :=
      Nat.le_trans (by decide : 192 ≤ 4 * 48) (Nat.mul_le_mul_right 48 (Nat.le_max_right _ 4))
    have hal_new : 8 ≤ new := Nat.le_trans (by decide : 8 ≤ 192) hnew_ge
    have hold_le_new : old ≤ new :=
      Nat.mul_le_mul_right 48 (Nat.le_trans (by omega : x.cap.toNat ≤ 2 * x.cap.toNat) (Nat.le_max_left _ 4))
    have hnew_le_top : new ≤ 48 * max 4 (2 * maxCap) := by
      have hm : max (2 * x.cap.toNat) 4 ≤ max 4 (2 * maxCap) := by omega
      dsimp only [new]
      rw [Nat.mul_comm (max (2 * x.cap.toNat) 4) 48]
      exact Nat.mul_le_mul_left 48 hm
    by_cases hold_sm : old ≤ 135167
    · by_cases hnew_sm : new ≤ 135167
      · have hs := PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (by decide) hal_new hold_pos
          (by rwa [fineCostModel_smallMaxReq_eq])
          (Nat.lt_of_lt_of_le (by decide : 0 < 192) hnew_ge)
          (by rwa [fineCostModel_smallMaxReq_eq])
        have hc : HasFineReallocCredit.smallReallocCost fineCostModel new ≤
            fineGrowOneDirCum maxCap := by
          unfold fineGrowOneDirCum
          split
          · rename_i hmc8
            have h768 : new ≤ 768 :=
              Nat.le_trans hnew_le_top
                (Nat.le_trans (Nat.mul_le_mul_left 48 (by omega : max 4 (2 * maxCap) ≤ 16)) (by decide))
            exact fineSmallReallocCost_le_9085_of_192_768 hnew_ge h768
          · exact fineSmallReallocCost_le_143484 (by rwa [fineCostModel_smallMaxReq_eq])
        exact hs.mono hc (Nat.zero_le _) (Nat.zero_le _) hnew_le_top
      · have hnew_gt : 135167 < new := Nat.lt_of_not_ge hnew_sm
        have hmc_gt : ¬ (maxCap ≤ 8) := by
          intro hmc8
          have h768 : new ≤ 768 :=
            Nat.le_trans hnew_le_top
              (Nat.le_trans (Nat.mul_le_mul_left 48 (by omega : max 4 (2 * maxCap) ≤ 16)) (by decide))
          exact hnew_sm (Nat.le_trans h768 (by decide))
        have hsl := PhaseCreditSpec.rustRealloc_small_large fineCostModel
          (by decide) hal_new hold_pos
          (by rwa [fineCostModel_smallMaxReq_eq])
          (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)
        have hc : HasFineReallocCredit.largeMetaCost fineCostModel ≤ fineGrowOneDirCum maxCap := by
          rw [fineCostModel_largeMetaCost_eq]
          unfold fineGrowOneDirCum
          simp only [hmc_gt, ↓reduceIte]
          decide
        have hl : HasFineReallocCredit.largeCost fineCostModel new ≤
            optLargeCost fineCostModel (48 * max 4 (2 * maxCap)) := by
          rw [← optLargeCost_fine_of_gt hnew_gt]
          exact optLargeCost_fine_mono hnew_le_top
        exact hsl.mono hc hl hl hnew_le_top
    · have hold_gt : 135167 < old := Nat.lt_of_not_ge hold_sm
      have hnew_gt : 135167 < new := Nat.lt_of_lt_of_le hold_gt hold_le_new
      have hmc_gt : ¬ (maxCap ≤ 8) := by
        intro hmc8
        have h768 : new ≤ 768 :=
          Nat.le_trans hnew_le_top
            (Nat.le_trans (Nat.mul_le_mul_left 48 (by omega : max 4 (2 * maxCap) ≤ 16)) (by decide))
        exact absurd (Nat.lt_of_lt_of_le hnew_gt h768) (by decide)
      have hll := rustRealloc_large_large_any fineCostModel
        (by decide) hal_new
        (by rw [fineCostModel_smallMaxReq_eq]; exact hold_gt)
        (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)
      have hc : HasFineReallocCredit.largeMetaCost fineCostModel ≤ fineGrowOneDirCum maxCap := by
        rw [fineCostModel_largeMetaCost_eq]
        unfold fineGrowOneDirCum
        simp only [hmc_gt, ↓reduceIte]
        decide
      have hl : HasFineReallocCredit.largeCost fineCostModel new ≤
          optLargeCost fineCostModel (48 * max 4 (2 * maxCap)) := by
        rw [← optLargeCost_fine_of_gt hnew_gt]
        exact optLargeCost_fine_mono hnew_le_top
      exact hll.mono hc hl hl hnew_le_top

def fineDirPutCum (maxEntries : Nat) : Nat :=
  fineGrowOneDirCum (max 4 (2 * maxEntries))

def fineDirPutLive (maxEntries : Nat) : Nat :=
  optLargeCost fineCostModel (96 * max 4 (2 * maxEntries))

theorem dirPut_fine_phaseCredit_tight
    (dir : DirGhost) (name bytes : List (BitVec 8))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) :
    PhaseCreditSpec fineCostModel (CliDirPutEnv dir name bytes)
      (fineDirPutCum maxEntries)
      (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries)
      (96 * max 4 (2 * maxEntries)) := by
  have hm_eq : 48 * max 4 (2 * max 4 (2 * maxEntries)) = 96 * max 4 (2 * maxEntries) := by
    have hmax : max 4 (2 * max 4 (2 * maxEntries)) = 2 * max 4 (2 * maxEntries) := by omega
    rw [hmax, ← Nat.mul_assoc]
  have hfr : PhaseCreditSpec fineCostModel FreeOnlyEvs
      (fineDirPutCum maxEntries) (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries) (96 * max 4 (2 * maxEntries)) :=
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have hgr : PhaseCreditSpec fineCostModel
      (fun evs => ∃ x : GrowOneDirGhost,
        x.cap.toNat ≤ max 4 (2 * dir.changed.length) ∧ GrowOneDirEnv x evs)
      (fineDirPutCum maxEntries) (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries) (96 * max 4 (2 * maxEntries)) := by
    have hxSpec : ∀ x : GrowOneDirGhost, x.cap.toNat ≤ max 4 (2 * dir.changed.length) →
        PhaseCreditSpec fineCostModel (GrowOneDirEnv x)
          (fineDirPutCum maxEntries) (fineDirPutLive maxEntries)
          (fineDirPutLive maxEntries) (96 * max 4 (2 * maxEntries)) := by
      intro x hx
      have hcap' : x.cap.toNat ≤ max 4 (2 * maxEntries) :=
        Nat.le_trans hx
          (Nat.max_le.mpr
            ⟨Nat.le_max_left 4 _,
             Nat.le_trans (Nat.mul_le_mul_left 2 hdc.changed_len_le) (Nat.le_max_right 4 _)⟩)
      have hg := growOneDir_fine_phaseCredit_tight hcap'
      unfold fineDirPutCum fineDirPutLive
      rw [← hm_eq]
      exact hg
    exact
      { req_align := fun evs ⟨x, hx, hg⟩ => (hxSpec x hx).req_align evs hg
        credit_le := fun st0 {_} ⟨x, hx, hg⟩ => (hxSpec x hx).credit_le st0 hg }
  unfold CliDirPutEnv
  exact (hfr.or hgr).mono
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))
    (Nat.le_of_eq (Nat.max_self _))

theorem dirPutStr_fine_phaseCredit_tight
    (dir : DirGhost) (name bytes : List (BitVec 8))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hname : name.length ≤ 64) :
    PhaseCreditSpec fineCostModel (CliDirPutStrEnv dir name bytes)
      (1607 + fineDirPutCum maxEntries)
      (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries)
      (96 * max 4 (2 * maxEntries)) := by
  unfold CliDirPutStrEnv
  have h1 := allocBytes1_fine_phaseCredit_tight hname
  have hl0 : optLargeCost fineCostModel 64 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hl0] at h1
  have h2 := dirPut_fine_phaseCredit_tight dir name bytes hdc
  have hr64 : 64 ≤ 96 * max 4 (2 * maxEntries) :=
    Nat.le_trans (by decide : 64 ≤ 96 * 4) (Nat.mul_le_mul_left 96 (Nat.le_max_left 4 _))
  exact (h1.seq h2).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
    (Nat.max_le.mpr ⟨hr64, Nat.le_refl _⟩)

private theorem step_bounded8192_fine {ev : AllocEvent} {maxReq : Nat}
    (hmax : maxReq ≤ 8192) (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16)
    (st : fineCostModel.σ) :
    HasFineReallocCredit.cumSmall (fineCostModel.step ev st) ≤
      HasFineReallocCredit.cumSmall st + 16509 ∧
    HasFineReallocCredit.liveLarge (fineCostModel.step ev st) ≤
      HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge (fineCostModel.step ev st) ≤
      HasFineReallocCredit.peakLarge st := by
  have h8 : eventStepReq ev ≤ 8192 := Nat.le_trans hreq hmax
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := fineCostModel_freeNonInc al sz st
    exact ⟨Nat.le_trans hc (Nat.le_add_right _ 16509), hl, hp⟩
  | alloc req =>
    simp only [eventStepReq] at h8
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans h8 (by decide)
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st hsm
    have hsa : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 16509 :=
      Nat.le_trans (fineSmallAllocCost_le_12410_of_le_8192 h8) (by decide)
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsa _), hl, hp⟩
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at h8 hal
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans h8 (by decide)
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st hal hsm
    have hsa : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 16509 :=
      Nat.le_trans (fineSmallAllocCost_le_12410_of_le_8192 h8) (by decide)
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsa _), hl, hp⟩
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at h8 hal
    have hsm : new ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans h8 (by decide)
    have hsr : HasFineReallocCredit.smallReallocCost fineCostModel new ≤ 16509 :=
      fineSmallReallocCost_le_16509_of_le_8192 h8
    by_cases hold : old ≤ HasFineReallocCredit.smallMaxReq fineCostModel
    · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_realloc_small_small_any st hal hold hsm
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsr _), hl, hp⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq fineCostModel < old := Nat.lt_of_not_ge hold
      obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_realloc_large_small_any st hal hold_gt hsm
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left hsr _),
        Nat.le_trans hl (Nat.sub_le _ _), hp⟩

private theorem stepEvents_bounded8192_fine {maxReq : Nat} (hmax : maxReq ≤ 8192) :
    ∀ (evs : List AllocEvent) (st0 : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (fineCostModel.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + evs.length * 16509 ∧
      HasFineReallocCredit.liveLarge (fineCostModel.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (fineCostModel.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0
  | [], st0, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: tl, st0, hAll => by
    obtain ⟨hr0, ha0⟩ := hAll ev List.mem_cons_self
    obtain ⟨hc1, hl1, hp1⟩ := step_bounded8192_fine hmax hr0 ha0 st0
    obtain ⟨hc2, hl2, hp2⟩ :=
      stepEvents_bounded8192_fine hmax tl (fineCostModel.step ev st0)
        (fun e he => hAll e (List.mem_cons_of_mem _ he))
    simp only [AllocCostModel.stepEvents_cons, List.length_cons]
    have hmul : (tl.length + 1) * 16509 = 16509 + tl.length * 16509 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    refine ⟨?_, Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
    rw [hmul, ← Nat.add_assoc]
    exact Nat.le_trans hc2 (Nat.add_le_add_right hc1 _)

/-- Tight `BoundedRustEvs maxCount maxReq` (`maxReq ≤ 8,192`) spec on `fineCostModel`:
`Δcum = maxCount * 16,509`, **`Δlive = 0`**, **`Δpeak = 0`**, `maxReq`. -/
theorem boundedRustEvs_fine_phaseCredit_tight {maxCount maxReq : Nat}
    (hmax : maxReq ≤ 8192) :
    PhaseCreditSpec fineCostModel (BoundedRustEvs maxCount maxReq)
      (maxCount * 16509) 0 0 maxReq where
  req_align := fun _ h ev hev =>
    let ⟨_, hr, ha, hre⟩ := h.2 ev hev
    boundedRustEvs_event_bounds hr ha hre
  credit_le := fun st0 {evs} h => by
    have hAll : ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 :=
      fun ev hev =>
        let ⟨_, hr, ha, hre⟩ := h.2 ev hev
        boundedRustEvs_event_bounds hr ha hre
    obtain ⟨hc, hl, hp⟩ := stepEvents_bounded8192_fine hmax evs st0 hAll
    have hmc : evs.length * 16509 ≤ maxCount * 16509 := Nat.mul_le_mul_right 16509 h.1
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmc _),
      by simpa using hl,
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-! ### Tight CLI `StoreKits` Poll `PhaseCreditSpec` Bounds -/

/-- Tight `CliSessLoadPollEnv` `Δcum`: `9,789` (`AddrText`) `+ 21,185` (`Path`) `+ fineReadFileCum fc + deserCum`
(`= 604,792 + deserCum` at `fc = 2 MiB`, yielding `3,886,069` B = `3.89M` with `deserCum = 3,281,277`,
and `Δpeak = max 3,162,118 (2,105,347 + deserPeak) = 3,162,118` B = `3.16M` at `deserPeak = 815,826`). -/
def sessLoadPollTightDeltaCum (fileCap deserCum : Nat) : Nat :=
  30974 + fineReadFileCum fileCap + deserCum

def sessLoadPollTightDeltaLive (fileCap deserLive : Nat) : Nat :=
  fineReadFileLive fileCap + deserLive

def sessLoadPollTightDeltaPeak (fileCap deserPeak : Nat) : Nat :=
  max (fineReadFilePeak fileCap) (fineReadFileLive fileCap + deserPeak)

def sessLoadPollTightMaxReq (fileCap deserMaxReq : Nat) : Nat :=
  max (max 256 (fineReadFileMaxReq fileCap)) deserMaxReq

theorem sessLoadPoll_phaseCredit_tight
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (CliSessLoadPollEnv rd DeserEnv files dir peer)
      (sessLoadPollTightDeltaCum (max maxVal fileCap) deserCum)
      (sessLoadPollTightDeltaLive (max maxVal fileCap) deserLive)
      (sessLoadPollTightDeltaPeak (max maxVal fileCap) deserPeak)
      (sessLoadPollTightMaxReq (max maxVal fileCap) deserMaxReq) := by
  unfold CliSessLoadPollEnv
  set fc := max maxVal fileCap
  have hname : (addressText peer.val).length ≤ 64 := addressText_peer_len_le peer hpeer
  have hcap' : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fc :=
    fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)
  have hdc64 : DirDomainCaps 64 maxEntries fc dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_max_left _ _)
  have h1 := addrText_fine_phaseCredit_tight peer hpeer
  have h2 := dirGet_rule_fine_phaseCredit_tight rd files dir (addressText peer.val) hdc64 hname hcap'
  rw [Nat.max_self fc] at h2
  have h3_ex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
      deserCum deserLive deserPeak deserMaxReq :=
    { req_align := fun evs ⟨bs, hbs, hd⟩ => (hdeser bs hbs).req_align evs hd
      credit_le := fun st0 {_} ⟨bs, hbs, hd⟩ => (hdeser bs hbs).credit_le st0 hd }
  have h3 : PhaseCreditSpec fineCostModel
      (fun evs' => evs' = [] ∨ ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
      deserCum deserLive deserPeak deserMaxReq :=
    ((PhaseCreditSpec.nil fineCostModel).or h3_ex).mono
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have h3f := seq_freeOnly fineCostModel_freeNonInc h3
  have h23 := h2.seq h3f
  have h123 := h1.seq h23
  unfold sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive
    sessLoadPollTightDeltaPeak sessLoadPollTightMaxReq
  refine h123.mono ?_ (Nat.le_of_eq (Nat.zero_add _)) ?_ ?_
  · rw [← Nat.add_assoc 9789 (21185 + fineReadFileCum fc) deserCum,
        ← Nat.add_assoc 9789 21185 (fineReadFileCum fc),
        show 9789 + 21185 = 30974 by decide]
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩
  · have h192 : 192 ≤ max (max 256 (fineReadFileMaxReq fc)) deserMaxReq :=
      Nat.le_trans (by decide : 192 ≤ 256)
        (Nat.le_trans (Nat.le_max_left 256 _) (Nat.le_max_left _ _))
    exact Nat.max_le.mpr ⟨h192, Nat.le_refl _⟩

/-- Tight `CliSessStorePollEnv` / `CliSessStorePollPrev1Env` `Δcum`:
`9,789` (`AddrText`) `+ serCum + fineDirPutCum maxEntries` (`= 18,874 + serCum` when `maxEntries ≤ 4`). -/
def sessStorePollTightDeltaCum (serCum maxEntries : Nat) : Nat :=
  9789 + serCum + fineDirPutCum maxEntries

def sessStorePollTightDeltaLive (serLive maxEntries : Nat) : Nat :=
  serLive + fineDirPutLive maxEntries

def sessStorePollTightDeltaPeak (serPeak maxEntries : Nat) : Nat :=
  serPeak + fineDirPutLive maxEntries

theorem sessStorePoll_phaseCredit_tight
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (CliSessStorePollEnv dir peer g r)
      (sessStorePollTightDeltaCum (recordSerializeTightCum fineCostModel g r) maxEntries)
      (sessStorePollTightDeltaLive (recordSerializeOutLarge fineCostModel g r) maxEntries)
      (sessStorePollTightDeltaPeak (recordSerializePeak fineCostModel g r) maxEntries)
      (sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries) := by
  unfold CliSessStorePollEnv
  have h1 := addrText_fine_phaseCredit_tight peer hpeer
  have h2 := serialize_phaseCredit_tight fineCostModel_modelHyps g r
  have h3 := seq_freeOnly fineCostModel_freeNonInc
    (dirPut_fine_phaseCredit_tight dir [] [] hdc)
  have hle_ser : recordSerializeOutLarge fineCostModel g r ≤
      recordSerializePeak fineCostModel g r := by
    unfold recordSerializeOutLarge recordSerializePeak
    cases g.cur <;> cases r.currentSession <;>
      simp [SessionSerializeCredit.serializeSomeOutLarge, SessionSerializeCredit.serializeSomePeak]
  have h23 : PhaseCreditSpec fineCostModel
      (SeqEnv (RecordSerializeCancelEnv g r) (SeqEnv (CliDirPutEnv dir [] []) FreeOnlyEvs))
      (recordSerializeTightCum fineCostModel g r + fineDirPutCum maxEntries)
      (recordSerializeOutLarge fineCostModel g r + fineDirPutLive maxEntries)
      (recordSerializePeak fineCostModel g r + fineDirPutLive maxEntries)
      (sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries) :=
    (h2.seq h3).mono
      (Nat.le_refl _)
      (Nat.le_refl _)
      (Nat.max_le.mpr
        ⟨Nat.le_add_right _ _,
         Nat.add_le_add_right hle_ser _⟩)
      (Nat.le_refl _)
  have h123 := h1.seq h23
  unfold sessStorePollTightDeltaCum sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
  refine h123.mono
    (Nat.le_of_eq (Nat.add_assoc 9789 _ _).symm)
    (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
    ?_
  unfold sessStorePollMaxReq
  have h192 : 192 ≤ max (recordSerializeMaxReq g r) (96 * max 4 (2 * maxEntries)) :=
    Nat.le_trans (by decide : 192 ≤ 96 * 4)
      (Nat.le_trans (Nat.mul_le_mul_left 96 (Nat.le_max_left 4 _)) (Nat.le_max_right _ _))
  exact Nat.max_le.mpr ⟨h192, Nat.le_refl _⟩

theorem cliStorePollPrev1_phaseCredit_tight
    {dir : DirGhost} {peer : AddrGhost}
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (CliSessStorePollPrev1Env dir peer G sess enc)
      (sessStorePollTightDeltaCum (serializePrev1TightCum fineCostModel G sess enc) maxEntries)
      (sessStorePollTightDeltaLive (serializePrev1OutLarge fineCostModel G sess enc) maxEntries)
      (sessStorePollTightDeltaPeak (serializePrev1Peak fineCostModel G sess enc) maxEntries)
      (sessStorePollMaxReq (serializePrev1MaxReq G sess enc) maxEntries) := by
  unfold CliSessStorePollPrev1Env
  have h1 := addrText_fine_phaseCredit_tight peer hpeer
  have h2 := serializePrev1_phaseCredit_tight fineCostModel_modelHyps G sess enc
  have h3 := seq_freeOnly fineCostModel_freeNonInc
    (dirPut_fine_phaseCredit_tight dir [] [] hdc)
  have hle_ser : serializePrev1OutLarge fineCostModel G sess enc ≤
      serializePrev1Peak fineCostModel G sess enc := by
    unfold serializePrev1OutLarge serializePrev1Peak
    exact Nat.le_add_left _ _
  have h23 : PhaseCreditSpec fineCostModel
      (SeqEnv (SerializePrev1CancelEnv G sess enc) (SeqEnv (CliDirPutEnv dir [] []) FreeOnlyEvs))
      (serializePrev1TightCum fineCostModel G sess enc + fineDirPutCum maxEntries)
      (serializePrev1OutLarge fineCostModel G sess enc + fineDirPutLive maxEntries)
      (serializePrev1Peak fineCostModel G sess enc + fineDirPutLive maxEntries)
      (sessStorePollMaxReq (serializePrev1MaxReq G sess enc) maxEntries) :=
    (h2.seq h3).mono
      (Nat.le_refl _)
      (Nat.le_refl _)
      (Nat.max_le.mpr
        ⟨Nat.le_add_right _ _,
         Nat.add_le_add_right hle_ser _⟩)
      (Nat.le_refl _)
  have h123 := h1.seq h23
  unfold sessStorePollTightDeltaCum sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
  refine h123.mono
    (Nat.le_of_eq (Nat.add_assoc 9789 _ _).symm)
    (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
    ?_
  unfold sessStorePollMaxReq
  have h192 : 192 ≤ max (serializePrev1MaxReq G sess enc) (96 * max 4 (2 * maxEntries)) :=
    Nat.le_trans (by decide : 192 ≤ 96 * 4)
      (Nat.le_trans (Nat.mul_le_mul_left 96 (Nat.le_max_left 4 _)) (Nat.le_max_right _ _))
  exact Nat.max_le.mpr ⟨h192, Nat.le_refl _⟩

/-- Tight `CliSmallStorePollEnv` `Δcum` on `fineCostModel`:
`738` (`Decimal`) `+ 21,185` (`Path`) `+ fineReadFileCum fileCap + 528,288` (`BoundedRustEvs 32 8192`)
`+ 1,607` (`name` clone) `+ fineDirPutCum maxEntries`
(`= 551,818 + fineReadFileCum fileCap + fineDirPutCum maxEntries`:
`= 573,313` B with `Δlive = 0, Δpeak = 0, maxReq = 8,192` at `0 < fileCap ≤ 4,096, maxEntries ≤ 4`). -/
def smallStorePollTightDeltaCum (fileCap maxEntries : Nat) : Nat :=
  551818 + fineReadFileCum fileCap + fineDirPutCum maxEntries

def smallStorePollTightDeltaLive (fileCap maxEntries : Nat) : Nat :=
  fineReadFileLive fileCap + fineDirPutLive maxEntries

def smallStorePollTightDeltaPeak (fileCap maxEntries : Nat) : Nat :=
  max (fineReadFilePeak fileCap) (fineReadFileLive fileCap + fineDirPutLive maxEntries)

def smallStorePollTightMaxReq (fileCap maxEntries : Nat) : Nat :=
  max (max 8192 (fineReadFileMaxReq fileCap)) (96 * max 4 (2 * maxEntries))

theorem smallStorePoll_phaseCredit_tight
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (CliSmallStorePollEnv rd files dir name)
      (smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries) := by
  unfold CliSmallStorePollEnv
  set fc := max maxVal fileCap
  have hcap' : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fc :=
    fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)
  have hdc64 : DirDomainCaps 64 maxEntries fc dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_max_left _ _)
  have h1 := decimal_fine_phaseCredit_tight 0#32
  have h2 := dirGet_rule_fine_phaseCredit_tight rd files dir name hdc64 hname hcap'
  rw [Nat.max_self fc] at h2
  have h3 : PhaseCreditSpec fineCostModel (BoundedRustEvs 32 8192) 528288 0 0 8192 :=
    (boundedRustEvs_fine_phaseCredit_tight (Nat.le_refl 8192)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8192)
  have h4 := seq_freeOnly fineCostModel_freeNonInc
    (dirPutStr_fine_phaseCredit_tight dir name [] hdc64 hname)
  have h34 : PhaseCreditSpec fineCostModel
      (SeqEnv (BoundedRustEvs 32 8192) (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs))
      (529895 + fineDirPutCum maxEntries)
      (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries)
      (max 8192 (96 * max 4 (2 * maxEntries))) :=
    (h3.seq h4).mono
      (by rw [← Nat.add_assoc 528288 1607, show 528288 + 1607 = 529895 by decide])
      (Nat.le_of_eq (Nat.zero_add _))
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
      (Nat.le_refl _)
  have h234 : PhaseCreditSpec fineCostModel
      (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
        (SeqEnv (BoundedRustEvs 32 8192) (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)))
      (551080 + fineReadFileCum fc + fineDirPutCum maxEntries)
      (fineReadFileLive fc + fineDirPutLive maxEntries)
      (max (fineReadFilePeak fc) (fineReadFileLive fc + fineDirPutLive maxEntries))
      (smallStorePollTightMaxReq fc maxEntries) := by
    refine (h2.seq h34).mono ?_ (Nat.le_refl _) (Nat.le_refl _) ?_
    · omega
    · unfold smallStorePollTightMaxReq
      have h256 : 256 ≤ max 8192 (fineReadFileMaxReq fc) :=
        Nat.le_trans (by decide : 256 ≤ 8192) (Nat.le_max_left 8192 _)
      exact Nat.max_le.mpr
        ⟨Nat.max_le.mpr
           ⟨Nat.le_trans h256 (Nat.le_max_left _ _),
            Nat.le_trans (Nat.le_max_right 8192 _) (Nat.le_max_left _ _)⟩,
         Nat.max_le.mpr
           ⟨Nat.le_trans (Nat.le_max_left 8192 _) (Nat.le_max_left _ _),
            Nat.le_max_right _ _⟩⟩
  have h1234 := h1.seq h234
  unfold smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
  refine h1234.mono ?_ (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩) ?_
  · omega
  · unfold smallStorePollTightMaxReq
    have h32 : 32 ≤ max (max 8192 (fineReadFileMaxReq fc)) (96 * max 4 (2 * maxEntries)) :=
      Nat.le_trans (by decide : 32 ≤ 8192)
        (Nat.le_trans (Nat.le_max_left 8192 _) (Nat.le_max_left _ _))
    exact Nat.max_le.mpr ⟨h32, Nat.le_refl _⟩

/-- Parametric decode-envelope variant of `smallStorePoll_phaseCredit_tight`: replaces the fixed
`BoundedRustEvs 32 8192` (`528,288` B) with any tighter small decode envelope `DecEnv` of cost
`(decCum, 0, 0, decMaxReq)` (`decMaxReq ≤ 8,192`), yielding
`Δcum = 23,530 + fineReadFileCum fileCap + decCum + fineDirPutCum maxEntries`
(`= 45,025 + decCum` with `Δlive = 0, Δpeak = 0, maxReq = 8,192` at `0 < fileCap ≤ 4,096, maxEntries ≤ 4`). -/
def CliSmallStorePollOfEnv (DecEnv : List AllocEvent → Prop)
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (CliDecimalEnv 0#32)
    (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
      (SeqEnv DecEnv
        (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)))
    evs

def smallStorePollOfDecodeTightDeltaCum (fileCap decCum maxEntries : Nat) : Nat :=
  23530 + fineReadFileCum fileCap + decCum + fineDirPutCum maxEntries

theorem smallStorePollOfDecode_phaseCredit_tight
    {DecEnv : List AllocEvent → Prop}
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {maxDir maxEntries maxVal fileCap decCum decMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap)
    (hdec : PhaseCreditSpec fineCostModel DecEnv decCum 0 0 decMaxReq)
    (hdecReq : decMaxReq ≤ 8192) :
    PhaseCreditSpec fineCostModel (CliSmallStorePollOfEnv DecEnv rd files dir name)
      (smallStorePollOfDecodeTightDeltaCum (max maxVal fileCap) decCum maxEntries)
      (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries)
      (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries) := by
  unfold CliSmallStorePollOfEnv
  set fc := max maxVal fileCap
  have hcap' : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fc :=
    fun bs h => Nat.le_trans (hcap bs h) (Nat.le_max_right maxVal fileCap)
  have hdc64 : DirDomainCaps 64 maxEntries fc dir :=
    hdc.mono hdir (Nat.le_refl _) (Nat.le_max_left _ _)
  have h1 := decimal_fine_phaseCredit_tight 0#32
  have h2 := dirGet_rule_fine_phaseCredit_tight rd files dir name hdc64 hname hcap'
  rw [Nat.max_self fc] at h2
  have h3 : PhaseCreditSpec fineCostModel DecEnv decCum 0 0 8192 :=
    hdec.mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) hdecReq
  have h4 := seq_freeOnly fineCostModel_freeNonInc
    (dirPutStr_fine_phaseCredit_tight dir name [] hdc64 hname)
  have h34 : PhaseCreditSpec fineCostModel
      (SeqEnv DecEnv (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs))
      (1607 + decCum + fineDirPutCum maxEntries)
      (fineDirPutLive maxEntries)
      (fineDirPutLive maxEntries)
      (max 8192 (96 * max 4 (2 * maxEntries))) := by
    refine (h3.seq h4).mono ?_ (Nat.le_of_eq (Nat.zero_add _))
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩) (Nat.le_refl _)
    rw [← Nat.add_assoc decCum 1607, Nat.add_comm decCum 1607]
  have h234 : PhaseCreditSpec fineCostModel
      (SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
        (SeqEnv DecEnv (SeqEnv (CliDirPutStrEnv dir name []) FreeOnlyEvs)))
      (22792 + fineReadFileCum fc + decCum + fineDirPutCum maxEntries)
      (fineReadFileLive fc + fineDirPutLive maxEntries)
      (max (fineReadFilePeak fc) (fineReadFileLive fc + fineDirPutLive maxEntries))
      (smallStorePollTightMaxReq fc maxEntries) := by
    refine (h2.seq h34).mono ?_ (Nat.le_refl _) (Nat.le_refl _) ?_
    · omega
    · unfold smallStorePollTightMaxReq
      have h256 : 256 ≤ max 8192 (fineReadFileMaxReq fc) :=
        Nat.le_trans (by decide : 256 ≤ 8192) (Nat.le_max_left 8192 _)
      exact Nat.max_le.mpr
        ⟨Nat.max_le.mpr
           ⟨Nat.le_trans h256 (Nat.le_max_left _ _),
            Nat.le_trans (Nat.le_max_right 8192 _) (Nat.le_max_left _ _)⟩,
         Nat.max_le.mpr
           ⟨Nat.le_trans (Nat.le_max_left 8192 _) (Nat.le_max_left _ _),
            Nat.le_max_right _ _⟩⟩
  have h1234 := h1.seq h234
  unfold smallStorePollOfDecodeTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
  refine h1234.mono ?_ (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩) ?_
  · omega
  · unfold smallStorePollTightMaxReq
    have h32 : 32 ≤ max (max 8192 (fineReadFileMaxReq fc)) (96 * max 4 (2 * maxEntries)) :=
      Nat.le_trans (by decide : 32 ≤ 8192)
        (Nat.le_trans (Nat.le_max_left 8192 _) (Nat.le_max_left _ _))
    exact Nat.max_le.mpr ⟨h32, Nat.le_refl _⟩

end TightStorePeakSpec

end LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
