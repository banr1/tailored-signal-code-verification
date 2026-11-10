/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs

/-!
# `.rodata` Encoder and CLI Send Domain Bridges for `spqr::send`

Bridges protocol-level SPQR V1 well-formedness (`Erasure.EncInv`, `SendTotal.BOk`) and CLI send
inputs (`CliPqxdhInputs`, `w1SessKit.ScopeAt`) to the `.rodata` encoder validity predicates
(`EncRodataValid`, `StatesRodataValid`, `ValidEncoderPts640`, `ValidChainParams`) and 10-stage
`spqr::send` trace envelopes.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes PolyEncoder PqRatchetState States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.ChainProofs (ChainAddEpochGhost ChainIntoPbCall)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1Sync.Erasure (EncInv msgPoints needed)
open CryptoVerification.SpqrV1Sync.SendTotal (BOk EncWF)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
  (FineSmallEvs fineSmallEvs_phaseCreditSpec
   nonFreeCount_seqEnv_le smallAllocCost_le_143484_of_le_135167)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightHelpers
  (EncRodataValid StatesRodataValid isRodataPtLen)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 ValidChainParams ValidEncoderPts640
   peerSpqrTightValid640_of_cliPqInputs_send peerSpqrTightValidAt_of_w1ScopeAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt ValidV1PtsAt)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (nonFreeCount nonFreeCount_eq_zero_of_freeOnly)

/-! ## `EncWF` and `BOk` to `.rodata` Encoder Validity -/

private theorem needed_eq_div32 {len : Nat}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152) (j : Nat) :
    needed len j = len / 32 := by
  rcases hlen with rfl | rfl | rfl | rfl <;> simp [needed]

theorem needed_isRodata_and_le_36 {len : Nat}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152) (j : Nat) :
    isRodataPtLen (needed len j) = true ∧ needed len j ≤ 36 := by
  rw [needed_eq_div32 hlen j]
  rcases hlen with rfl | rfl | rfl | rfl <;> decide

/-- Any `EncWF len enc` with `len ∈ {96, 160, 960, 1152}` satisfies `EncRodataValid enc`. -/
theorem encRodataValid_of_encWF {len : Nat} {enc : PolyEncoder}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152)
    (hwf : EncWF len enc) :
    EncRodataValid enc := by
  obtain ⟨msg, hinv, hmlen⟩ := hwf
  rcases hinv with hs | ⟨polys, hs, hplen, hp⟩
  · unfold EncRodataValid
    rw [hs]
    refine ⟨by simp [msgPoints], fun pt hpt => ?_⟩
    unfold msgPoints at hpt
    rcases List.mem_map.mp hpt with ⟨j, _, rfl⟩
    simp only [List.length_map, List.length_range, hmlen]
    exact (needed_isRodata_and_le_36 hlen j).1
  · unfold EncRodataValid
    rw [hs]
    refine ⟨Nat.le_of_eq hplen, fun p hp_mem => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp_mem
    rw [(hp j hj).1, hmlen]
    exact (needed_isRodata_and_le_36 hlen j).2

/-- Every well-formed braid state `BOk st` satisfies `StatesRodataValid st`. -/
theorem statesRodataValid_of_bOk {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} (hb : BOk st) :
    StatesRodataValid st := by
  cases st with
  | keysUnsampled _ | ekSentCt1Received _ | noHeaderReceived _ | ct1Acknowledged _ =>
    trivial
  | headerReceived s =>
    change s.uc.auth.rootKey.length ≤ 32
    exact Nat.le_of_eq hb.1.1
  | keysSampled _ =>
    exact encRodataValid_of_encWF (Or.inl rfl) hb.2.2
  | headerSent _ =>
    exact encRodataValid_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2.1
  | ct1Received _ =>
    exact encRodataValid_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2
  | ct1Sampled _ =>
    exact encRodataValid_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2.1
  | ekReceivedCt1Sampled _ =>
    exact encRodataValid_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2
  | ct2Sampled _ =>
    exact encRodataValid_of_encWF (Or.inr (Or.inl rfl)) hb.2

/-! ## CLI `send` Session-Store Bridge and Domain Bundles -/

/-- Extracts `ValidEncoderPts640 otrPqr ∧ ValidChainParams otrPqr ∧ otrPqr.length < 2 ^ 31` from `CliPqxdhInputs` on `.send peer` and `w1SessKit.ScopeAt`.
-/
theorem cliSend_peerSpqrTightValid640 {B : RunBudgets} {img : Image}
    {W : PEParams} {i : Inputs} {peer : AddrV} {peerG : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otrPqr : List (BitVec 8)}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peer))
    (hScAt : (w1SessKit B img (runFiles i) peerG).ScopeAt scopeKit
      StoresGhost.opened.sessions (addrValOf peer) r)
    (hcur : r.currentSession = some sess)
    (hpqr : otrPqr = sess.state.pqRatchetState) :
    ValidEncoderPts640 otrPqr ∧ ValidChainParams otrPqr ∧ otrPqr.length < 2 ^ 31 :=
  peerSpqrTightValidAt_of_w1ScopeAt hScAt hcur hpqr
    (peerSpqrTightValid640_of_cliPqInputs_send hi hparse)

/-- Domain invariant bundle for `spqr::send` at `links ≤ 4` and `postSt ≤ 286,196` bytes. -/
structure SpqrSendTightDomain (F : ShaCompress)
    (stBytes : Bytes) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost)
    (xSInto : StatesIntoPbGhost F)
    (xCInto : ChainIntoPbCall)
    (postSt : PqRatchetState) : Prop where
  hLen : stBytes.length ≤ spqrStateTightCapBytes
  hPts : ValidEncoderPts640 stBytes
  hChainParams : ValidChainParams stBytes
  hV1Pts : ValidV1PtsAt 640 pb
  hV1Raw : rawV1State pb ≤ 46880
  hRodata : StatesRodataValid st0
  hAddLinks : xAdd.self.links.length ≤ 4
  hCIntoLinks : xCInto.chain.links.length ≤ 4
  hSIntoPts : StatesPtsBoundedAt 640 xSInto.st
  hSIntoV1Pts : ValidV1PtsAt 640 xSInto.st.into_pb
  hSIntoRaw : rawV1State xSInto.st.into_pb ≤ 49856
  hPostLen : pqRatchetStatePBEncodedLen postSt ≤ 286196

/-- Relaxed `spqr::send` domain invariant bundle allowing `xCInto.chain.links.length ≤ 707`. -/
structure SpqrSendTightDomain707 (F : ShaCompress)
    (stBytes : Bytes) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost)
    (xSInto : StatesIntoPbGhost F)
    (xCInto : ChainIntoPbCall)
    (postSt : PqRatchetState) : Prop where
  hLen : stBytes.length ≤ spqrStateTightCapBytes
  hPts : ValidEncoderPts640 stBytes
  hChainParams : ValidChainParams stBytes
  hV1Pts : ValidV1PtsAt 640 pb
  hV1Raw : rawV1State pb ≤ 46880
  hRodata : StatesRodataValid st0
  hAddLinks : xAdd.self.links.length ≤ 4
  hCIntoLinks : xCInto.chain.links.length ≤ 707
  hSIntoPts : StatesPtsBoundedAt 640 xSInto.st
  hSIntoV1Pts : ValidV1PtsAt 640 xSInto.st.into_pb
  hSIntoRaw : rawV1State xSInto.st.into_pb ≤ 49856
  hPostLen : pqRatchetStatePBEncodedLen postSt ≤ 286196

theorem SpqrSendTightDomain.to707 {F : ShaCompress}
    {stBytes : Bytes} {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {xAdd : ChainAddEpochGhost} {xSInto : StatesIntoPbGhost F}
    {xCInto : ChainIntoPbCall} {postSt : PqRatchetState}
    (d : SpqrSendTightDomain F stBytes pb st0 xAdd xSInto xCInto postSt) :
    SpqrSendTightDomain707 F stBytes pb st0 xAdd xSInto xCInto postSt where
  hLen := d.hLen
  hPts := d.hPts
  hChainParams := d.hChainParams
  hV1Pts := d.hV1Pts
  hV1Raw := d.hV1Raw
  hRodata := d.hRodata
  hAddLinks := d.hAddLinks
  hCIntoLinks := Nat.le_trans d.hCIntoLinks (by decide)
  hSIntoPts := d.hSIntoPts
  hSIntoV1Pts := d.hSIntoV1Pts
  hSIntoRaw := d.hSIntoRaw
  hPostLen := d.hPostLen

/-! ## Tight `PqRatchetState::encode_to_vec` and 10-Stage `spqr::send` Envelopes -/

/-- Large-class (`135,167 < req ≤ maxLen`) envelope for `PqRatchetState::encode_to_vec`. -/
def PqEncodeLargeTightEnv (maxLen : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ 1 ∧
  ∀ ev ∈ evs,
    (∀ r, ev = .alloc r → 135167 < r ∧ r ≤ maxLen) ∧
    (∀ al r, ev = .aligned al r → 135167 < r ∧ r ≤ maxLen ∧ al ≤ 16) ∧
    (∀ al o n, ev ≠ .realloc al o n)

/-- Combined small-or-large (`0 ≤ req ≤ maxLen`) envelope for `PqRatchetState::encode_to_vec`. -/
def PqEncodeCapTightEnv (maxLen : Nat) (evs : List AllocEvent) : Prop :=
  FineSmallEvs 1 143484 (min maxLen 135167) evs ∨ PqEncodeLargeTightEnv maxLen evs

private theorem stepEvents_pqEncodeLarge_model_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmallEq : HasFineReallocCredit.smallMaxReq M = 135167)
    (hMetaEq : HasFineReallocCredit.largeMetaCost M = 122)
    (hLargeEq : ∀ r, HasFineReallocCredit.largeCost M r = r + 8195)
    {maxLen : Nat} :
    ∀ (evs : List AllocEvent) (maxOps : Nat) (st0 : M.σ),
      maxOps ≤ 1 →
      nonFreeCount evs ≤ maxOps →
      (∀ ev ∈ evs,
        (∀ r, ev = .alloc r → 135167 < r ∧ r ≤ maxLen) ∧
        (∀ al r, ev = .aligned al r → 135167 < r ∧ r ≤ maxLen ∧ al ≤ 16) ∧
        (∀ al o n, ev ≠ .realloc al o n)) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxOps * 122 ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 + maxOps * (maxLen + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + maxOps * (maxLen + 8195))
  | [], _, st0, _, _, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
  | .free al sz :: tl, maxOps, st0, hmo, hcnt, hall => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount] at hcnt
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_pqEncodeLarge_model_le hM hSmallEq hMetaEq hLargeEq tl maxOps
        (M.step (.free al sz) st0) hmo hcnt (fun e he => hall e (List.mem_cons_of_mem _ he))
    exact ⟨Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ _),
      Nat.le_trans hl₂ (Nat.add_le_add_right hl₁ _),
      Nat.le_trans hp₂ (Nat.max_le.mpr ⟨Nat.le_trans hp₁ (Nat.le_max_left _ _),
        Nat.le_trans (Nat.add_le_add_right hl₁ _) (Nat.le_max_right _ _)⟩)⟩
  | .alloc r :: tl, maxOps, st0, hmo, hcnt, hall => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount] at hcnt
    have hm1 : maxOps = 1 := by omega
    subst hm1
    obtain ⟨hgt, hr_le⟩ := (hall (.alloc r) List.mem_cons_self).1 r rfl
    have hgt' : HasFineReallocCredit.smallMaxReq M < r := by
      rw [hSmallEq]; exact hgt
    obtain ⟨hc₁, hl₁, hp₁⟩ := HasFineReallocCredit.step_alloc_large st0 hgt'
    rw [hMetaEq] at hc₁
    rw [hLargeEq r] at hl₁ hp₁
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_pqEncodeLarge_model_le hM hSmallEq hMetaEq hLargeEq tl 0
        (M.step (.alloc r) st0) (Nat.zero_le 1) (by omega)
        (fun e he => hall e (List.mem_cons_of_mem _ he))
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hc₂ hl₂ hp₂ ⊢
    have hlive_cap : HasFineReallocCredit.liveLarge (M.step (.alloc r) st0) ≤
        HasFineReallocCredit.liveLarge st0 + (maxLen + 8195) :=
      Nat.le_trans hl₁ (Nat.add_le_add_left (Nat.add_le_add_right hr_le 8195) _)
    exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hlive_cap,
      Nat.le_trans hp₂ (Nat.max_le.mpr ⟨Nat.le_trans hp₁ (Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_right hr_le 8195) _)
           (Nat.le_max_right _ _)⟩),
        Nat.le_trans hlive_cap (Nat.le_max_right _ _)⟩)⟩
  | .aligned al r :: tl, maxOps, st0, hmo, hcnt, hall => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount] at hcnt
    have hm1 : maxOps = 1 := by omega
    subst hm1
    obtain ⟨hgt, hr_le, hal⟩ := (hall (.aligned al r) List.mem_cons_self).2.1 al r rfl
    have hgt' : HasFineReallocCredit.smallMaxReq M < r := by
      rw [hSmallEq]; exact hgt
    obtain ⟨hc₁, hl₁, hp₁⟩ := HasFineReallocCredit.step_aligned_large st0 hal hgt'
    rw [hMetaEq] at hc₁
    rw [hLargeEq r] at hl₁ hp₁
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_pqEncodeLarge_model_le hM hSmallEq hMetaEq hLargeEq tl 0
        (M.step (.aligned al r) st0) (Nat.zero_le 1) (by omega)
        (fun e he => hall e (List.mem_cons_of_mem _ he))
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at hc₂ hl₂ hp₂ ⊢
    have hlive_cap : HasFineReallocCredit.liveLarge (M.step (.aligned al r) st0) ≤
        HasFineReallocCredit.liveLarge st0 + (maxLen + 8195) :=
      Nat.le_trans hl₁ (Nat.add_le_add_left (Nat.add_le_add_right hr_le 8195) _)
    exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hlive_cap,
      Nat.le_trans hp₂ (Nat.max_le.mpr ⟨Nat.le_trans hp₁ (Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_right hr_le 8195) _)
           (Nat.le_max_right _ _)⟩),
        Nat.le_trans hlive_cap (Nat.le_max_right _ _)⟩)⟩
  | .realloc al o n :: _, _, _, _, _, hall =>
    False.elim ((hall (.realloc al o n) List.mem_cons_self).2.2 al o n rfl)

theorem pqEncodeLargeTight_fine_phaseCreditSpec (maxLen : Nat) :
    PhaseCreditSpec fineCostModel (PqEncodeLargeTightEnv maxLen)
      122 (maxLen + 8195) (maxLen + 8195) maxLen where
  req_align evs hE ev hev := by
    obtain ⟨ha, hal, hre⟩ := hE.2 ev hev
    cases ev with
    | free _ _ => exact ⟨Nat.zero_le maxLen, Nat.le_refl 16⟩
    | alloc r => exact ⟨(ha r rfl).2, Nat.le_refl 16⟩
    | aligned al r => exact ⟨(hal al r rfl).2.1, (hal al r rfl).2.2⟩
    | realloc al o n => exact False.elim (hre al o n rfl)
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ :=
      stepEvents_pqEncodeLarge_model_le fineCostModel_modelHyps fineCostModel_smallMaxReq_eq
        fineCostModel_largeMetaCost_eq fineCostModel_largeCost_eq evs 1 st0 (Nat.le_refl 1)
        hE.1 hE.2
    simp only [Nat.one_mul] at hc hl hp
    exact ⟨hc, hl, hp⟩

theorem pqEncodeCapTight_fine_phaseCreditSpec (maxLen : Nat) :
    PhaseCreditSpec fineCostModel (PqEncodeCapTightEnv maxLen)
      143484 (maxLen + 8195) (maxLen + 8195) maxLen := by
  have hsm := fineSmallEvs_phaseCreditSpec 1 143484 (Nat.min_le_right maxLen 135167)
  have hlg := pqEncodeLargeTight_fine_phaseCreditSpec maxLen
  exact (hsm.or hlg).mono (by decide) (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.min_le_left maxLen 135167, Nat.le_refl maxLen⟩)

theorem pqEncodeLargeTight_nonFreeCount_le {maxLen : Nat} {evs : List AllocEvent}
    (h : PqEncodeLargeTightEnv maxLen evs) :
    nonFreeCount evs ≤ 1 :=
  h.1

theorem pqEncodeCapTight_nonFreeCount_le {maxLen : Nat} {evs : List AllocEvent}
    (h : PqEncodeCapTightEnv maxLen evs) :
    nonFreeCount evs ≤ 1 := by
  rcases h with hs | hl
  · exact hs.1
  · exact hl.1

theorem pqRatchetStateEncodeToVecEnv_to_largeTight {st : PqRatchetState} {maxLen : Nat}
    {evs : List AllocEvent}
    (hgt : 135167 < pqRatchetStatePBEncodedLen st)
    (hle : pqRatchetStatePBEncodedLen st ≤ maxLen)
    (hEnv : PqRatchetStateEncodeToVecEnv st evs) :
    PqEncodeLargeTightEnv maxLen evs := by
  rcases hEnv with ⟨hz, rfl⟩ | ⟨hpos, rfl⟩
  · omega
  · have hcond : 1 ≤ 16 ∧ 1 ≤ pqRatchetStatePBEncodedLen st := ⟨by decide, hpos⟩
    simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨(fun r hr => by injection hr with hr'; subst hr'; exact ⟨hgt, hle⟩),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem pqRatchetStateEncodeToVecEnv_to_capTight {st : PqRatchetState} {maxLen : Nat}
    {evs : List AllocEvent}
    (hle : pqRatchetStatePBEncodedLen st ≤ maxLen)
    (hEnv : PqRatchetStateEncodeToVecEnv st evs) :
    PqEncodeCapTightEnv maxLen evs := by
  by_cases hgt : 135167 < pqRatchetStatePBEncodedLen st
  · exact Or.inr (pqRatchetStateEncodeToVecEnv_to_largeTight hgt hle hEnv)
  · left
    have hsm : pqRatchetStatePBEncodedLen st ≤ 135167 := Nat.le_of_not_lt hgt
    rcases hEnv with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact FineSmallEvs.nil 1 143484 (min maxLen 135167)
    · exact FineSmallEvs.rustAlloc (by decide) (Nat.le_min.mpr ⟨hle, hsm⟩)
        (smallAllocCost_le_143484_of_le_135167 hsm)

/-- Generic 10-stage binary-order `spqr::send::<HookRng>` (`Block 124`) envelope composing
`decode_state`, `States::from_pb`, `States::send`, `chain_from`, optional `Chain::add_epoch` and
`Chain::send_key`, `Chain::into_pb`, `Message::serialize`, `States::into_pb`, and
`PqRatchetState::encode_to_vec` with `FreeOnlyEvs` teardown exits. -/
def SpqrSendPartsTightGenEnv
    (Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv Edec (fun e₁ => FreeOnlyEvs e₁ ∨
      SeqEnv Efrom (fun e₂ => FreeOnlyEvs e₂ ∨
        SeqEnv Esend (fun e₃ => FreeOnlyEvs e₃ ∨
          SeqEnv Ecfrom (fun e₄ => FreeOnlyEvs e₄ ∨
            SeqEnv Eadd (fun e₅ => FreeOnlyEvs e₅ ∨
              SeqEnv Esk (fun e₆ => FreeOnlyEvs e₆ ∨
                SeqEnv Ecinto
                  (SeqEnv Emsg
                    (SeqEnv Esinto
                      (SeqEnv Epq FreeOnlyEvs))) e₆) e₅) e₄) e₃) e₂) e₁) evs

theorem spqrSendPartsTightGenEnv_nil
    (Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq : List AllocEvent → Prop) :
    SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq [] :=
  Or.inl fun _ h => nomatch h

private theorem phaseCreditSpec_or_freeOnly_left
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (hE : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => FreeOnlyEvs evs ∨ E evs) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hE).mono
    (Nat.max_le.mpr ⟨Nat.zero_le c, Nat.le_refl c⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le l, Nat.le_refl l⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le p, Nat.le_refl p⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le r, Nat.le_refl r⟩)

private theorem phaseCreditSpec_seq_zero_left
    {E₁ E₂ : List AllocEvent → Prop} {c₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 0 0 r₁)
    (h₂ : PhaseCreditSpec fineCostModel E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel (SeqEnv E₁ E₂) (c₁ + c₂) l₂ p₂ (max r₁ r₂) :=
  (h₁.seq h₂).mono
    (Nat.le_refl (c₁ + c₂))
    (Nat.le_of_eq (Nat.zero_add l₂))
    (Nat.max_le.mpr ⟨Nat.zero_le p₂, Nat.le_of_eq (Nat.zero_add p₂)⟩)
    (Nat.le_refl (max r₁ r₂))

theorem spqrSendPartsTightGen_phaseCreditSpec
    {Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq : List AllocEvent → Prop}
    {cDec rDec cFrom rFrom cSend rSend cCfrom rCfrom cAdd rAdd cSk rSk cCinto rCinto
     cMsg rMsg cSinto rSinto cPq lPq pPq rPq : Nat}
    (hDec : PhaseCreditSpec fineCostModel Edec cDec 0 0 rDec)
    (hFrom : PhaseCreditSpec fineCostModel Efrom cFrom 0 0 rFrom)
    (hSend : PhaseCreditSpec fineCostModel Esend cSend 0 0 rSend)
    (hCfrom : PhaseCreditSpec fineCostModel Ecfrom cCfrom 0 0 rCfrom)
    (hAdd : PhaseCreditSpec fineCostModel Eadd cAdd 0 0 rAdd)
    (hSk : PhaseCreditSpec fineCostModel Esk cSk 0 0 rSk)
    (hCinto : PhaseCreditSpec fineCostModel Ecinto cCinto 0 0 rCinto)
    (hMsg : PhaseCreditSpec fineCostModel Emsg cMsg 0 0 rMsg)
    (hSinto : PhaseCreditSpec fineCostModel Esinto cSinto 0 0 rSinto)
    (hPq : PhaseCreditSpec fineCostModel Epq cPq lPq pPq rPq)
    (hlp : lPq ≤ pPq) :
    PhaseCreditSpec fineCostModel
      (SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq)
      (cDec + (cFrom + (cSend + (cCfrom + (cAdd + (cSk + (cCinto + (cMsg + (cSinto + cPq)))))))))
      lPq pPq
      (max rDec (max rFrom (max rSend (max rCfrom (max rAdd
        (max rSk (max rCinto (max rMsg (max rSinto rPq))))))))) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have h10 : PhaseCreditSpec fineCostModel (SeqEnv Epq FreeOnlyEvs) cPq lPq pPq rPq :=
    (hPq.seq hFree).mono
      (Nat.le_of_eq (Nat.add_zero cPq))
      (Nat.le_of_eq (Nat.add_zero lPq))
      (Nat.max_le.mpr ⟨Nat.le_refl pPq, Nat.le_trans (Nat.le_of_eq (Nat.add_zero lPq)) hlp⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl rPq, Nat.zero_le rPq⟩)
  have h9 := phaseCreditSpec_seq_zero_left hSinto h10
  have h8 := phaseCreditSpec_seq_zero_left hMsg h9
  have h7 := phaseCreditSpec_seq_zero_left hCinto h8
  have h6 := phaseCreditSpec_seq_zero_left hSk (phaseCreditSpec_or_freeOnly_left h7)
  have h5 := phaseCreditSpec_seq_zero_left hAdd (phaseCreditSpec_or_freeOnly_left h6)
  have h4 := phaseCreditSpec_seq_zero_left hCfrom (phaseCreditSpec_or_freeOnly_left h5)
  have h3 := phaseCreditSpec_seq_zero_left hSend (phaseCreditSpec_or_freeOnly_left h4)
  have h2 := phaseCreditSpec_seq_zero_left hFrom (phaseCreditSpec_or_freeOnly_left h3)
  have h1 := phaseCreditSpec_seq_zero_left hDec (phaseCreditSpec_or_freeOnly_left h2)
  exact phaseCreditSpec_or_freeOnly_left h1

theorem spqrSendPartsTightGen_nonFreeCount_le
    {Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq : List AllocEvent → Prop}
    {kDec kFrom kSend kCfrom kAdd kSk kCinto kMsg kSinto kPq : Nat}
    (hDec : ∀ e, Edec e → nonFreeCount e ≤ kDec)
    (hFrom : ∀ e, Efrom e → nonFreeCount e ≤ kFrom)
    (hSend : ∀ e, Esend e → nonFreeCount e ≤ kSend)
    (hCfrom : ∀ e, Ecfrom e → nonFreeCount e ≤ kCfrom)
    (hAdd : ∀ e, Eadd e → nonFreeCount e ≤ kAdd)
    (hSk : ∀ e, Esk e → nonFreeCount e ≤ kSk)
    (hCinto : ∀ e, Ecinto e → nonFreeCount e ≤ kCinto)
    (hMsg : ∀ e, Emsg e → nonFreeCount e ≤ kMsg)
    (hSinto : ∀ e, Esinto e → nonFreeCount e ≤ kSinto)
    (hPq : ∀ e, Epq e → nonFreeCount e ≤ kPq)
    {evs : List AllocEvent}
    (h : SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq evs) :
    nonFreeCount evs ≤
      kDec + (kFrom + (kSend + (kCfrom + (kAdd + (kSk + (kCinto + (kMsg + (kSinto + kPq)))))))) := by
  have hFree : ∀ e, FreeOnlyEvs e → nonFreeCount e ≤ 0 :=
    fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)
  have hor : ∀ {P : List AllocEvent → Prop} {k : Nat},
      (∀ e, P e → nonFreeCount e ≤ k) → ∀ e, FreeOnlyEvs e ∨ P e → nonFreeCount e ≤ k := by
    intro P k hP e he
    rcases he with hf | hp
    · exact Nat.le_trans (hFree e hf) (Nat.zero_le k)
    · exact hP e hp
  have h10 : ∀ e, SeqEnv Epq FreeOnlyEvs e → nonFreeCount e ≤ kPq := fun _ he => by
    have hc := nonFreeCount_seqEnv_le hPq hFree he
    rwa [Nat.add_zero] at hc
  have h9 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hSinto h10 (evs := e) he
  have h8 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hMsg h9 (evs := e) he
  have h7 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hCinto h8 (evs := e) he
  have h6 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hSk (hor h7) (evs := e) he
  have h5 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hAdd (hor h6) (evs := e) he
  have h4 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hCfrom (hor h5) (evs := e) he
  have h3 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hSend (hor h4) (evs := e) he
  have h2 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hFrom (hor h3) (evs := e) he
  have h1 := fun (e : List AllocEvent) he => nonFreeCount_seqEnv_le hDec (hor h2) (evs := e) he
  exact hor h1 evs h

private theorem seqEnv_imp_or (A : List AllocEvent → Prop) {B B₁ B₂ : List AllocEvent → Prop}
    (hB : ∀ x, B x → B₁ x ∨ B₂ x) :
    ∀ e, SeqEnv A B e → SeqEnv A B₁ e ∨ SeqEnv A B₂ e := by
  intro e hs
  rcases hs with ha | ⟨x₁, x₂, rfl, ha, hb⟩
  · exact Or.inl (Or.inl ha)
  · rcases hB x₂ hb with hb₁ | hb₂
    · exact Or.inl (Or.inr ⟨x₁, x₂, rfl, ha, hb₁⟩)
    · exact Or.inr (Or.inr ⟨x₁, x₂, rfl, ha, hb₂⟩)

private theorem freeOr_imp_or {B B₁ B₂ : List AllocEvent → Prop}
    (hB : ∀ x, B x → B₁ x ∨ B₂ x) :
    ∀ e, FreeOnlyEvs e ∨ B e → (FreeOnlyEvs e ∨ B₁ e) ∨ (FreeOnlyEvs e ∨ B₂ e) := by
  intro e ho
  rcases ho with hf | hb
  · exact Or.inl (Or.inl hf)
  · rcases hB e hb with hb₁ | hb₂
    · exact Or.inl (Or.inr hb₁)
    · exact Or.inr (Or.inr hb₂)

theorem spqrSendPartsTightGenEnv_or_pq
    {Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq₁ Epq₂ : List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto
      (fun e => Epq₁ e ∨ Epq₂ e) evs) :
    SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq₁ evs ∨
    SpqrSendPartsTightGenEnv Edec Efrom Esend Ecfrom Eadd Esk Ecinto Emsg Esinto Epq₂ evs := by
  unfold SpqrSendPartsTightGenEnv at h ⊢
  have h10 : ∀ e, SeqEnv (fun x => Epq₁ x ∨ Epq₂ x) FreeOnlyEvs e →
      SeqEnv Epq₁ FreeOnlyEvs e ∨ SeqEnv Epq₂ FreeOnlyEvs e := by
    intro e hs
    rcases hs with (hp₁ | hp₂) | ⟨x₁, x₂, rfl, hp₁ | hp₂, hf⟩
    · exact Or.inl (Or.inl hp₁)
    · exact Or.inr (Or.inl hp₂)
    · exact Or.inl (Or.inr ⟨x₁, x₂, rfl, hp₁, hf⟩)
    · exact Or.inr (Or.inr ⟨x₁, x₂, rfl, hp₂, hf⟩)
  exact freeOr_imp_or (seqEnv_imp_or Edec (freeOr_imp_or (seqEnv_imp_or Efrom (freeOr_imp_or
    (seqEnv_imp_or Esend (freeOr_imp_or (seqEnv_imp_or Ecfrom (freeOr_imp_or (seqEnv_imp_or Eadd
      (freeOr_imp_or (seqEnv_imp_or Esk (freeOr_imp_or
        (seqEnv_imp_or Ecinto (seqEnv_imp_or Emsg (seqEnv_imp_or Esinto h10))))))))))))))) evs h

end LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
