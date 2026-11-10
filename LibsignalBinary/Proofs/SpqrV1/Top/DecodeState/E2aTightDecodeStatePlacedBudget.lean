/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Guarded-Tight Placed Verification of `spqr::decode_state` (Block `325`)

Extends canonical `PqRatchetState` extraction to `SpqrStateTight640 F K bs`, bridges
`EpochDirectionPB::merge` and `V1State::merge` tight contracts to the canonical entry seam,
and proves guarded-tight `spqr::decode_state` contracts under `tlb_DecodeStateGuardedEnv F K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement ls_subroutine_ok_cl_of_plain lsmpl subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB MlKem PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (V1StateMergeGhost v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost EpochDirectionMergeGhost V1InnerHeapPred decodeStatePlacedEntry
   decodeStatePlacedProg decodeStateStackX)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateDom tlb_DecodeStateGuardedEnv tlb_DecodeStateGuardedEnvOf
   tlb_EpochDirDom tlb_EpochDirectionGuardedEnvOf tlb_EpochDirectionMergeBlk325TightOkOf
   tlb_V1StateMergeBlk325TightOkOf tlb_V1StateMergeGuardedEnvOf tlb_ValidPqRatchetStatePB
   tlb_ValidV1StatePB tlb_decodeStateGuardedEnv_mono tlb_domHeap_of_dom
   tlb_epochDirDom_zero_imp_79236 tlb_epochDirectionMergeTightSpecOfEnv
   tlb_fitsEnv_fallback_of_not_dom tlb_guardedEnv_tight_of_dom)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (SpqrStateTight640)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux (e2a_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
  (e2ar_topStateTight_encode_valid)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStateChPlacedBudget
  (E2aEpochDirCanonicalOk e2a_ValidChainPB)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudgetAux
  (e2a_ValidVersionNegotiationPB e2a_decodeState_entry_canonical_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget
  (decodeStatePanicPostPlacedOfEnv decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoopClPlacedBudget
  (decodeState_entry_5349c_cl_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX DecodeStatePlacedOkOfEnv spqrDecodeStatePlacedSpecOfEnv)

/-! ## 1. `SpqrStateTight640` Canonical Extraction & `PlacedX → ClPlacedX` / Envelope Lifts -/

/-- Every `SpqrStateTight640 F K bs` state (`bs = [] ∨ TopStateTight F K bs`) is a canonical
`encodeState pb` satisfying `tlb_ValidPqRatchetStatePB pb` (`[] = encodeState default`). -/
theorem e2a_spqrStateTight640_encode_valid {F : ShaCompress} {K : MlKem} {bs : Bytes}
    (hDom : SpqrStateTight640 F K bs) :
    ∃ pb : PqRatchetState, bs = encodeState pb ∧ tlb_ValidPqRatchetStatePB pb := by
  rcases hDom with rfl | hTop
  · refine ⟨{ versionNegotiation := none, chain := none, inner := none }, rfl, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro vn hvn; simp at hvn
    · intro ch hch; simp at hch
    · intro v1 hv1; simp at hv1
  · exact e2ar_topStateTight_encode_valid hTop

/-- Weaken `DecodeStateCalleeContractsPlacedX` to `DecodeStateCalleeContractsClPlacedX`. -/
theorem e2a_contractsClPlacedX_of_placedX [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    DecodeStateCalleeContractsClPlacedX H_inner A lim ext where
  of_drop_inner := hc.of_drop_inner
  of_cap_inner := hc.of_cap_inner
  dealloc := hc.dealloc
  memcpy := hc.memcpy
  session_memcpy := hc.session_memcpy
  decodeErrorFrom := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorFrom
  decodeErrorPush := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeErrorPush
  decodeVarint2 := subroutine_ok_withLsCodeLoaded_of_plain hc.decodeVarint2
  skipField3 := subroutine_ok_withLsCodeLoaded_of_plain hc.skipField3
  chainParamsMerge := subroutine_ok_withLsCodeLoaded_of_plain hc.chainParamsMerge
  growOneChainEpoch := subroutine_ok_withLsCodeLoaded_of_plain hc.growOneChainEpoch
  dropOptProtoInnerState := ls_subroutine_ok_cl_of_plain hc.dropOptProtoInnerState
  dropProtoPqRatchetState := ls_subroutine_ok_cl_of_plain hc.dropProtoPqRatchetState
  bytesMerge3 := hc.bytesMerge3
  epochDirectionMerge := hc.epochDirectionMerge
  v1StateMerge := hc.v1StateMerge

/-- Monotonicity of `DecodeStatePlacedOkOfEnv` when `PreEnv = PostEnv` widens (`Env₁ ⊆ Env₂`):
`FitsEnv M lim st (Env₂ x)` is contravariant (`FitsEnv Env₂ → FitsEnv Env₁`) while `PostEnv` is
covariant (`Env₁ x evs → Env₂ x evs`). -/
theorem e2a_decodeStatePlacedOkOfEnv_mono [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : DecodeStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hImp : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (hOk : DecodeStatePlacedOkOfEnv H_inner A lim Env₁ Env₁ ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim Env₂ Env₂ ext := by
  refine subroutine_ok_mono hOk (fun ⟨x, st⟩ R s0 hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv] at hp ⊢
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left
        (Entails.pure_left fun ⟨h1, h2, h3, hFit⟩ =>
          Entails.pure_right ⟨h1, h2, h3, hFit.mono (hImp x)⟩ (Entails.refl _))))
      hp
  · dsimp only [withLsCodeRoLoaded, spqrDecodeStatePlacedSpecOfEnv] at hq ⊢
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left
        (Entails.sepExists_mono fun evs =>
          Entails.pure_left fun ⟨htr, hev⟩ =>
            Entails.pure_right ⟨htr, hImp x evs hev⟩ (Entails.refl _))))
      hq

/-! ## 2. Bridges from `SpqrTightLeafBridges` to Canonical Seams -/

private theorem e2a_epochDirectionGuarded_imp_tight {x : EpochDirectionMergeGhost}
    {maxPrev ops cum maxReq : Nat} {evs : List AllocEvent}
    (hCase : (maxPrev = 0 ∧ ops = 2 ∧ cum = 1476 ∧ maxReq = 32) ∨
             (maxPrev = 79236 ∧ ops = 4 ∧ cum = 181944 ∧ maxReq = 79236))
    (hDom : tlb_EpochDirDom maxPrev x)
    (hEv : tlb_EpochDirectionGuardedEnvOf 2 4 x evs) :
    SpqrTightEvs ops cum maxReq evs := by
  rcases hCase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rcases hEv with ⟨_, ht⟩ | ⟨hnot0, _⟩ | ⟨hnot79, _⟩
    · exact ht
    · exact absurd hDom hnot0
    · exact absurd (tlb_epochDirDom_zero_imp_79236 hDom) hnot79
  · rcases hEv with ⟨_, ht⟩ | ⟨_, _, ht⟩ | ⟨hnot79, _⟩
    · exact ht.mono (by decide) (by decide) (by decide)
    · exact ht
    · exact absurd hDom hnot79

/-- Bridge `tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext` to `E2aEpochDirCanonicalOk`. -/
theorem e2a_epochDirCanonicalOk_of_tlb [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext) :
    E2aEpochDirCanonicalOk A lim ext := by
  intro maxPrev ops cum maxReq hCase
  refine subroutine_ok_refine hEpochDir ?_
  rintro ⟨x, st⟩ R s0 hp
  dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv,
    epochDirectionMergeSpecOfEnv] at hp ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp
  rcases hp with ⟨hcro, hp⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hw0, hw1, hw2, hlen, hwt, hmsg, ⟨pb, rest, hval, hbs⟩, hFit⟩, hm⟩
  have hDom : tlb_EpochDirDom maxPrev x := ⟨hwt, hmsg, pb, rest, hval, hbs⟩
  have hDom79 : tlb_EpochDirDom 79236 x := by
    rcases hCase with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact tlb_epochDirDom_zero_imp_79236 hDom
    · exact hDom
  refine ⟨(x, st), ?_, fun sf hq => ?_⟩
  · dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hw1, hw2, hlen,
      hFit.mono (fun _ h => e2a_epochDirectionGuarded_imp_tight hCase hDom h)⟩, ?_⟩
    rwa [tlb_domHeap_of_dom hDom79]
  · dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv,
      epochDirectionMergeSpecOfEnv] at hq ⊢
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left
          (Entails.sepExists_mono fun evs =>
            Entails.pure_left fun hev =>
              Entails.pure_right (e2a_epochDirectionGuarded_imp_tight hCase hDom hev)
                (Entails.refl _))))))
      hq

/-- Canonical `V1State::merge` (`Block 298`) envelope projection on `V1State.encodeRaw v1`. -/
theorem e2a_v1StateMerge_tight_of_dom {v1Ops : Nat} {v1 : V1State}
    (hv1 : tlb_ValidV1StatePB v1)
    (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent)
    (h : tlb_V1StateMergeGuardedEnvOf v1Ops
      ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
        e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs) :
    SpqrTightEvs v1Ops 731332 2560 evs :=
  tlb_guardedEnv_tight_of_dom ⟨rfl, rfl, v1, rest3, hv1, rfl⟩ h

/-! ## 3. Canonical Entry Seam & Guarded-Tight Block `325` Producers -/

/-- Canonical entry specification for Block `325` (`+0`) on `encodeState pb` wire inputs. -/
def E2aDecodeStateCanonicalEntryOk [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (v1Ops : Nat) (V1Env : V1StateMergeGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  DecodeStateCalleeContractsClPlacedX H_inner A lim ext →
  E2aEpochDirCanonicalOk A lim ext →
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298)
    (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1Env V1Env)) →
  ∀ {PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop}
    (x : DecodeStateGhost) (pb : PqRatchetState) (st0 : M.σ) (s0 : State) (P R : SepProp)
    (post : State → SepProp → Prop),
    post = decodeStatePostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R →
    (∀ evs, SpqrTightEvs (23 + v1Ops) 1307216 79236 evs → PostEnv x evs) →
    x.st.bytes = encodeState pb →
    spqrDecodeState x.st.bytes = .ok pb →
    (∀ vn, pb.versionNegotiation = some vn → e2a_ValidVersionNegotiationPB vn) →
    (∀ ch, pb.chain = some ch → e2a_ValidChainPB ch) →
    (∀ v1, pb.inner = some (.v1 v1) →
      ∀ (msgPtr bufRef slot ptr : BitVec 64) (rest3 : Bytes) (evs : List AllocEvent),
        V1Env ⟨.lengthDelimited, msgPtr, default, bufRef, slot, ptr,
          e2a_lenPrefixed (V1State.encodeRaw v1) rest3⟩ evs →
        SpqrTightEvs v1Ops 731332 2560 evs) →
    s0.spAligned = true →
    s0.pc = decodeStatePlacedEntry →
    s0.status = .Running →
    s0.readReg64 .x8 = x.outPtr →
    s0.readReg64 .x0 = x.st.v →
    x.st.bytes.length < 2 ^ 32 →
    FitsEnv M lim st0 (SpqrTightEvs (23 + v1Ops) 1307216 79236) →
    P = v1StateJumpTablesPlacedAt ∗ x.st.at A.repAlloc ∗ memRegion x.outPtr 352 ∗
      A.pool lim st0 s0 ∗ stackAt s0.sp decodeStateStackX →
    SepWPpIPlaced (decodeStatePlacedProg ext) (s0.readReg64 .x30) s0 P post
      (decodeStatePanicPostPlacedOfEnv H_inner A lim PreEnv PostEnv (x, st0) s0 R)

/-- Guarded-tight code-loaded Block `325` contract at `23 + v1Ops` from `E2aDecodeStateCanonicalEntryOk`. -/
theorem e2a_decodeState_cl_placed_ok_of_canonical [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {v1Ops : Nat}
    {ext : String → Option (State → State)}
    (hCanon : E2aDecodeStateCanonicalEntryOk H_inner A lim v1Ops
      (tlb_V1StateMergeGuardedEnvOf v1Ops) ext)
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim v1Ops ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops)) ext := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre halign
  change s0.mem ⊨
    ((spqrDecodeStatePlacedSpecOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))).pre (x, st0) s0 ∗
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  dsimp only [spqrDecodeStatePlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hlen_bound, hFit⟩, hm⟩
  by_cases hdom : tlb_DecodeStateDom F K x
  · obtain ⟨pb, hbs, hvn, hch, hv1⟩ := e2a_spqrStateTight640_encode_valid hdom
    have hok : spqrDecodeState x.st.bytes = .ok pb := by
      rw [hbs]
      exact spqrDecodeState_encodeState pb (by rw [← hbs]; omega)
    exact ⟨_, R, hm, @hCanon hc (e2a_epochDirCanonicalOk_of_tlb hEpochDir) hV1Merge
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      x pb st0 s0 _ R _ rfl (fun _ ht => Or.inl ⟨hdom, ht⟩) hbs hok hvn hch
      (fun v1 hv1_eq msgPtr bufRef slot ptr rest3 evs hev =>
        e2a_v1StateMerge_tight_of_dom (hv1 v1 hv1_eq) msgPtr bufRef slot ptr rest3 evs hev)
      halign hpc hrun hx8 hx0 hlen_bound (hFit.mono fun _ ht => Or.inl ⟨hdom, ht⟩) rfl hinv⟩
  · exact ⟨_, R, hm, decodeState_entry_5349c_cl_placed_ofEnv hc x st0 s0 _ R
      (decodeStatePostPlacedOfEnv H_inner A lim
        (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
        (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops)) (x, st0) s0 R)
      rfl (fun _ hf => Or.inr ⟨hdom, hf⟩) halign hpc hrun hx8 hx0 hlen_bound
      (tlb_fitsEnv_fallback_of_not_dom hdom hFit) rfl hinv⟩

/-- Guarded-tight code-loaded Block `325` contract under `tlb_DecodeStateGuardedEnv F K` (`109` ops) from `E2aDecodeStateCanonicalEntryOk`. -/
theorem e2a_decodeState_cl_placed_ok_of_canonical_109 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hCanon : E2aDecodeStateCanonicalEntryOk H_inner A lim 80
      (tlb_V1StateMergeGuardedEnvOf 80) ext)
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80 ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnv F K)
      (tlb_DecodeStateGuardedEnv F K) ext :=
  e2a_decodeStatePlacedOkOfEnv_mono
    (fun _ _ h => tlb_decodeStateGuardedEnv_mono (by decide : 23 + 80 ≤ 109) h)
    (e2a_decodeState_cl_placed_ok_of_canonical hCanon hc hEpochDir hV1Merge)

theorem e2a_decodeState_placed_ok_of_canonical [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {v1Ops : Nat}
    {ext : String → Option (State → State)}
    (hCanon : E2aDecodeStateCanonicalEntryOk H_inner A lim v1Ops
      (tlb_V1StateMergeGuardedEnvOf v1Ops) ext)
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim v1Ops ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops)) ext :=
  e2a_decodeState_cl_placed_ok_of_canonical hCanon
    (e2a_contractsClPlacedX_of_placedX hc) hEpochDir hV1Merge

theorem e2a_decodeState_placed_ok_of_canonical_109 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hCanon : E2aDecodeStateCanonicalEntryOk H_inner A lim 80
      (tlb_V1StateMergeGuardedEnvOf 80) ext)
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80 ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnv F K)
      (tlb_DecodeStateGuardedEnv F K) ext :=
  e2a_decodeState_cl_placed_ok_of_canonical_109 hCanon
    (e2a_contractsClPlacedX_of_placedX hc) hEpochDir hV1Merge

/-! ## 4. Unconditional Block `325` Guarded-Tight Producers -/

/-- Unconditional guarded-tight code-loaded Block `325` (`spqr::decode_state`) contract at `23 + v1Ops`. -/
theorem e2a_decodeState_cl_placed_ok_of_v1Merge [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {v1Ops : Nat}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim v1Ops ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops)) ext :=
  e2a_decodeState_cl_placed_ok_of_canonical e2a_decodeState_entry_canonical_cl_placed
    hc hEpochDir hV1Merge

/-- Unconditional guarded-tight code-loaded Block `325` (`spqr::decode_state`) contract under `tlb_DecodeStateGuardedEnv F K` (`109` ops). -/
theorem e2a_decodeState_cl_placed_ok_of_v1Merge_109 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80 ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnv F K)
      (tlb_DecodeStateGuardedEnv F K) ext :=
  e2a_decodeState_cl_placed_ok_of_canonical_109 e2a_decodeState_entry_canonical_cl_placed
    hc hEpochDir hV1Merge

theorem e2a_decodeState_placed_ok_of_v1Merge [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {v1Ops : Nat}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim v1Ops ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops))
      (tlb_DecodeStateGuardedEnvOf F K (23 + v1Ops)) ext :=
  e2a_decodeState_placed_ok_of_canonical e2a_decodeState_entry_canonical_cl_placed
    hc hEpochDir hV1Merge

theorem e2a_decodeState_placed_ok_of_v1Merge_109 [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext)
    (hEpochDir : tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80 ext) :
    DecodeStatePlacedOkOfEnv H_inner A lim
      (tlb_DecodeStateGuardedEnv F K)
      (tlb_DecodeStateGuardedEnv F K) ext :=
  e2a_decodeState_placed_ok_of_canonical_109 e2a_decodeState_entry_canonical_cl_placed
    hc hEpochDir hV1Merge

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
