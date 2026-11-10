/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncCallPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 5 Aux): Environment Bridges and `SegSignal` Call Seam

Provides `h45_kitF_placed` and `h45_ScopeNone_placed` budget environment bridges
(`EncCalleesTFullBudget`, `EncEnvTFullBudget`, `h45_envF_budget`, `h45_envNone_budget`) and proves
the `OTR::encrypt` call seam `h45_segSignal_enc_to_ret_pf_placed` on Block `464` (`lsProg_464 Hk`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget (
  withStoresEncBudgetSpecVT otrEncryptBudgetSpecQF otrEncryptBudgetSpecQT
  EncCalleesTBudget EncEnvTBudget h45_otrEncryptBudgetOkQ_false
  h45_subroutineOutcome_vt_of_v_placed h45_SegExitVTPlaced
  h45_segExitVT_of_segExit_placed h45_segExitVT_call_sub_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget (
  SegSignalEncStateVPlaced
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget (
  SegSignalRetStateVPlaced
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget (
  segSignal_panic_bridge_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  otrEncryptBudgetSpec otrEncryptBudgetSpecQ PublicApiEncHooksBudget EncCalleesBudget
  withStoresEncBudgetSpecV EncTailVBudget SegExitBudget EncEnvBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  FromCurEnv timeAddBudgetSpec durationSinceBoundedBudgetSpec sessionMemcpyRegionBudgetSpec
  kitLoadShimBudgetSpec kitStoreShimBudgetSpec kitLoadPollBudgetSpecS kitLoadPollBudgetSpecSE
  kitStorePollBudgetSpec kitStorePollBudgetSpecE SessionOnlyKitBudgetOkSE
  CurStateVBudget EncCalleesFullBudget EncEnvFullBudget
  otrFromRawBudgetSpec otrApplyBudgetSpec kyberMapBudgetSpec
  preKeyMsgNewBudgetSpec dropSessionStructureLocal2BudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SeamBudget retagSessionStore retagIdentityStore BoxAllocEnv StringCloneEnv
  SpqrSendBudgetEnv OtrEncryptEnv SessionStoreBudgetEnv IdentityStoreBudgetEnv
  IdentityStoreKitBudgetOkI WithStoresEncEnv FromOtrEnv FromKeyEnv FromCmEnv
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget (
  LoadRemEnv seqEnv3_reassoc
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget (
  tailWriteResult_placed_ok tailWriteErr_placed_ok tailFreePrevSessions_placed_ok
)

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced
  SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced
  SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName
  cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced
  encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym
  lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec
  otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced
  withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed
  withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding
  EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok
  tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok
  tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `h45_kitF_placed` & `Scope` Invariance / Monotonicity Helpers -/

/-- Transport `SessionStoreBudgetEnv` across `h45_kitF_placed` (`rfl` on all poll envelopes). -/
@[reducible] def h45_kitEnvF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit) :
    SessionStoreBudgetEnv (h45_kitF_placed kit) where
  loadPollEnv := kitEnv.loadPollEnv
  storePollEnv := kitEnv.storePollEnv

theorem h45_encTailVBudget_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) :
    EncTailVBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv x st_init st answers pc regs slots R s0 s =
    EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv x st_init st answers pc regs slots R s0 s := by
  have hseam :
      SeamBudget lim
        (WithStoresEncEnv (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0 Scope C S sendEnv parse x)
        st_init st FreeOnlyEvs =
      SeamBudget lim
        (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x)
        st_init st FreeOnlyEvs := rfl
  have henc :
      EncTailVPlaced (retagSessionStore (A' := A.atState lim st s) (h45_kitF_placed kit)) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
        x answers pc regs slots R s0 s =
      EncTailVPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
        x answers pc regs slots R s0 s :=
    h45_encTailV_kitF_placed (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
      x answers pc regs slots R s0 s
  unfold EncTailVBudget
  rw [hseam, henc]

theorem h45_subroutineOutcome_budget_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init : M.σ) (R0 : SepProp) (s0 sf : State) :
    SubroutineOutcome
      (withStoresEncBudgetSpecV A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord)
      (x, st_init) R0 s0 sf =
    SubroutineOutcome
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord)
      (x, st_init) R0 s0 sf := by
  have hpost :
      (withStoresEncBudgetSpecV A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord).post =
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord).post := by
    simp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded, withStoresEncStackV,
      h45_kitF_placed, h45_kitEnvF, h45_storeFinal_kitF_placed, h45_callsRel_kitF_placed, h45_traceOfWith_kitF_placed]
    rfl
  unfold SubroutineOutcome
  rw [hpost]
  rfl

theorem h45_segExitBudget_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (st_init : M.σ) (R0 : SepProp) (s0 s : State)
    (next : State → Prop) :
    SegExitBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next =
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next := by
  simp only [SegExitBudget, h45_subroutineOutcome_budget_kitF_placed]

theorem h45_fromCurEnv_mono {A : RustAlloc}
    {Scope' Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {parse : UuidParser}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost}
    (hmono : ∀ r, Scope' r → Scope r) :
    ∀ evs, FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope' x evs →
      FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope x evs := by
  rintro evs (h1 | ⟨e1, e2, rfl, he1, hfree | ⟨r, sess, otr, taken, ⟨hs, hl⟩, hcur, hfrom, hotr⟩⟩)
  · exact Or.inl h1
  · exact Or.inr ⟨e1, e2, rfl, he1, Or.inl hfree⟩
  · exact Or.inr ⟨e1, e2, rfl, he1, Or.inr ⟨r, sess, otr, taken, ⟨hmono r hs, hl⟩, hcur, hfrom, hotr⟩⟩

theorem h45_withStoresEncEnv_mono {A : RustAlloc}
    {Scope' Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {parse : UuidParser}
    {x : WithStoresEncGhost}
    (hmono : ∀ r, Scope' r → Scope r) :
    ∀ evs, WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope' C S sendEnv parse x evs →
      WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x evs := by
  rintro evs (hpre | ⟨e1, e2, rfl, he1, hfree | hclone | hcur⟩)
  · exact Or.inl hpre
  · exact Or.inr ⟨e1, e2, rfl, he1, Or.inl hfree⟩
  · exact Or.inr ⟨e1, e2, rfl, he1, Or.inr (Or.inl hclone)⟩
  · exact Or.inr ⟨e1, e2, rfl, he1, Or.inr (Or.inr (h45_fromCurEnv_mono hmono e2 hcur))⟩

theorem h45_segExitBudget_scopeMono [LibsignalPlacement] {M : AllocCostModel}
    {Scope' Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {p q : State → Prop}
    (hmono : ∀ r, Scope' r → Scope r)
    (h : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s p)
    (hpq : ∀ sf, p sf → q sf) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s q := by
  intro hL
  obtain ⟨sf, hst, hp | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl (hpq sf hp)⟩
  · refine ⟨sf, hst, Or.inr ?_⟩
    rcases hout with ⟨h1, hcs, hpost⟩ | hpan | hexit | hoom
    · refine Or.inl ⟨h1, hcs, ?_⟩
      dsimp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      apply Entails.sepExists_elim; intro answers
      refine Entails.trans ?_ (Entails.sepExists_intro answers)
      apply Entails.sepExists_elim; intro evs
      refine Entails.trans ?_ (Entails.sepExists_intro evs)
      refine Entails.pure_left fun ⟨hm1, hm2, hm3, hm4, hevs⟩ => ?_
      exact Entails.pure_right ⟨hm1, hm2, hm3, hm4, h45_withStoresEncEnv_mono hmono evs hevs⟩ (Entails.refl _)
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hexit))
    · exact Or.inr (Or.inr (Or.inr hoom))

theorem h45_seamBudget_loadRem_of_prefix {M : AllocCostModel} {A : RustAlloc}
    {lim : BudgetLimits}
    {Scope' Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {parse : UuidParser}
    {x : WithStoresEncGhost} {st_init : M.σ} {evs_shim evs_poll : List AllocEvent}
    (hfit0 : FitsEnv M lim st_init (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x))
    (hevs_shim : BoxAllocEnv kit.loadBoxSize evs_shim)
    (hevs_poll : kitEnv.loadPollEnv st0 x.rem.val evs_poll)
    (hmono : ∀ r, Scope' r → Scope r) :
    SeamBudget lim
      (WithStoresEncEnv (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0 Scope' C S sendEnv parse x)
      st_init
      (M.stepEvents (rustDeallocEvents kit.loadBoxSize 8) (M.stepEvents evs_poll (M.stepEvents evs_shim st_init)))
      (LoadRemEnv C S sendEnv parse (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0 Scope' x) := by
  have hfit0' : FitsEnv M lim st_init
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope' C S sendEnv parse x) :=
    FitsEnv.mono (h45_withStoresEncEnv_mono hmono) hfit0
  have hbud0' :
      SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope' C S sendEnv parse x)
        st_init st_init
        (SeqEnv (BoxAllocEnv kit.loadBoxSize)
          (SeqEnv (kitEnv.loadPollEnv st0 x.rem.val)
            (SeqEnv (· = rustDeallocEvents kit.loadBoxSize 8)
              (LoadRemEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope' x)))) :=
    (SeamBudget.init hfit0').narrow fun evs h => seqEnv3_reassoc evs h
  exact ((hbud0'.advance hevs_shim).advance hevs_poll).advance rfl

theorem h45_curStateVBudget_of_false [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s' : State}
    (h : ∃ st' r g sess,
      CurStateVBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
        (fun _ => False) C ctl parse S sendEnv encRecord x st_init st' r g sess R s0 s') :
    ∃ st' r g sess,
      CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord x st_init st' r g sess R s0 s' := by
  rcases h with ⟨_, _, _, _, _, _, ⟨hfalse, _⟩, _⟩
  exact False.elim hfalse

theorem h45_curStateVBudget_of_scopeNone [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s' : State}
    (h : ∃ st' r g sess,
      CurStateVBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
        (h45_ScopeNone_placed Scope) C ctl parse S sendEnv encRecord x st_init st' r g sess R s0 s') :
    ∃ st' r g sess,
      CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0
        Scope C ctl parse S sendEnv encRecord x st_init st' r g sess R s0 s' := by
  rcases h with ⟨_, r, _, sess, _, hcur, ⟨⟨_, hnone⟩, _⟩, _⟩
  rw [hnone] at hcur
  cases hcur

theorem h45_loadOutRes_some_scopeNone_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} (hcur : r.currentSession = none) :
    LoadOutResPlaced Scope A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ⊢
      LoadOutResPlaced (h45_ScopeNone_placed Scope) A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail := by
  rw [loadOutResPlaced_some_eq, loadOutResPlaced_some_eq]
  apply Entails.sepExists_elim
  intro g
  refine Entails.trans ?_ (Entails.sepExists_intro g)
  refine Entails.pure_left fun ⟨hscope, hrest⟩ => ?_
  exact Entails.pure_right ⟨⟨hscope, hcur⟩, hrest⟩ (Entails.refl _)

/-! ## 2. Full `VT` Budget Environment (`EncCalleesTFullBudget`, `EncEnvTFullBudget`) & `h45_env{F,None}_budget` -/

/-- Full budget-threaded callee bundle extending `EncCalleesTBudget F` with the non-`VT` callees. -/
structure EncCalleesTFullBudget [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop
    extends EncCalleesTBudget F C A lim ctl parse S sendEnv H where
  otrFrom : subroutine_ok (lsProg_464 H) (lsmpl.base 19)
    (StoreKit.withLsRoCl lsmpl (otrFromRawBudgetSpec M A lim))
  otrApply : subroutine_ok (lsProg_464 H) (lsmpl.base 20)
    (StoreKit.withLsRoCl lsmpl (otrApplyBudgetSpec M A lim))
  kyber : subroutine_ok (lsProg_464 H) (lsmpl.base 430)
    (StoreKit.withLsRoCl lsmpl (kyberMapBudgetSpec M A lim))
  psmNew : subroutine_ok (lsProg_464 H) (lsmpl.base 41)
    (StoreKit.withLsRoCl lsmpl (preKeyMsgNewBudgetSpec M A lim))
  dropSs : subroutine_ok (lsProg_464 H) (lsmpl.base 442)
    (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim))

/-- Full budget-threaded `VT` environment extending `EncEnvTBudget F` with session-store kit,
full callees, VM-preserving hook contracts, and `Scope'`-polymorphic error tails
(`tailWriteResult`, `tailWriteErr`, and `tailFreePrevSessions` are discharged automatically). -/
structure EncEnvTFullBudget [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop
    extends EncEnvTBudget F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H where
  kitOk : SessionOnlyKitBudgetOkSE A lim kit kitEnv Scope encRecord H
  calleesFull : EncCalleesTFullBudget F C A lim ctl parse S sendEnv H
  timeAddVm : HookSat H CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddBudgetSpec)
  durationSinceVm : HookSat H CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsDurationSinceSym
    (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
      durationSinceBoundedBudgetSpec)
  memcpyVm : HookSat H CryptoVerification.lsMemcpySym sessionMemcpyRegionBudgetSpec
  tailDropRecord :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailSignalEncryptErr :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xc14#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0xb00 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailCmDrop :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (m : CiphertextMessage),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailStoreHookErr :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (m : CiphertextMessage) (pcOff src : Nat),
        ((pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
          (pcOff, src) = (0xf2c, 0x9b0)) →
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + BitVec.ofNat 64 pcOff) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
            (pollWith sp src [w3, w4, w5]) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)
  tailFromSessionStateErr :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (g : RecordGhost)
      (rec : SessionRecord (List (BitVec 8))),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
      SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
        (encEntryPlaced + 0x49c#64)
        (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
          s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
        (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ Hp) R s0 s →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
        x st_init R s0 s (fun _ => False)
  tailPreKeyEncryptErr :
    ∀ {Scope' : SessionRecord (List (BitVec 8)) → Prop}
      (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
      (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
      (scratch = curScratch ∨ scratch = cmScratch) →
      ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
        (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
        (kyPtr : BitVec 64) (kp : Option KyberPayload),
        TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
        SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv x st_init st answers
          (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
              (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
                memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
                memRegion (sp + 0xb18#64) 0x68) ∗ Hp) R s0 s →
        SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord H
          x st_init R s0 s (fun _ => False)

private theorem h45_kitOkF_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (hkit : SessionOnlyKitBudgetOkSE A lim kit kitEnv Scope encRecord H) :
    SessionOnlyKitBudgetOkSE A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) Scope' encRecord H where
  loadShim := hkit.loadShim
  loadPoll := by
    intro callerProg callerBlk _ hblk
    refine Arm64.subroutine_ok_outcome_intro fun ⟨x, self, st0, st⟩ R s0 _ _ hpre _ => ?_
    have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
    obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
    dsimp only [kitLoadPollBudgetSpecS, h45_kitF_placed, h45_kitEnvF] at hp2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
    exact False.elim hp2.1.2.2.1
  loadFutDrop := hkit.loadFutDrop
  storeShim := hkit.storeShim
  storePoll := by
    intro callerProg callerBlk _ hblk
    refine Arm64.subroutine_ok_outcome_intro fun ⟨x, self, st0, st⟩ R s0 _ _ hpre _ => ?_
    have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
    obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
    dsimp only [kitStorePollBudgetSpec, h45_kitF_placed, h45_kitEnvF] at hp2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
    exact False.elim hp2.1.2.2.2.1
  storeFutDrop := hkit.storeFutDrop

private theorem h45_envBase_budget [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTFullBudget F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H)
    (hscopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      (h45_kitF_placed kit).ScopeAt Scope' st0 rem r → RecordInScopeEnc r)
    (hscopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
      (h45_kitF_placed kit).ScopeAt Scope' st0 rem r → r.currentSession = some s → False)
    (hrecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      StepsThroughEncrypt ((h45_kitF_placed kit).ScopeAt Scope' st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' →
      (h45_kitF_placed kit).RecOk (storedRecord sess otr' taken)) :
    EncEnvFullBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
      Scope' (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H := by
  let base : EncEnvBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
      Scope' (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H := {
    hooks := hEnv.hooks
    ikitOk := hEnv.ikitOk
    callees := {
      remoteIk := hEnv.callees.remoteIk
      otrEnc := h45_otrEncryptBudgetOkQ_false
      unack := hEnv.callees.unack
    }
    vtables := {
      loadSlot := hEnv.vtables.loadSlot
      storeSlot := hEnv.vtables.storeSlot
      loadFutDrop := hEnv.vtables.loadFutDrop
      loadFutSize := hEnv.vtables.loadFutSize
      loadFutAlign := hEnv.vtables.loadFutAlign
      loadFutPoll := hEnv.vtables.loadFutPoll
      storeFutDrop := hEnv.vtables.storeFutDrop
      storeFutSize := hEnv.vtables.storeFutSize
      storeFutAlign := hEnv.vtables.storeFutAlign
      storeFutPoll := hEnv.vtables.storeFutPoll
    }
    idVtables := hEnv.idVtables
    scopeIn := hscopeIn
    scopeQ := hscopeQ
    recOk := hrecOk
    tailDropRecord := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailDropRecord x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot hm hst hs
    tailSignalEncryptErr := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailSignalEncryptErr x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot hm hst hs
    tailCmDrop := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot m hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailCmDrop x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot m hm hst hs
    tailStoreHookErr := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot m pcOff src hpc hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailStoreHookErr x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot m pcOff src hpc hm hst hs
  }
  exact {
    toEncEnvBudget := base
    kitOk := h45_kitOkF_budget hEnv.kitOk
    calleesFull := {
      toEncCalleesBudget := base.callees
      otrFrom := hEnv.calleesFull.otrFrom
      otrApply := hEnv.calleesFull.otrApply
      kyber := hEnv.calleesFull.kyber
      psmNew := hEnv.calleesFull.psmNew
      dropSs := hEnv.calleesFull.dropSs
    }
    timeAddVm := hEnv.timeAddVm
    durationSinceVm := hEnv.durationSinceVm
    memcpyVm := hEnv.memcpyVm
    tailWriteResult := fun x st_init st R s0 s ans res w0 w1 w2 w3 bs Hp hm hst hs =>
      tailWriteResult_placed_ok x st_init st R s0 s ans res w0 w1 w2 w3 bs Hp hm hst hs
    tailWriteErr := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp hm hst hs =>
      tailWriteErr_placed_ok x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp hm hst hs
    tailFreePrevSessions := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp prevCap prevPtr hm hst hs =>
      tailFreePrevSessions_placed_ok base x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp prevCap prevPtr hm hst hs
    tailFromSessionStateErr := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp g rec hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailFromSessionStateErr x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp g rec hm hst hs
    tailPreKeyEncryptErr := fun x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot kyPtr kp hm hst hs => by
      rw [h45_tailModel_kitF_placed] at hm
      rw [h45_encTailVBudget_kitF_placed] at hs
      rw [h45_segExitBudget_kitF_placed]
      exact hEnv.tailPreKeyEncryptErr x st_init st R s0 s ans e w0 w1 w2 w3 w4 w5 Hp scr hscr g rec ot kyPtr kp hm hst hs
  }

theorem h45_envF_budget [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTFullBudget F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H) :
    EncEnvFullBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
      (fun _ => False) (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H :=
  h45_envBase_budget hEnv
    (fun _ h => False.elim h.1)
    (fun _ _ h _ => False.elim h.1)
    (fun h => False.elim h.2.1.1)

theorem h45_envNone_budget [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTFullBudget F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H) :
    EncEnvFullBudget A lim (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
      (h45_ScopeNone_placed Scope) (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H :=
  h45_envBase_budget hEnv
    (fun r h => hEnv.scopeIn r ⟨h.1.1, h.2⟩)
    (fun _ _ h hs => by rw [h.1.2] at hs; cases hs)
    (fun h => by have hnone := h.2.1.1.2; rw [h.1] at hnone; cases hnone)

/-! ## 3. `SegSignal` `VT` Call Seam (`h45_segSignal_enc_to_ret_pf_placed`) -/

private def h45_segSignalEncCallFramePlaced {ss_vt id_vt : BitVec 64} (A : RustAlloc)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
  memRegion x.ret 248 ∗
  protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

set_option maxHeartbeats 800000 in
private theorem h45_segSignal_enc_pre_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    {M : AllocCostModel} (F0 : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x)))
    (hQ : otr.pqrState.length < 2 ^ 32) (h64 : 64 ≤ x.rest.length)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = sp + 0x580#64) (hx1 : s.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s.readReg64 .x2 = x.ptA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hx4 : s.readReg64 .x4 = 0#64) (hx5 : s.readReg64 .x5 = x.remA)
    (hpt : x.ptext.length < 2 ^ 32) (hrest : x.rest.length < 2 ^ 63)
    (hm : s.mem ⊨
      (takenSlots (A.atState lim st s) sp sess taken ∗
        otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗ (F0 ∗ R)) :
    ∃ g : RecordGhost,
      s.mem ⊨ (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).pre
          (segSignalEncGhost sp pqCap pqPtr otr x, st) s ∗
        (h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R) := by
  unfold takenSlots encCommonPlaced at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  refine ⟨g, ?_⟩
  rw [show sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc from rfl,
    show protocolAddressAt (A.atState lim st s) x.loc x.locA = protocolAddressAt A.repAlloc x.loc x.locA from rfl] at hm
  have htape := cliTapeAfter_zero_entails_cliTapeAt ctl x.cur x.rest hrest
  have hm_rearr : s.mem ⊨
      cliTapeAfter ctl x.cur x.rest 0 ∗
      (F0 ∗ otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗
        (A.atState lim st s).pool ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R) := by
    unfold h45_segSignalEncCallFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  have hx3_nat : (s.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQT otrEncryptBudgetSpecQF
  dsimp only
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hfit, ?_⟩
  unfold otrEncryptPlacedSpecQF otrEncryptPlacedSpec segSignalEncGhost optAddrAt
  dsimp only
  rw [hsp, emp_sepConj]
  have hgoal : s.mem ⊨
      (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ : SepProp) ∗
      ⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
      ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
        s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
        ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
        s.readReg64 .x5 = x.remA⌝ ∗
      (cliTapeAt ctl x.cur x.rest ∗
        (F0 ∗ otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt (A.atState lim st s) x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗
          (A.atState lim st s).pool ∗
          h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0 ∗ R)) := by
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcrl, ⟨hQ, h64⟩, ⟨hx0, hx1, hx2, hx3_nat, hpt, hx4, (by intro h; cases h), hx5⟩, hm_tape⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hgoal

set_option maxHeartbeats 800000 in
private theorem h45_segSignal_enc_post_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    {M : AllocCostModel} (F0 : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st : M.σ) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s sm : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hpost : sm.mem ⊨
      ((StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).post
          (segSignalEncGhost sp pqCap pqPtr otr x, st) s sm ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :
    ∃ evs : List AllocEvent,
      OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x) evs ∧
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem ∧
      (segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace ∧
      (sm.mem ⊨
        (sessionRecordAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x110#64) g (takenRecord sess taken) ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
            otrAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        (memRegion (sp + 0x46a#64) 0x116 ∗
          signalMessageResultAt (A.atState lim (M.stepEvents evs st) sm) (utf8 "encrypt") (sp + 0x580#64)
            (segSignalRes C S x otr).1 ∗
          memRegion (sp + 0x5f8#64) 0x588) ∗
        memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim (M.stepEvents evs st) sm) ctl x (S.draws otr.pqrState x.rest) s0 ∗
        (F0 ∗ R)) := by
  unfold StoreKit.withLsRoCl otrEncryptBudgetSpecQT otrEncryptBudgetSpecQF otrEncryptPlacedSpecQF at hpost
  dsimp only at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨evs, hpost⟩ := hpost
  let A' := A.atState lim (M.stepEvents evs st) sm
  have h0 : sm.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
      ⌜OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x) evs⌝ ∗
      ((F0 ∗ (otrEncryptPlacedSpec C A' ctl uuidTryParse S).post
          (segSignalEncGhost sp pqCap pqPtr otr x) s sm ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h0
  rcases h0 with ⟨hcrlm, hevs, hpost⟩
  refine ⟨evs, hevs, hcrlm, ?_⟩
  unfold otrEncryptPlacedSpec at hpost
  dsimp only at hpost
  rw [segSignalEncGhost_model, hsp] at hpost
  unfold segSignalEncGhost optAddrAt at hpost
  dsimp only at hpost
  rw [emp_sepConj] at hpost
  have h1 : sm.mem ⊨
      ⌜(segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace⌝ ∗
      ((F0 ∗ (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A' (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.rem x.remA ∗
        cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A'.pool ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A.repAlloc x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨hne, htr, ?_⟩
  unfold h45_segSignalEncCallFramePlaced at hmem
  rw [show sessionRecordAt A.repAlloc = sessionRecordAt A' from rfl,
    show protocolAddressAt A.repAlloc x.loc x.locA = protocolAddressAt A' x.loc x.locA from rfl] at hmem
  have hmem_rearr : sm.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
        stackAt sp rootStack) ∗
      (sessionRecordAt A' (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A' (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A' (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A' x.rem x.remA ∗ protocolAddressAt A' x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ encSavedRegs s0.sp s0 ∗ A'.pool ∗ (F0 ∗ R)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack rootStack] at hmem_rearr
  unfold encCommonPlaced
  rw [hsp0]
  exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem_rearr

theorem h45_q_otr_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    otr.pqrState.length < 2 ^ 32 :=
  fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hsc hcur

/-- **Enc → Ret** (`bl OTR::encrypt` returns to `+0x3a4`) under `withStoresEncBudgetSpecVT F0`:
calls `hEnv.callees.otrEnc` (`otrEncryptBudgetSpecQT F0`), advances `SeamBudget` across `evs`,
and frames `F0` into `SegSignalRetStateVPlaced`. -/
theorem h45_segSignal_enc_to_ret_pf_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hs : SegSignalEncStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R_frame) s0 s) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R_frame s0 s
      (fun s' => ∃ st',
        SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
          x st_init st' r sess otr taken k (F0 ∗ R_frame) s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R_frame
  rcases hs with ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hbud_seq : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x))
        (fun evs' =>
          FreeOnlyEvs evs' ∨
          FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess (segSignalRes C S x otr).2 taken k evs')) :=
    hbud.narrow fun _ hseq => Or.inl ⟨hnone, hseq⟩
  have hfit : FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidTryParse (segSignalEncGhost sp pqCap pqPtr otr x)) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_seq.1
  have hQ : otr.pqrState.length < 2 ^ 32 := h45_q_otr_placed hEnv hcur hsc hfrom
  have hm' : s.mem ⊨
      (takenSlots (A.atState lim st s) sp sess taken ∗
        otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗ (F0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm
  obtain ⟨g, hm_pre⟩ := h45_segSignal_enc_pre_unpack F0 C A lim ctl S sendEnv x st sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp hfit hQ h64 hcrl hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm'
  refine h45_segExitVT_call_sub_placed hEnv.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x, st)
    hs_pc hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQT F0 C A lim ctl uuidTryParse S sendEnv)).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x, st) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      segSignal_panic_bridge_placed (Q := fun _ => True) hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm _hL1 _hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := spAligned_of_sp_eq hal hsm_sp
  obtain ⟨evs, hevs, hcrlm, hne, hsm_tr, hm_ret⟩ :=
    h45_segSignal_enc_post_pack F0 C A lim ctl S sendEnv x st g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  have hm_ret' : sm.mem ⊨
      (sessionRecordAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt (A.atState lim (M.stepEvents evs st) sm) (sp + 0x288#64) pqCap' pqPtr'
            (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt (A.atState lim (M.stepEvents evs st) sm) (utf8 "encrypt") (sp + 0x580#64)
          (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim (M.stepEvents evs st) sm) ctl x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ (F0 ∗ R_frame)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm_ret
  exact h45_segExitVT_of_segExit_placed (SegExitBudget.next
    ⟨M.stepEvents evs st, hbud_seq.advance hevs, hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
      ⟨hsm_run, hsm_sp', hal0, hsm_al,
        (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29,
        (hcsm.1).trans hx19,
        hcrlm,
        (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs⟩,
      hsm_tr.trans htr,
      (hcsm.2.1).trans hx20,
      (hcsm.2.2.2.2.2.2.1).trans hx25,
      (hcsm.2.2.2.2.2.2.2.1).trans hx26,
      (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28,
      hpt, hrest, hloc, hnow, hstk, g, hm_ret'⟩)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux
