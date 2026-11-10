/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `WithStoresVTPlacedBudget`: Top-Level Composition

Assembles all nine `VT` segment theorems into `withStores_placed_okVT_fs`,
`withStores_placed_okVT`, and the disjunctive CLI encrypt contracts `withStores_placed_okVT_fs_cli_F0`
and `withStores_placed_okVT_fs_cli` (`64 ≤ x.rest.length ∨ RecordPqEmpty`) on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto IdentityKey OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage Session SessionRecord StoreAnswers StoreCall)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (EncFsCtxPlaced encEntryPlaced)
open CryptoVerification.Cli.LibsignalTripleRatchet (otrEncryptName)
open CryptoVerification.E2E.Record (RecordPqEmpty)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (RecordInScopeEnc StepsThroughEncrypt WithStoresEncGhost storedRecord withStoresEncStackV)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsCtx IdentityVtablesPlacedOk KitFsOk LibsignalCodeRoLoaded SessionOnlyVtablesPlacedOk
   SessionStoreSpec extract_withLsRoCl reaches_outcome_withEnvPre subroutine_ok_of_withEnvPre
   withEnvPre withEnvPre_pre_elim withEnvPre_pre_intro withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser protocolAddressAt uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitLoadPollPlacedSpecS
   kitLoadPollPlacedSpecSE kitStorePollPlacedSpec kitStorePollPlacedSpecE)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromOtrEnv SpqrSendBudgetEnv WithStoresEncEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (CmStateVPlaced EncCalleesPlaced EncEnvPlaced PublicApiEncHooksPlaced
   otrEncryptPlacedSpecQ toTempTwinsIkitEnv toTempTwinsKitEnv
   withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget
  (withStores_placed_okV_fs)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (EncCalleesTPlaced EncEnvTPlaced EncTailsVTPlaced otrEncryptPlacedSpecQT
   withStoresEncPlacedSpecVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget
  (h45_SegExitVTPlaced h45_segExitVT_of_segExit_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1
  (h45_segIdentity_placed_okVT h45_segLoad_placed_okVT h45_segSignal_placed_okVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
  (h45_segFrom_placed_okVT h45_segTrust_placed_okVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
  (h45_segPreKey_placed_okVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
  (h45_segFinish_placed_okVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
  (h45_segSave_placed_okVT)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3PlacedBudget
  (h45_segApplyStore_placed_okVT)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (withStoresEncPlacedSpecVT_cli withStoresEncPlacedSpecVT_cli_F0)

export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (withStoresEncPlacedSpecVT otrEncryptPlacedSpecQT EncCalleesTPlaced EncEnvTPlaced
   EncTailsVTPlaced)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1
  (h45_segLoad_placed_okVT h45_segIdentity_placed_okVT h45_segSignal_placed_okVT)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
  (h45_segFrom_placed_okVT h45_segTrust_placed_okVT)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux
  (h45_segPreKey_placed_okVT)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
  (h45_segSave_placed_okVT)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
  (h45_segFinish_placed_okVT)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3PlacedBudget
  (h45_segApplyStore_placed_okVT)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (withStoresEncPlacedSpecVT_cli_F0 withStoresEncPlacedSpecVT_cli)

/-! ## 1. Segment Chaining & `withStores_placed_okVT_fs` -/

private theorem h45_segExitVT_chain_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : h45_SegExitVTPlaced F0 A lim kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_464 Hk)
      (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s') :
    reaches_outcome (lsProg_464 Hk)
      (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

private theorem h45_segExitVT_chainFs_placed [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (h1 : h45_SegExitVTPlaced F0 A lim kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s next)
    (h2 : ∀ s', EncFsCtxPlaced kit ikit Hk s0 s' → next s' →
      reaches_outcome (lsProg_464 Hk)
        (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord)
        (x, st_init) R s0 s') :
    reaches_outcome (lsProg_464 Hk)
      (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- Budget-threaded, frame-generalised `withStores_placed_okV_fs` with `64 ≤ x.rest.length` and
`F0` framed, carrying both kits' `envOk` from `KitFsOk`. -/
theorem withStores_placed_okVT_fs [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 Hk)) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withEnvPre
        (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine subroutine_ok_outcome_intro fun (x, st_init) R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpre_rearr : s0.mem ⊨ ⌜64 ≤ x.rest.length⌝ ∗
      ((withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ (F0 ∗ R)) := by
    change s0.mem ⊨ (⌜64 ≤ x.rest.length⌝ ∗ F0 ∗
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_rearr
  rcases hpre_rearr with ⟨h64, hpreV⟩
  have ⟨haddr_ss, haddr_id⟩ := withStoresEncPlacedSpecV_pre_addrOk hpreV
  have hfs0 : EncFsCtxPlaced kit ikit Hk s0 s0 := FsCtx.of_entry hKitFs h0
  refine h45_segExitVT_chainFs_placed hfs0
    (h45_segExitVT_of_segExit_placed
      (h45_segLoad_placed_okVT hEnv hTails x st_init (F0 ∗ R) s0 hfs0 hpc hrun hal hpreV)) ?_
  rintro s hfs ⟨st1, r, g, sess, hCur⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed
      (h45_segFrom_placed_okVT hEnv (@hTails kit kitEnv st0 Scope)
        x st_init st1 r g sess (F0 ∗ R) s0 s hCur)) ?_
  rintro s hfs ⟨st2, otr, taken, pqCap, pqPtr, hOtr⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed
      (h45_segIdentity_placed_okVT hEnv x st_init st2 r sess otr taken pqCap pqPtr (F0 ∗ R) s0 s
        hOtr)) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : h45_SegExitVTPlaced F0 A lim kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R) s0 s') := by
    cases hp : sess.pendingPreKey with
    | none =>
      exact h45_segSignal_placed_okVT hEnv hTails x st_init st2 r sess otr taken pqCap pqPtr k R
        s0 s h64 hp hKey
    | some _ =>
      exact h45_segPreKey_placed_okVT hEnv hTails x st_init st2 r sess otr taken pqCap pqPtr k R
        s0 s h64 (by simp [hp]) hKey
  refine h45_segExitVT_chainFs_placed hfs hCm ?_
  rintro s hfs ⟨st3, m, otr', pqCap', pqPtr', hCmS⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed
      (h45_segTrust_placed_okVT hEnv hTails x st_init st3 r sess otr taken k m otr' pqCap' pqPtr'
        (F0 ∗ R) s0 s haddr_id hfs hCmS)) ?_
  rintro s hfs ⟨st4, hSave⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed
      (h45_segSave_placed_okVT hEnv hTails x st_init st4 r sess otr taken k m otr' pqCap' pqPtr'
        (F0 ∗ R) s0 s haddr_id hfs hSave)) ?_
  rintro s hfs ⟨st5, c, hApply⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed
      (h45_segApplyStore_placed_okVT hEnv hTails x st_init st5 r sess otr taken k m otr' pqCap'
        pqPtr' c (F0 ∗ R) s0 s haddr_ss hfs hApply)) ?_
  rintro s _ ⟨st6, hStored⟩
  exact h45_segExitVT_chain_placed
    (h45_segExitVT_of_segExit_placed
      (h45_segFinish_placed_okVT hEnv hTails x st_init st6 r sess otr taken k m otr' c (F0 ∗ R)
        s0 s hStored))
    (fun _ hF => False.elim hF)

/-- Corollary of `withStores_placed_okVT_fs` when `envOk` holds trivially. -/
theorem withStores_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord) :=
  subroutine_ok_of_withEnvPre (withStores_placed_okVT_fs hEnv hTails (.inl htriv))
    fun s => htriv s.fs.files

/-! ## 2. Remote-Address Kit Restriction (`h45_kitAt_placed`) & Disjunctive CLI Spec -/

@[reducible] private def h45_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) : SessionStoreSpec A b :=
  { kit with
    addrOk := fun rem => kit.addrOk rem ∧ rem = target
    loadRel := fun st rem ans => kit.loadRel st rem ans ∧ rem = target }

@[reducible] private def h45_kitAtBudget {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} (kitEnv : SessionStoreBudgetEnv kit) (target : AddrVal) :
    SessionStoreBudgetEnv (h45_kitAt_placed kit target) where
  loadPollEnv := kitEnv.loadPollEnv
  storePollEnv := kitEnv.storePollEnv

private theorem h45_pure_mono_placed {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ : SepProp) ⊢ ⌜ψ⌝ :=
  Entails.pure_left_only fun hφ => Entails.pure_right_only (h hφ) (Entails.refl _)

private theorem h45_scopeAt_kitAt_self {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (st0 : kit.StoreState) (rem : AddrVal) :
    (h45_kitAt_placed kit rem).ScopeAt Scope st0 rem = kit.ScopeAt Scope st0 rem := by
  funext r
  exact propext ⟨fun ⟨hs, hl, _⟩ => ⟨hs, hl⟩, fun ⟨hs, hl⟩ => ⟨hs, hl, rfl⟩⟩

private theorem h45_withStoresEncEnv_kitAt_self {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (parse : UuidParser)
    (x : WithStoresEncGhost) :
    WithStoresEncEnv (h45_kitAt_placed kit x.rem.val)
      (toTempTwinsKitEnv (h45_kitAtBudget kitEnv x.rem.val)) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x =
    WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x := by
  have hfr :
      FromOtrEnv C S sendEnv parse (h45_kitAt_placed kit x.rem.val)
        (toTempTwinsKitEnv (h45_kitAtBudget kitEnv x.rem.val)) st0
        ikit (toTempTwinsIkitEnv ikitEnv) ist0 x =
      FromOtrEnv C S sendEnv parse kit (toTempTwinsKitEnv kitEnv) st0
        ikit (toTempTwinsIkitEnv ikitEnv) ist0 x := rfl
  unfold WithStoresEncEnv
  rw [h45_scopeAt_kitAt_self kit Scope st0 x.rem.val, hfr]

private theorem h45_storeFinal_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt_placed kit target).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitAt_placed, ih]

private theorem h45_traceOfWith_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitAt_placed kit target) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls := rfl

private theorem h45_stackV_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b) :
    withStoresEncStackV (h45_kitAt_placed kit target) ikit = withStoresEncStackV kit ikit := rfl

private theorem h45_callsRel_kitAt_imp_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt_placed kit target).callsRel st0 ans calls → kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => exact id
  | cons c cs ih =>
    cases c with
    | loadSession rem => intro ⟨⟨hl, _⟩, hcs⟩; exact ⟨hl, ih st0 hcs⟩
    | isTrustedIdentity _ _ _ => intro hcs; exact ih st0 hcs
    | saveIdentity _ _ => intro hcs; exact ih st0 hcs
    | storeSession rem r' => intro ⟨hs, hcs⟩; exact ⟨hs, ih st0 hcs⟩

private theorem h45_stepsThroughEncrypt_mono_placed
    {Scope1 Scope2 : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (himp : ∀ r', Scope1 r' → Scope2 r')
    (h : StepsThroughEncrypt Scope1 C S parse x r sess otr taken k m otr') :
    StepsThroughEncrypt Scope2 C S parse x r sess otr taken k m otr' :=
  ⟨h.1, himp r h.2.1, h.2.2⟩

private theorem h45_sessionOnlyKitPlacedOkSE_kitAt [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (target : AddrVal)
    (hKitOk : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord Hk) :
    SessionOnlyKitPlacedOkSE A lim (h45_kitAt_placed kit target) (h45_kitAtBudget kitEnv target)
      Scope encRecord Hk where
  loadShim := hKitOk.loadShim
  loadFutDrop := hKitOk.loadFutDrop
  storeShim := hKitOk.storeShim
  storeFutDrop := hKitOk.storeFutDrop
  loadPoll := by
    intro callerProg callerBlk _hcaller hblk
    refine subroutine_ok_outcome_intro fun ⟨c, self, st0', st⟩ R s0 hpc hrun hpre0 hal => ?_
    have ⟨hcrl0, hp1⟩ := extract_withLsRoCl hpre0
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hp1
    have hpre_pure : s0.mem ⊨
        ⌜s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧
          (kit.addrOk c.addr.val ∧ c.addr.val = target) ∧
          LibsignalBinary.Heap.FitsEnv M lim st (kitEnv.loadPollEnv st0' c.addr.val)⌝ ∗
        (kit.loadBoxAt c.fut self c.addrA 0#8 ∗ kit.storeAt self st0' ∗ memRegion c.out 368 ∗
          protocolAddressAt A.repAlloc c.addr c.addrA ∗ A.pool lim st s0 ∗
          stackAt s0.sp kit.loadPollStack ∗ R) := by
      simpa only [kitLoadPollPlacedSpecS, h45_kitAt_placed, h45_kitAtBudget, sepConj_assoc]
        using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hx0, hx8, ⟨haddr, hrem⟩, hfit⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        (withLsRoCl lsmpl (kitLoadPollPlacedSpecSE M A lim kit kitEnv Scope encRecord)).pre
          (c, self, st0', st) s0 ∗ R := by
      dsimp only [withLsRoCl]
      rw [sepConj_comm _ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcrl0, withEnvPre_pre_intro henv ?_⟩
      dsimp only [kitLoadPollPlacedSpecS]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8, haddr, hfit⟩, by simpa only [sepConj_assoc] using hmem⟩
    refine subroutine_ok.mono_outcome
      (hKitOk.loadPoll (callerProg := callerProg) (callerBlk := callerBlk) hblk)
      (c, self, st0', st) R s0 hpc hrun hpre_kit hal (fun sf hout => ?_)
    rcases hout with ⟨hret, hcs, hpost⟩ | hpan | hexit | hoom
    · refine Or.inl ⟨hret, hcs, ?_⟩
      dsimp only [withLsRoCl, withEnvPre, kitLoadPollPlacedSpecS, h45_kitAt_placed,
        h45_kitAtBudget] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_elim fun ans => Entails.sepExists_right ans
          (Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_)))) hpost
      exact sepConj_mono_left (h45_pure_mono_placed fun ⟨hl, htr, hev⟩ => ⟨⟨hl, hrem⟩, htr, hev⟩)
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hexit))
    · exact Or.inr (Or.inr (Or.inr hoom))
  storePoll := by
    intro callerProg callerBlk _hcaller hblk
    refine subroutine_ok_outcome_intro fun ⟨c, self, st0', st⟩ R s0 hpc hrun hpre0 hal => ?_
    have ⟨hcrl0, hp1⟩ := extract_withLsRoCl hpre0
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hp1
    have hpre_pure : s0.mem ⊨
        ⌜s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧ kit.RecOk c.call.record ∧
          (kit.addrOk c.call.addr.val ∧ c.call.addr.val = target) ∧
          LibsignalBinary.Heap.FitsEnv M lim st
            (kitEnv.storePollEnv st0' c.call.addr.val c.call.record)⌝ ∗
        (kit.storeBoxAt c.fut self c.call.addrA c.call.recA 0#8 ∗ kit.storeAt self st0' ∗
          memRegion c.out 48 ∗ protocolAddressAt A.repAlloc c.call.addr c.call.addrA ∗
          sessionRecordAt A.repAlloc c.call.recA c.call.g c.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
      simpa only [kitStorePollPlacedSpec, h45_kitAt_placed, h45_kitAtBudget, sepConj_assoc]
        using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hx0, hx8, hrec, ⟨haddr, _⟩, hfit⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        (withLsRoCl lsmpl (kitStorePollPlacedSpecE M A lim kit kitEnv encRecord)).pre
          (c, self, st0', st) s0 ∗ R := by
      dsimp only [withLsRoCl]
      rw [sepConj_comm _ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcrl0, withEnvPre_pre_intro henv ?_⟩
      dsimp only [kitStorePollPlacedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, by simpa only [sepConj_assoc] using hmem⟩
    exact subroutine_ok.mono_outcome
      (hKitOk.storePoll (callerProg := callerProg) (callerBlk := callerBlk) hblk)
      (c, self, st0', st) R s0 hpc hrun hpre_kit hal (fun _ hout => hout)

private theorem h45_subroutineOutcome_cli_of_kitAt_placed [LibsignalPlacement]
    {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV A lim (h45_kitAt_placed kit x.rem.val)
        (h45_kitAtBudget kitEnv x.rem.val) st0 ikit ikitEnv ist0 Scope
        C ctl uuidParse S sendEnv encRecord)
      (x, st_init) (F0 ∗ R) s0 sf) :
    SubroutineOutcome
      (withStoresEncPlacedSpecVT_cli_F0 F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidParse S sendEnv encRecord)
      (x, st_init) R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecVT_cli_F0]
    have hrearr :
        (F0 ∗
          (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
            C ctl uuidParse S sendEnv encRecord).post (x, st_init) s0 sf) ∗ R =
        (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidParse S sendEnv encRecord).post (x, st_init) s0 sf ∗ (F0 ∗ R) := by sep_ac_rfl
    rw [hrearr]
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded]
    refine Entails.sepExists_elim fun answers => Entails.sepExists_right answers
      (Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_)
    rw [h45_traceOfWith_kitAt_placed kit x.rem.val, h45_storeFinal_kitAt_placed kit x.rem.val,
      h45_stackV_kitAt_placed kit x.rem.val,
      h45_withStoresEncEnv_kitAt_self kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv
        uuidParse x]
    exact sepConj_mono_left (h45_pure_mono_placed fun ⟨hnp, hcalls, hid, htr, hev⟩ =>
      ⟨hnp, h45_callsRel_kitAt_imp_placed kit x.rem.val st0 answers _ hcalls, hid, htr, hev⟩)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncPlacedSpecVT_cli_F0, withStoresEncPlacedSpecV, withLsCodeRoLoaded,
      h45_kitAt_placed] at honp ⊢
    have hmono1 :
        ⌜s0.trace <+: sf.trace ∧
          ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            (kit.loadRel st0 x.rem.val answers.loadSession ∧ x.rem.val = x.rem.val) ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers)⌝ ⊢
        ⌜s0.trace <+: sf.trace ∧
          ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            kit.loadRel st0 x.rem.val answers.loadSession ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers)⌝ :=
      h45_pure_mono_placed fun ⟨htr, ans, ⟨hl, _⟩, hpfx, herr⟩ => ⟨htr, ans, hl, hpfx, herr⟩
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc _ anyHeap F0]
    exact sepConj_mono_left (sepConj_mono hmono1 (entails_anyHeap (anyHeap ∗ F0)))
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

/-- **Budget-threaded relocatable CLI disjunctive `_with_stores` encrypt (`_fs`, general `F0`)**
on `lsProg_464 Hk`. -/
theorem withStores_placed_okVT_fs_cli_F0 [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hhooks : PublicApiEncHooksPlaced A lim Hk)
    (hKitOk : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord Hk)
    (hIkitOk : IdentityStoreKitPlacedOkI A lim ikit ikitEnv Hk)
    (hOtrT : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A lim ctl uuidTryParse S sendEnv)))
    (hOtrEmpty : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQ (· = []) C A lim ctl uuidTryParse S sendEnv)))
    (hVtables : SessionOnlyVtablesPlacedOk kit) (hIdVtables : IdentityVtablesPlacedOk ikit)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 Hk))
    (hScopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hScopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8)))
      (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
      s.state.pqRatchetState.length < 2 ^ 32)
    (hRecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse
        x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken))
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli_F0 F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) := by
  refine subroutine_ok_outcome_intro fun (x, st_init) R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpre_disj : s0.mem ⊨
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → RecordPqEmpty r)⌝ ∗
      ((F0 ∗
        (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0) ∗ R) := by
    change s0.mem ⊨
      (⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → RecordPqEmpty r)⌝ ∗ F0 ∗
        (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_disj
  rcases hpre_disj with ⟨h64 | hpqE, hpre_tok⟩
  · have hEnvT : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord Hk :=
      { hooks := hhooks
        kitOk := hKitOk
        ikitOk := hIkitOk
        callees := EncCalleesTPlaced.of_otrEnc hhooks hOtrT
        vtables := hVtables
        idVtables := hIdVtables
        scopeIn := hScopeIn
        scopeQ := hScopeQ
        recOk := hRecOk }
    have hpreVT : s0.mem ⊨
        (withStoresEncPlacedSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ R := by
      dsimp only [withStoresEncPlacedSpecVT]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨h64, by simpa only [sepConj_assoc] using hpre_tok⟩
    exact subroutine_ok.mono_outcome (withStores_placed_okVT_fs hEnvT hTails hKitFs)
      (x, st_init) R s0 hpc hrun (withEnvPre_pre_intro h0 hpreVT) hal (fun _ hout => hout)
  · have hpreV_rearr : s0.mem ⊨
        (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ (F0 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre_tok
    have ⟨haddr_ss, _⟩ := withStoresEncPlacedSpecV_pre_addrOk hpreV_rearr
    let kit' := h45_kitAt_placed kit x.rem.val
    let kitEnv' := h45_kitAtBudget kitEnv x.rem.val
    have hEnvE : EncEnvPlaced A lim kit' kitEnv' st0 ikit ikitEnv ist0 Scope (· = [])
        C ctl uuidTryParse S sendEnv encRecord Hk :=
      { hooks := hhooks
        kitOk := h45_sessionOnlyKitPlacedOkSE_kitAt x.rem.val hKitOk
        ikitOk := hIkitOk
        callees := EncCalleesPlaced.of_otrEnc hhooks hOtrEmpty
        vtables := ⟨hVtables.loadSlot, hVtables.storeSlot, hVtables.loadFutDrop,
          hVtables.loadFutSize, hVtables.loadFutAlign, hVtables.loadFutPoll,
          hVtables.storeFutDrop, hVtables.storeFutSize, hVtables.storeFutAlign,
          hVtables.storeFutPoll⟩
        idVtables := hIdVtables
        scopeIn := fun r ⟨hsc, hl, _⟩ => hScopeIn r ⟨hsc, hl⟩
        scopeQ := fun r s ⟨hsc, hl, hrem⟩ hsess => by
          subst hrem
          exact hpqE r ⟨hsc, hl⟩ s hsess
        recOk := fun {y r sess otr taken k m otr'} h15 =>
          hRecOk (h15.2.1.2.2.symm ▸ haddr_ss)
            (h45_stepsThroughEncrypt_mono_placed (fun _ ⟨hsc, hl, _⟩ => ⟨hsc, hl⟩) h15) }
    have hpreV' : s0.mem ⊨
        (withStoresEncPlacedSpecV A lim kit' kitEnv' st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ (F0 ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpreV_rearr
      dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded, kit', kitEnv']
      rw [h45_stackV_kitAt_placed kit x.rem.val,
        h45_withStoresEncEnv_kitAt_self kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv
          uuidTryParse x]
      exact sepConj_mono_left (sepConj_mono_left
        (h45_pure_mono_placed
          fun ⟨hfit, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hss, hid⟩ =>
            ⟨hfit, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ⟨hss, rfl⟩, hid⟩))
    exact subroutine_ok.mono_outcome
      (withStores_placed_okV_fs (hEnvE.toTempTwinsFull (@hTails kit' kitEnv' st0 Scope)) hKitFs)
      (x, st_init) (F0 ∗ R) s0 hpc hrun (withEnvPre_pre_intro h0 hpreV') hal
      (fun _ hout => h45_subroutineOutcome_cli_of_kitAt_placed hout)

/-- **Budget-threaded relocatable CLI disjunctive `_with_stores` encrypt (`_fs`)** specialized to
`tokenInitPlacedAt` (matching `SlotOfInnerPlacedBudget.withStoresEncPlacedSpecVT_cli`). -/
theorem withStores_placed_okVT_fs_cli [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hhooks : PublicApiEncHooksPlaced A lim Hk)
    (hKitOk : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord Hk)
    (hIkitOk : IdentityStoreKitPlacedOkI A lim ikit ikitEnv Hk)
    (hOtrT : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl
        (otrEncryptPlacedSpecQT tokenInitPlacedAt C A lim ctl uuidTryParse S sendEnv)))
    (hOtrEmpty : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQ (· = []) C A lim ctl uuidTryParse S sendEnv)))
    (hVtables : SessionOnlyVtablesPlacedOk kit) (hIdVtables : IdentityVtablesPlacedOk ikit)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 Hk))
    (hScopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hScopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8)))
      (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
      s.state.pqRatchetState.length < 2 ^ 32)
    (hRecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse
        x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken))
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl uuidTryParse S sendEnv encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) :=
  withStores_placed_okVT_fs_cli_F0 hhooks hKitOk hIkitOk hOtrT hOtrEmpty hVtables hIdVtables
    hKitFs hScopeIn hScopeQ hRecOk hTails

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudget
