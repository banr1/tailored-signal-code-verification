/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `MessageEncrypt` Assembly

Composes the nine budget-threaded `[LibsignalPlacement]` segments on `lsProg_464 H` (`blkPl_464`)
into `withStores_placed_okV` and `withStores_placed_okV_fs` for `withStoresEncBudgetSpecV`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost)
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (
  EncFsCtxPlaced encEntryPlaced lsTimeAddSym
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  CmStateVBudget EncCalleesBudget EncEnvBudget IdentityStoreBudgetEnv
  PublicApiEncHooksBudget SegExitBudget SegIdentitySpecVBudget SegSaveSpecVBudget
  SegSignalSpecVBudget SegTrustSpecVBudget SessionStoreBudgetEnv SpqrSendBudgetEnv
  otrEncryptBudgetSpecQ withStoresEncBudgetSpecV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  EncEnvFullBudget SegApplyStoreSpecVBudget SegFinishSpecVBudget SegFromSpecVBudget
  SegLoadSpecVBudget SegPreKeySpecVBudget timeAddBudgetSpec
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget (
  segLoad_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget (
  segFrom_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlacedBudget (
  segIdentity_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalPlacedBudget (
  segSignal_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget (
  segPreKey_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget (
  segTrust_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget (
  segSave_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlacedBudget (
  segApplyStore_placed_okV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishPlacedBudget (
  segFinish_placed_okV
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (
  remote_identity_key_placed_ok
)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget (
  unackItems_ls_placed_ok
)

variable [LibsignalPlacement] {M : AllocCostModel}
  {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {C : Crypto} {ctl : BitVec 64}
  {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
  {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}

/-- Extract `kit.addrOk` and `ikit.addrOk` from `(withStoresEncBudgetSpecV ...).pre`. -/
theorem withStoresEncBudgetSpecV_pre_addrOk
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp.1 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hss, hid⟩
  exact ⟨hss, hid⟩

/-- All nine budget-threaded `MessageEncrypt` segments on `lsProg_464 H` under `[LibsignalPlacement]`. -/
structure EncSegsVBudget
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  load : SegLoadSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  fromS : SegFromSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  identity : SegIdentitySpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  signal : SegSignalSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  preKey : SegPreKeySpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  trust : SegTrustSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  save : SegSaveSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  applyStore : SegApplyStoreSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H
  finish : SegFinishSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord H

/-- All nine budget-threaded `[LibsignalPlacement]` segment proofs assembled into `EncSegsVBudget`. -/
theorem encSegsV_placed_ok
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} :
    EncSegsVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H where
  load := segLoad_placed_okV
  fromS := segFrom_placed_okV
  identity := segIdentity_placed_okV
  signal := segSignal_placed_okV
  preKey := segPreKey_placed_okV
  trust := segTrust_placed_okV
  save := segSave_placed_okV
  applyStore := segApplyStore_placed_okV
  finish := segFinish_placed_okV

/-- Chain a `[LibsignalPlacement]` budget segment into the rest of the run on `lsProg_464 H`. -/
theorem segExitBudget_chain
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H
      x st_init R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_464 H)
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s') :
    reaches_outcome (lsProg_464 H)
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- `segExitBudget_chain` carrying the fs carrier `EncFsCtxPlaced kit ikit H s0` to the next seam. -/
theorem segExitBudget_chainFs
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (hfs : EncFsCtxPlaced kit ikit H s0 s)
    (h1 : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H
      x st_init R s0 s next)
    (h2 : ∀ s', EncFsCtxPlaced kit ikit H s0 s' → next s' →
      reaches_outcome (lsProg_464 H)
        (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
        (x, st_init) R s0 s') :
    reaches_outcome (lsProg_464 H)
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
      (x, st_init) R s0 s := by
  refine Arm64.reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact Arm64.reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact Arm64.reaches_outcome_steps hst (Arm64.reaches_outcome.of_outcome hout)

/-- `session_message_encrypt_with_stores` (`blkPl_464`) satisfies `withStoresEncBudgetSpecV`
with both kits' `envOk` on the entry files from `EncSegsVBudget`, given `KitFsOk`. -/
theorem withStores_placed_ok_of_segsV_fs
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (hSegs : EncSegsVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 H)) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withEnvPre
        (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun (x, st_init) R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have ⟨haddr_ss, haddr_id⟩ := withStoresEncBudgetSpecV_pre_addrOk hpre
  have hfs0 : EncFsCtxPlaced kit ikit H s0 s0 := FsCtx.of_entry hKitFs h0
  refine segExitBudget_chainFs hfs0 (hSegs.load hEnv x st_init R s0 hfs0 hpc hrun hal hpre) ?_
  rintro s hfs ⟨st1, r, g, sess, hCur⟩
  refine segExitBudget_chainFs hfs (hSegs.fromS hEnv x st_init st1 r g sess R s0 s hCur) ?_
  rintro s hfs ⟨st2, otr, taken, pqCap, pqPtr, hOtr⟩
  refine segExitBudget_chainFs hfs
    (hSegs.identity hEnv.toEncEnvBudget x st_init st2 r sess otr taken pqCap pqPtr R s0 s hOtr) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H
      x st_init R s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R s0 s') := by
    cases hp : sess.pendingPreKey with
    | none =>
      exact hSegs.signal hEnv.toEncEnvBudget x st_init st2 r sess otr taken pqCap pqPtr k R s0 s hp hKey
    | some _ =>
      exact hSegs.preKey hEnv x st_init st2 r sess otr taken pqCap pqPtr k R s0 s (by simp [hp]) hKey
  refine segExitBudget_chainFs hfs hCm ?_
  rintro s hfs ⟨st3, m, otr', pqCap', pqPtr', hCmS⟩
  refine segExitBudget_chainFs hfs
    (hSegs.trust hEnv.toEncEnvBudget x st_init st3 r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hCmS) ?_
  rintro s hfs ⟨st4, hSave⟩
  refine segExitBudget_chainFs hfs
    (hSegs.save hEnv.toEncEnvBudget x st_init st4 r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hSave) ?_
  rintro s hfs ⟨st5, c, hApply⟩
  refine segExitBudget_chainFs hfs
    (hSegs.applyStore hEnv x st_init st5 r sess otr taken k m otr' pqCap' pqPtr' c R s0 s haddr_ss hfs hApply) ?_
  rintro s _ ⟨st6, hStored⟩
  exact segExitBudget_chain (hSegs.finish hEnv x st_init st6 r sess otr taken k m otr' c R s0 s hStored)
    (fun _ hF => False.elim hF)

/-- `session_message_encrypt_with_stores` (`blkPl_464`) satisfies `withStoresEncBudgetSpecV`
from `EncSegsVBudget` when both kits have trivial `envOk`. -/
theorem withStores_placed_ok_of_segsV
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (hSegs : EncSegsVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord) :=
  subroutine_ok_of_withEnvPre (withStores_placed_ok_of_segsV_fs hEnv hSegs (.inl htriv))
    fun s => htriv s.fs.files

/-- Relocatable budget-threaded `session_message_encrypt_with_stores` contract for arbitrary
session and identity stores with trivial `envOk`. -/
theorem withStores_placed_okV
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord) :=
  withStores_placed_ok_of_segsV hEnv encSegsV_placed_ok htriv

/-- Relocatable budget-threaded `session_message_encrypt_with_stores` contract preserving both
kits' `envOk` on the entry files, given `KitFsOk`. -/
theorem withStores_placed_okV_fs
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord H)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_464 H)) :
    subroutine_ok (lsProg_464 H) encEntryPlaced
      (withEnvPre
        (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStores_placed_ok_of_segsV_fs hEnv encSegsV_placed_ok hKitFs

/-- Construct `EncCalleesBudget` from `timeAddVm` and `hotrEnc` by discharging `remoteIk` and `unack`. -/
theorem encCalleesBudget_of_otrEnc
    {Q : List (BitVec 8) → Prop} {parse : UuidParser}
    (htimeAddVm : HookSat H CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddBudgetSpec))
    (hotrEnc : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (otrEncryptBudgetSpecQ Q C A lim ctl parse S sendEnv))) :
    EncCalleesBudget Q C A lim ctl parse S sendEnv H where
  remoteIk :=
    CryptoVerification.LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (remote_identity_key_placed_ok A.repAlloc H)
  otrEnc := hotrEnc
  unack :=
    CryptoVerification.LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (unackItems_ls_placed_ok htimeAddVm)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlacedBudget
