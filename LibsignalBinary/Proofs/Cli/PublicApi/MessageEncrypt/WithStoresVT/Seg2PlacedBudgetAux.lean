/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishStepPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinish
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 2a): `SegFinish`

Proves `h45_segFinish_placed_okVT_of_tails` and `h45_segFinish_placed_okVT` (`StoredStateVPlaced`
at `+0xe88` to final exit) on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishStepPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced
  SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced
  SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced
  otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF withStoresEncPlacedSpecV
  withStoresEncPlacedSpecV_pre_addrOk
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon hiding EncTailVPlaced segExit_placed_of_sepWP segExit_placed_of_sepWP_ret
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon hiding segExit_placed_of_sepWP segExit_placed_of_sepWP_ret
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust hiding
  alloc_onPanic_entails_placed dealloc_placed_ok_at_enc stringClone_placed_ok_at_enc
  trustVtablesAt_placed_intro saveVtablesAt_placed_intro storeVtablesAt_placed_intro
  speStaged_storeErr_placed call_nopanic_placed call_alloc_placed call_rocl_alloc_placed
  call_rocl_nopanic_placed
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncCalleesPlaced EncTailVPlaced EncTailsVPlaced PublicApiEncHooksPlaced SegExitPlaced
   StoredStateVPlaced toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (segExitPlaced_eq_tempTwins segExit_placed_of_sepWP)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (EncEnvTPlaced EncTailsVTPlaced h45_envF_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (SeamBudget SpqrSendBudgetEnv freeOnlyEvs_rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
  (dropSessionStructureLocal2BudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem dealloc_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {Hk : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim Hk) :
    subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : lsRustDeallocSym ∈ libsignalSessionExterns)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hhooks.dealloc

private theorem seamBudget_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st FreeOnlyEvs) (hstep : FreeOnlyEvs evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) FreeOnlyEvs :=
  (h.narrow (by rintro _ (h1 | ⟨_, _, rfl, h1, h2⟩); exact h1; exact h1.append h2)).advance hstep

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

private theorem sessionRecordAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc := rfl

private theorem apiEncResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    apiEncResultAt (A.atState lim st s) = apiEncResultAt A.repAlloc := rfl

private theorem sessionStateAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionStateAt (A.atState lim st s) = sessionStateAt A.repAlloc := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

private theorem encCommonPlaced_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 s1 s2 : State)
    (hvm : VmPreserved s1 s2) :
    encCommonPlaced (A.atState lim st s1) ctl x draws s0 =
      encCommonPlaced (A.atState lim st s2) ctl x draws s0 := by
  rw [(A.atState_eq_of_vmPreserved lim st hvm).symm]

private theorem encModelOk_placed_vt {C : Crypto} {S : SpqrModel} :
    EncModelOkStmt C S uuidTryParse := by
  rintro x r sess otr taken k m otr' c ⟨hcur, -, hfrom, hrem, hstep5⟩
  unfold EncEncryptStep at hstep5
  cases hp : sess.pendingPreKey with
  | none =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp]⟩
  | some items =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, hts, hexp, hlt, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp, hts, hexp, hlt, Option.bind]⟩

private theorem segFinish_from_f58_placed_vt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 : BitVec 64) (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A.repAlloc x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0xf58#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  let F := memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
  have hmem_re : s.mem ⊨ (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ (F ∗ R) := by
    have heq :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
        ((words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ (F ∗ R)) := by
      dsimp only [F, sp]; sep_ac_rfl
    rwa [← heq]
  have hwp := finish_copyAtF58_placed_sepWP (Hk := Hk) hbws hdws hw0_ne hpc hrun hsp_al hsp hx22 hx26 hx28
  refine segExit_placed_of_sepWP (R := R0) hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hvm1, hsp1, hsp1_al, htr1, hx29_1, hx19_1, hx28_1, hx22_1, hx27_1, hx21_1, hx23_1, hvregs1, hPf⟩
  subst hPf
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine hTails.tailWriteResult x st_init st R0 s0 s1 answers (.ok m) w0 w1 w2 w3
    (unpack64List bws) H hm1 hst ⟨hbud, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
    ⟨hx28_1, hx22_1, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
  have hbws_mem : words64At (sp + 0x9d0#64) bws ⊢ memRegion (sp + 0x9d0#64) 0xd8 := by
    have h0xd8 : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [h0xd8]
    exact words64At_entails_memRegion (sp + 0x9d0#64) bws (by omega)
  have hjoin_high :
      memRegion (sp + 0x578#64) 0x608 =
        memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) 0xd8 ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [@memRegion_split' (sp + 0x578#64) (sp + 0x9d0#64) 0x458 0x1b0 _
        (by decide) (by bv_omega) (by decide),
      @memRegion_split' (sp + 0x9d0#64) (sp + 0xaa8#64) 0xd8 0xd8 _
        (by decide) (by bv_omega) (by decide)]
  have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hbws_mem)) hmf1
  have heq :
      ((memRegion (sp + 0x9d0#64) 0xd8 ∗ words64At (sp + 0x4a0#64) bws) ∗ (F ∗ R)) =
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ unpack64List bws) ∗ memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
    dsimp only [F]
    rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1,
        ← words64At_eq_pointsToBytes (sp + 0x4a0#64) bws, hjoin_high]
    sep_ac_rfl
  rwa [← heq]

private theorem segFinish_from_ef8_placed_vt [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 prevCap prevPtr : BitVec 64) (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A.repAlloc x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0xef8#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A.repAlloc sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x378 ∗
            words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R))) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hwp := finish_prev_zero_placed_sepWP (Hk := Hk) (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine segExit_placed_of_sepWP (R := R0) hmem_re.2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine segFinish_from_f58_placed_vt hTails x st_init st R0 s0 s1 answers m
      w0 w1 w2 w3 bws dws H hbws hdws hw0_ne hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx22_1.trans hx22, hx26_1.trans hx26, hx28_1.trans hx28,
       hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
        (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
          (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (prev_hdr_378_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x390 ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A.repAlloc sp prevCap prevPtr hcap] at hmem
    let F_core := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0
    have hmem_re : s.mem ⊨
        ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
         ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
           stackAt sp allocHookStack ∗ F_core) ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
               A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x378 ∗
            words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
            ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
              stackAt sp allocHookStack ∗ F_core) ∗ R))) := by
        unfold encCommonPlaced
        rw [protocolAddressAt_atState]
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
             A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x378 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := finish_prev_nz_placed_step_pre (Hk := Hk) (prevPtr := prevPtr) hcap hcap_lt hpc hrun hsp_al hsp
    refine segExit_placed_of_sepWP (R := R0) hmem2 hwp ?_
    intro s_pre P_pre hsteps_pre hpc_pre hrun_pre hmf_pre
      ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hx1_pre, hx2_pre, hlr_pre,
        hx19_pre, hx21_pre, hx22_pre, hx23_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
    subst hP_pre
    have hm_dealloc : s_pre.mem ⊨
        (rustCliDeallocBudgetSpec M A lim).pre (prevPtr, prevCap.toNat * 24, 8, st) s_pre ∗
        ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R) := by
      dsimp only [rustCliDeallocBudgetSpec]
      rw [hsp_pre]
      rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
      have hlr_ls : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr) := by
        rw [show s_pre.readReg64 .lr = _ from hlr_pre]
        simp (config := { decide := true }) only [arm64_norm, wp_norm]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_pre, hx1_pre, hx2_pre, hlr_ls⟩, Eq.mp (congrArg (s_pre.mem ⊨ ·) (by sep_ac_rfl)) hmf_pre⟩
    rw [segExitPlaced_eq_tempTwins]
    refine call_nopanic_placed (R0 := R0) (dealloc_placed_ok_of_hooks hhooks)
      (prevPtr, prevCap.toNat * 24, 8, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hm_dealloc ?_
    intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
    rw [← segExitPlaced_eq_tempTwins]
    dsimp only [rustCliDeallocBudgetSpec] at hmf1
    rw [hsp_pre] at hmf1
    have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨⟨hacp1, _⟩, hmf1⟩ := hmf1
    have htr_call : s1.trace = s_pre.trace := hacp1.2.1
    have hbud1 := seamBudget_step_freeOnly hbud (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
    set st1 := M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
      ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
    have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
      hcrl.of_keepsFrozen (hsteps_pre.trans hsteps_call).keepsFrozen
    refine segFinish_from_f58_placed_vt hTails x st_init st1 R0 s0 s1 answers m
      w0 w1 w2 w3 bws dws H hbws hdws hw0_ne hm1 hst ⟨hbud1, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
      (hcs1.2.2.2.2.2.2.2.2.2.2.1.trans hx29_pre).trans hx29,
      (hcs1.1.trans hx19_pre).trans hx19,
      hcrl1,
      (hcs1.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_pre).trans hvregs⟩,
      ⟨(hcs1.2.2.2.1.trans hx22_pre).trans hx22,
       (hcs1.2.2.2.2.2.2.2.1.trans hx26_pre).trans hx26,
       (hcs1.2.2.2.2.2.2.2.2.2.1.trans hx28_pre).trans hx28,
       (hcs1.2.2.2.2.2.2.2.2.1.trans hx27_pre).trans hx27,
       (hcs1.2.2.1.trans hx21_pre).trans hx21,
       (hcs1.2.2.2.2.1.trans hx23_pre).trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
        (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((A.pool lim st1 s1 ∗ stackAt sp allocHookStack) ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
           (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        unfold encCommonPlaced
        rw [protocolAddressAt_atState]
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
           nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
           stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (prev_hdr_378_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x390 ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

private theorem segFinish_from_ef0_placed_vt [LibsignalPlacement]
    {M : AllocCostModel} {F0 : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 prevCap prevPtr : BitVec 64) (G : SessionGhost) (ssSt : SessionState (List (BitVec 8)))
    (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A.repAlloc x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0xef0#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => cmScratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗
        memRegion (sp + 0x280#64) 0x220 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 (Or.inr rfl) sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (cmScratch sp ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗
      memRegion (sp + 0x280#64) 0x220 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F_core := S50 ∗ vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x220 ∗
    words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
    words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0
  have hmem_re : s.mem ⊨
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗ A.pool lim st s ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ F_core) ∗ R) := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗
          memRegion (sp + 0x280#64) 0x220 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
        (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
         ((sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗ A.pool lim st s ∗
           stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ F_core) ∗ R)) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗
        memRegion (sp + 0x280#64) 0x220 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F_core]
      sep_ac_rfl
    rwa [← heq]
  have hwp := finish_dropSs_placed_step_pre (Hk := Hk) hpc hrun hsp_al hsp
  refine segExit_placed_of_sepWP (R := R0) hmem_re hwp ?_
  intro s_pre P_pre hsteps_pre hpc_pre hrun_pre hmf_pre
    ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hlr_pre,
      hx19_pre, hx21_pre, hx22_pre, hx23_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
  subst hP_pre
  have hcrl_pre : StoreKit.LibsignalCodeRoLoaded lsmpl s_pre.mem :=
    hcrl.of_keepsFrozen hsteps_pre.keepsFrozen
  let dropGhost : FromRecordCallees.DropSessionStructureGhost := ⟨sp + 0x128#64, G, ssSt⟩
  have hm_drop : s_pre.mem ⊨
      (dropSessionStructureLocal2BudgetSpec M A lim).pre (dropGhost, st) s_pre ∗
      ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ F_core) ∗ R) := by
    dsimp only [dropSessionStructureLocal2BudgetSpec, FromRecordCallees.dropSessionStructureLocal2Spec, dropGhost]
    rw [sessionStateAt_atState, hsp_pre]
    change s_pre.mem ⊨ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
      (sessionStateAt A.repAlloc (sp + 0x128#64) G ssSt ∗
        A.pool lim st s ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗ F_core) ∗ R at hmf_pre
    rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
    have hlr_ls : LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s_pre.readReg64 .lr) := by
      rw [show s_pre.readReg64 .lr = _ from hlr_pre]
      simp (config := { decide := true }) only [arm64_norm, wp_norm]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hlr_ls, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0_pre, Eq.mp (congrArg (s_pre.mem ⊨ ·) (by sep_ac_rfl)) hmf_pre⟩
  rw [segExitPlaced_eq_tempTwins]
  refine call_rocl_nopanic_placed (R0 := R0) ((h45_envF_placed hEnv).callees.toTempTwinsFull).dropSs
    (dropGhost, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hcrl_pre hm_drop ?_
  intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
  rw [← segExitPlaced_eq_tempTwins]
  dsimp only [dropSessionStructureLocal2BudgetSpec, FromRecordCallees.dropSessionStructureLocal2Spec, dropGhost] at hmf1
  rw [hsp_pre] at hmf1
  have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hmf1
  obtain ⟨evs_drop, hevs_drop, htr_call, hmf1⟩ := hmf1
  have hbud1 := seamBudget_step_freeOnly hbud hevs_drop
  set st1 := M.stepEvents evs_drop st
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
    ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    hcrl_pre.of_keepsFrozen hsteps_call.keepsFrozen
  refine segFinish_from_ef8_placed_vt hEnv.hooks hTails x st_init st1 R0 s0 s1 answers m
    w0 w1 w2 w3 prevCap prevPtr bws dws H
    hbws hdws hw0_ne hm1 hst ⟨hbud1, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
    (hcs1.2.2.2.2.2.2.2.2.2.2.1.trans hx29_pre).trans hx29,
    (hcs1.1.trans hx19_pre).trans hx19,
    hcrl1,
    (hcs1.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_pre).trans hvregs⟩,
    ⟨(hcs1.2.2.2.1.trans hx22_pre).trans hx22,
     (hcs1.2.2.2.2.2.2.2.1.trans hx26_pre).trans hx26,
     (hcs1.2.2.2.2.2.2.2.2.2.1.trans hx28_pre).trans hx28,
     (hcs1.2.2.2.2.2.2.2.2.1.trans hx27_pre).trans hx27,
     (hcs1.2.2.1.trans hx21_pre).trans hx21,
     (hcs1.2.2.2.2.1.trans hx23_pre).trans hx23⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
  have hjoin_128 :
      memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x220 =
        memRegion (sp + 0x128#64) 0x378 :=
    (@memRegion_split' (sp + 0x128#64) (sp + 0x280#64) 0x158 0x220 _
      (by decide) (by bv_omega) (by decide)).symm
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x378 ∗
       words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
       words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
    change s1.mem ⊨
      (memRegion (sp + 0x128#64) 0x158 ∗
       (A.atState lim st1 s1).pool ∗
       stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗
       ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ F_core ∗ R) at hmf1
    have heq :
        (memRegion (sp + 0x128#64) 0x158 ∗
         (A.atState lim st1 s1).pool ∗
         stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗
         ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ F_core ∗ R) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x378 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x378 ∗
         words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
         words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ (A.atState lim st1 s1).pool) ∗ R))
      rw [stackAt_encSubStack_dropSs sp, ← hjoin_128]
      dsimp only [F_core]
      sep_ac_rfl
    rwa [heq] at hmf1
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
  rwa [← heq2]

theorem h45_segFinish_placed_okVT_of_tails [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R0 : SepProp)
    (s0 s : State)
    (hstored : StoredStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' c R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  rcases hstored with ⟨hbud, ⟨h1to5, htrustRel, hsaveRel, hstoreRel⟩, hpc,
    ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htrace, ⟨hx26, hx28⟩, _, _, _, _, hstack_le, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore, SessionStoreSpec.ScopeAt] at h1to5 htrustRel hsaveRel hstoreRel htrace
  rw [show (retagSessionStore (A' := A.atState lim st s) kit).ss_vt = kit.ss_vt from rfl,
      show (retagIdentityStore (A' := A.atState lim st s) ikit).id_vt = ikit.id_vt from rfl,
      show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit)
            ((retagSessionStore (A' := A.atState lim st s) kit).storeUpdate st0 x.rem.val
              (storedRecord sess otr' taken) (.ok ()))
            (retagIdentityStore (A' := A.atState lim st s) ikit)
            ((retagIdentityStore (A' := A.atState lim st s) ikit).saveUpdate
              ((retagIdentityStore (A' := A.atState lim st s) ikit).trustUpdate ist0 x.rem.val k
                .sending (.ok true)) x.rem.val k (.ok c)) x s0 =
          encStoreExtraPlaced kit
            (kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()))
            ikit
            (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true))
              x.rem.val k (.ok c)) x s0 from rfl,
      sessionRecordAt_atState, apiEncResultAt_atState] at hmem
  have ⟨hmod_eq, hdraws_eq⟩ := encModelOk_placed_vt x r sess otr taken k m otr' c (h1to5.inScope hEnv.scopeIn)
  have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s := by
    refine ⟨⟨by rw [hmod_eq], ?_, ?_⟩, ?_⟩
    · rw [hmod_eq]
      exact ⟨h1to5.2.1.2, hstoreRel, trivial⟩
    · rw [hmod_eq]
      exact ⟨htrustRel, hsaveRel, trivial⟩
    · rw [htrace, hmod_eq]
      dsimp only
      rw [ikit.traceOfWith_all4 kit]
      simp only [okAnswers, List.append_assoc]
  have hstf : kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()) := by
    rw [hmod_eq]
    rfl
  have hidf : ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c) := by
    rw [hmod_eq]
    rfl
  rw [← hdraws_eq, ← hstf, ← hidf] at hmem
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2)
    ikit (ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2) x s0 ∗ R0
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    ((∃∗ g : RecordGhost,
        sessionRecordAt A.repAlloc (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R at hmem
  have hmem_g : s.mem ⊨
      (∃∗ g : RecordGhost, sessionRecordAt A.repAlloc (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      (apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
       memRegion (sp + 0x46a#64) 0x716 ∗
       (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R)) := by
    have heq :
        (((∃∗ g : RecordGhost,
            sessionRecordAt A.repAlloc (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
         cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
         memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R) =
        ((∃∗ g : RecordGhost, sessionRecordAt A.repAlloc (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
         (apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R))) := by sep_ac_rfl
    rwa [← heq]
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_g
  obtain ⟨⟨prevCap, prevPtr, _ | G⟩, hmem_g⟩ := hmem_g
  · unfold sessionRecordAt storedRecord at hmem_g
    rw [sepConj_assoc, sepConj_comm (vecAt _ _ _ _ _ _ _ _), sepConj_assoc,
      satisfies_pure_sepConj] at hmem_g
    exact hmem_g.1.elim
  unfold sessionRecordAt storedRecord sessionStateReprAt at hmem_g
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128] at hmem_g
  dsimp only at hmem_g
  rw [sessionStateAt_unfold_cap] at hmem_g
  have hmem_cm : s.mem ⊨ apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗
      (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
       ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
       ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
       sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
       vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
       cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
       ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R) := by
    have heq :
        ((vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
            G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
            (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
           (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
            (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
             sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken))))) ∗
         (apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R))) =
        (apiEncResultAt A.repAlloc (sp + 0x370#64) (.ok m) ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R)) := by sep_ac_rfl
    rwa [← heq]
  obtain ⟨w0, w1, w2, w3, bws, H, hbws, hw0_ne, hst, hmem_words⟩ :=
    extract_ok_cm (ret := x.ret) hmem_cm
  have h390 : sp + 0x370#64 + 0x20#64 = sp + 0x390#64 := by bv_omega
  rw [h390] at hmem_words
  have hpoll_split :
      memRegion (sp + 0x46a#64) 0x716 =
        memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x4a0#64) (8 * 27) ∗
          memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) (8 * 27) ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [@memRegion_split' (sp + 0x46a#64) (sp + 0x4a0#64) 0x36 0x6e0 _
          (by decide) (by bv_omega) (by decide),
        @memRegion_split' (sp + 0x4a0#64) (sp + 0x578#64) (8 * 27) 0x608 _
          (by decide) (by bv_omega) (by decide),
        @memRegion_split' (sp + 0x578#64) (sp + 0x9d0#64) 0x458 0x1b0 _
          (by decide) (by bv_omega) (by decide),
        @memRegion_split' (sp + 0x9d0#64) (sp + 0xaa8#64) (8 * 27) 0xd8 _
          (by decide) (by bv_omega) (by decide)]
  rw [hpoll_split, memRegion_one (sp + 0x469#64)] at hmem_words
  let F0_s := ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
    words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
    sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R
  have hmem_p : s.mem ⊨
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
       (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0_s))) := by
    have heq :
        (words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
          (memRegion (sp + 0x46a#64) 0x36 ∗ (memRegion (sp + 0x4a0#64) (8 * 27) ∗
           (memRegion (sp + 0x578#64) 0x458 ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗
            memRegion (sp + 0xaa8#64) 0xd8)))) ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0 ∗ R)) =
        (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
         (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
           (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0_s))))) := by
      dsimp only [F0_s]; sep_ac_rfl
    rw [heq, satisfies_pure_sepConj] at hmem_words
    exact hmem_words.2
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmem_p⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_p
  obtain ⟨b469, hmem_p⟩ := hmem_p
  rw [sepConj_comm ((sp + 0x469#64) ↦₈ b469), sepConj_assoc] at hmem_p
  obtain ⟨dws, hdws, hmem_d⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x4a0#64) (by decide) s.mem _ hmem_p
  rw [sepConj_comm (words64At (sp + 0x4a0#64) dws), sepConj_assoc, sepConj_assoc] at hmem_d
  obtain ⟨dws9d0, hdws9d0, hmem_d2⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x9d0#64) (by decide) s.mem _ hmem_d
  let F1 := words64At (sp + 0x4a0#64) dws ∗ H ∗
    sessionStateAfterLocalIk A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S (okAnswers r c)) s0
  have hmem_stage : s.mem ⊨
      (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x469#64) ↦₈ b469) ∗
        words64At (sp + 0x9d0#64) dws9d0) ∗ (F1 ∗ R) := by
    have heq :
        (words64At (sp + 0x9d0#64) dws9d0 ∗
         (F0_s ∗ (((sp + 0x469#64) ↦₈ b469) ∗ words64At (sp + 0x4a0#64) dws))) =
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ b469) ∗
          words64At (sp + 0x9d0#64) dws9d0) ∗ (F1 ∗ R)) := by
      dsimp only [F0_s, F1]; sep_ac_rfl
    rwa [← heq]
  have hpc' : s.pc = encEntryPlaced + 0xe88#64 := hpc
  have hwp := finish_stage_placed_sepWP (Hk := Hk) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (b469 := b469)
    hbws hdws9d0 hcap_lt hpc' hrun hsp_al hsp hx26
  refine segExit_placed_of_sepWP (R := R0) hmem_stage hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hvm1, hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
  subst hPf
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine segFinish_from_ef0_placed_vt hEnv hTails x st_init st R0 s0 s1 (okAnswers r c) m
    w0 w1 w2 w3 prevCap prevPtr
    G (otr'.applyToSessionState taken) bws dws H hbws hdws hw0_ne hm1 hst ⟨hbud, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
    ⟨hx22_1, hx26_1, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x (okAnswers r c) _ R0 s0)) ?_
  have hmf2 : s1.mem ⊨
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
        memRegion (sp + 0x46a#64) 0x36) ∗
      (sessionStateAt A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
       cmScratch sp ∗
       vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
       words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s1) ctl x (x.draws S (okAnswers r c)) s0 ∗ R) := by
    have heq :
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          memRegion (sp + 0x46a#64) 0x36) ∗
        (sessionStateAt A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
         cmScratch sp ∗
         vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
         words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S (okAnswers r c)) s0 ∗ R) =
        ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ 0#8) ∗
          words64At (sp + 0x9d0#64) bws) ∗ (F1 ∗ R)) := by
      rw [sessionStateAt_unfold_cap A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken)]
      dsimp only [F1]
      rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S (okAnswers r c)) s0 s s1 hvm1]
      sep_ac_rfl
    rw [heq, satisfies_pure_sepConj]
    exact ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmf1⟩
  have hmf3 := Satisfies.mono
    (sepConj_mono_left (mid_280_to_4a0_weaken sp k w0 w1 w2 w3 bws hbws)) hmf2
  have heq2 :
      (memRegion (sp + 0x280#64) 0x220 ∗
       (sessionStateAt A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
        cmScratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st s1) ctl x (x.draws S (okAnswers r c)) s0 ∗ R)) =
      ((cmScratch sp ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A.repAlloc (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
        memRegion (sp + 0x280#64) 0x220 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s1) ctl x (x.draws S (okAnswers r c)) s0 ∗ R) := by sep_ac_rfl
  rwa [← heq2]

theorem h45_segFinish_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R0 : SepProp)
    (s0 s : State)
    (hstored : StoredStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' c R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  h45_segFinish_placed_okVT_of_tails hEnv (@hTails kit kitEnv st0 Scope)
    x st_init st r sess otr taken k m otr' c R0 s0 s hstored

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
