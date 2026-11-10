/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 1): Segments `SegFrom` and `SegTrust`

Re-exports the `VT` environment and restricted-kit/scope bridges from `Seg1PlacedBudgetAux` and
proves `h45_segFrom_placed_okVT` and `h45_segTrust_placed_okVT` on Block `464` (`lsProg_464 H`)
under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto IdentityKey Mut OutgoingTripleRatchet SessionState SignalProtocolError)
open CryptoGames.LibsignalSessionApi
  (Api ApiError CiphertextMessage Session SessionRecord StoreAnswers StoreCall
   execOk liftProtocol messageEncrypt storeCall)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (EncFsCtxPlaced encCommonPlaced encEntryPlaced encStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (curState_placed_mem_unpack fromRestFramePlaced otrFrom_placed_err_tail_mem
   otrFrom_placed_err_unpack otrFrom_placed_ok_pack otrFrom_placed_ok_unpack
   otrFrom_placed_post_unpack otrFrom_placed_pre_frame)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (execOk_fromSessionState_of_error_shared_lb execOk_fromSessionState_of_ok_shared_lb
   fromSessionState_error_ne_invalidState_shared_lb spAligned_of_sp_eq)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (speStaged_storeErr_placed trustVtablesAt_placed_intro)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (answersOfTrust trustPoll_merge_970 trustPoll_merge_9d0 trustVtablesAt
   words3_entails_memRegion24)
open CryptoVerification.LibsignalPublicApi (EncryptGhost loadedSession)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost sessionRecordAt storeHookStr)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (StepsThroughEncrypt WithStoresEncGhost cmScratch cmSlots
   encSpillsAtV encSubStackV okAnswers takenRecord)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
  (SpeStaged dropRecordSlots pollWith speStaged_untrusted vecU8Body)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (otrFromRawPlacedSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (otrAt otrResultAt speWord uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (CmStateVPlaced CurStateVPlaced EncTailsVPlaced OtrStateVPlaced SaveStateVPlaced SegExitPlaced
   toTempTwinsIkitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (segExitPlaced_eq_tempTwins segExit_placed_of_sepWP)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (SegExitBudget SpqrSendBudgetEnv StringCloneEnv TrustStepEnv retagIdentityStore retagSessionStore)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
  (segFrom_placed_step_err_vm segFrom_placed_step_ok_vm segFrom_placed_step_pre_vm)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlacedBudget
  (cliTrustPassive cliTrustPassive_atState seam_mem_split_placed seam_mem_to_tail_placed
   trustActivePlaced trustActive_split_extra_placed trustBaseActivePlaced
   trustBaseActive_join_extra_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget
  (trust_false_to_d40_placed trust_to_bc4_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget
  (step_bc4_err_placed step_bc4_ok_true_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (EncCalleesTPlaced EncEnvTPlaced EncTailsVTPlaced h45_ScopeNone_placed h45_callsRel_kitF_placed
   h45_encTailV_kitF_placed h45_envF_placed h45_envL_placed h45_envNone_placed
   h45_kitEnvF h45_kitEnvL h45_kitF_placed h45_kitL_placed h45_otrEncryptPlacedOkQ_false
   h45_segExit_kitF_placed h45_segExit_kitL_placed h45_segExit_mono_scope_placed
   h45_segExit_of_tempTwins_kitF_scope h45_storeFinal_kitF_placed
   h45_subroutineOutcome_kitF_placed h45_subroutineOutcome_kitL_placed
   h45_subroutineOutcome_mono_scope_placed h45_subroutineOutcome_vt_of_v_placed
   h45_tailModel_kitF_placed h45_traceOfWith_kitF_placed h45_withStoresEncEnv_kitF
   h45_withStoresEncEnv_kitL h45_withStoresEncEnv_mono_scope
   otrEncryptPlacedSpecQT withStoresEncPlacedSpecVT)

export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_kitF_placed h45_storeFinal_kitF_placed h45_callsRel_kitF_placed h45_traceOfWith_kitF_placed)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_tailModel_kitF_placed h45_ScopeNone_placed h45_kitL_placed)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (withStoresEncPlacedSpecVT otrEncryptPlacedSpecQT EncCalleesTPlaced h45_otrEncryptPlacedOkQ_false)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (EncEnvTPlaced EncTailsVTPlaced h45_kitEnvF h45_kitEnvL)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_withStoresEncEnv_kitF h45_withStoresEncEnv_mono_scope h45_withStoresEncEnv_kitL)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_subroutineOutcome_kitF_placed h45_segExit_kitF_placed h45_encTailV_kitF_placed)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_subroutineOutcome_mono_scope_placed h45_segExit_mono_scope_placed)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_subroutineOutcome_kitL_placed h45_segExit_kitL_placed h45_segExit_of_tempTwins_kitF_scope)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (h45_envF_placed h45_subroutineOutcome_vt_of_v_placed h45_envNone_placed h45_envL_placed)

/-! ## 1. Segment `SegFrom` under `EncEnvTPlaced`: `h45_segFrom_placed_okVT` -/

section SegFrom

private theorem fromRestFramePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st1 st2 : M.σ) (s1 s2 : State) :
    fromRestFramePlaced ss_vt id_vt (A.atState lim st1 s1) =
      fromRestFramePlaced ss_vt id_vt (A.atState lim st2 s2) := rfl

private theorem speStaged_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    SpeStaged (A.atState lim st s) = SpeStaged A.repAlloc := rfl

private theorem sessionRecordAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc := rfl

private theorem otrAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 st2 : M.σ) (s1 s2 : State) :
    otrAt (A.atState lim st1 s1) = otrAt (A.atState lim st2 s2) := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs,
      (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal st0 ans cs =
      kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs,
      (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs =
      ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced
      (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit)
      ((LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit)
      ((LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs)
      x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced
          (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit) st
          (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit) ist
          x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).ss_vt
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).id_vt
        (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit)
        ((LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal
          st0 answers (x.model C S uuidTryParse answers).2)
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit)
        ((LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal
          ist0 answers (x.model C S uuidTryParse answers).2)
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
      encSpillsAtV
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).ss_vt
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

private theorem model_of_fromSessionState_error_placed
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error_shared_lb herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState_shared_lb herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

theorem h45_segFrom_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R0 : SepProp) (s0 s : State)
    (hcurState : CurStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r g sess R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st' otr taken pqCap pqPtr,
        OtrStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken pqCap pqPtr R0 s0 s') := by
  rw [segExitPlaced_eq_tempTwins]
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hbud0, hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hs_pc' : s.pc = encEntryPlaced + 0x20c#64 := hs_pc
  have hsc' : kit.ScopeAt Scope st0 x.rem.val r := hsc
  have htr' : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) := htr
  obtain ⟨G, u280, _, hpure, hm_unp⟩ :=
    curState_placed_mem_unpack (A.atState lim st s) ctl x r g sess sp R s0 hsp0 hcur hm
  refine SegExitBudget.of_sepWP (R0 := R0) hm_unp
    (segFrom_placed_step_pre_vm hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hAs1 : A.atState lim st s = A.atState lim st s1 :=
    (A.atState_eq_of_vmPreserved lim st hvm01).symm
  rw [hAs1] at hm1
  have hm1_pre := otrFrom_placed_pre_frame (A.atState lim st s1) ctl x g G sess sp R Pm1 s0 s1
    hcrl1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine SegExitBudget.call (R0 := R0) hEnv.callees.otrFrom
    (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (withLsRoCl lsmpl
            (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec
              M A lim)).onExit
            (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpan_post => by
      rw [show (withLsRoCl lsmpl
            (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec
              M A lim)).onPanic
            (⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩, st) s1 sf = ⌜False⌝ from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan_post
      exact hpan_post.1.elim)
    ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  dsimp only [withLsRoCl,
    LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec] at hpost2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost2
  obtain ⟨evs, hpost2⟩ := hpost2
  have hpost2_pull : s2.mem ⊨ ⌜FreeOnlyEvs evs⌝ ∗
      (((withLsRoCl lsmpl (otrFromRawPlacedSpec
            (A.atState lim (M.stepEvents evs st) s2))).post
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 s2 ∗
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          fromRestFramePlaced kit.ss_vt ikit.id_vt (A.atState lim (M.stepEvents evs st) s2)
            ctl x g sp s0)) ∗ R) := by
    rw [← fromRestFramePlaced_atState kit.ss_vt ikit.id_vt A lim st (M.stepEvents evs st) s1 s2]
    dsimp only [withLsRoCl]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj] at hpost2_pull
  rcases hpost2_pull with ⟨hevs, hpost2_rocl⟩
  set st2 := M.stepEvents evs st
  have hbud2 := hbud0.advance hevs
  obtain ⟨hcrl2, G', _, hs2_tr, hm2⟩ :=
    otrFrom_placed_post_unpack (A.atState lim st2 s2) ctl x g G sess
      ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2_rocl
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr')
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt (A.atState lim st2 s2) (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      otrFrom_placed_err_unpack (A.atState lim st2 s2) ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    rw [speStaged_atState A lim st2 s2] at hst
    refine SegExitBudget.of_sepWP (R0 := R0) hm2_err
      (segFrom_placed_step_err_vm hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hvm23, hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hAs23 : A.atState lim st2 s2 = A.atState lim st2 s3 :=
      (A.atState_eq_of_vmPreserved lim st2 hvm23).symm
    rw [hAs23] at hm3
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error_placed (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := otrFrom_placed_err_tail_mem (A.atState lim st2 s3) ctl x
      { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    rw [sessionRecordAt_atState A lim st2 s3] at hm3_tail
    refine SegExitBudget.of_false (hTails.tailFromSessionStateErr x st_init st2 R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc'.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨hbud2.narrow (fun _ => Or.inl),
        hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      rw [encTail_mem_retag_eq (A' := A.atState lim st2 s3) kit st0 ikit ist0 C ctl S x
        (okAnswers r .newOrUnchanged) _ R0 s0]
      rw [hdraws0, hmod_res]
      exact hm3_tail
  · change s2.mem ⊨ otrResultAt (A.atState lim st2 s2) (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      otrFrom_placed_ok_unpack (A.atState lim st2 s2) ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine SegExitBudget.of_sepWP (R0 := R0) hm2_ok
      (segFrom_placed_step_ok_vm hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hvm23, hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hAs23 : A.atState lim st2 s2 = A.atState lim st2 s3 :=
      (A.atState_eq_of_vmPreserved lim st2 hvm23).symm
    rw [hAs23] at hm3
    rw [otrAt_atState A lim st2 st2 s2 s3] at hpack
    have hm3_ok := otrFrom_placed_ok_pack (A.atState lim st2 s3) ctl x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine SegExitBudget.next
      ⟨st2, otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
        G.pq.cap, G.pq.ptr,
        hbud2.narrow (fun _ h =>
          Or.inr ⟨r, sess, otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
            hsc', hcur, execOk_fromSessionState_of_ok_shared_lb hres, h⟩),
        hcur, hsc', execOk_fromSessionState_of_ok_shared_lb hres, ?_⟩
    exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩

end SegFrom

/-! ## 2. Segment `SegTrust` under `EncEnvTPlaced`: `h45_segTrust_placed_okVT` -/

section SegTrust

private theorem dropRecordSlots_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (om : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots (A.atState lim st s) sp scratch g rec ot om poll =
      dropRecordSlots A.repAlloc sp scratch g rec ot om poll := rfl

private theorem encStoreExtraPlaced_retag [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist x s0 =
      encStoreExtraPlaced kit st0 ikit ist x s0 := rfl

theorem h45_segTrust_placed_okVT_of_tails [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTailsF : EncTailsVPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0
      ikit ikitEnv ist0 (fun _ => False) C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0
      ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hcm : CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st',
        SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') := by
  let envF := (h45_envF_placed hEnv).toTempTwins hTailsF
  obtain ⟨hbud, hcm⟩ := hcm
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨h15, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hcm
  have h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' := h15
  dsimp only [retagSessionStore, retagIdentityStore,
    LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore,
    LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore] at htr hm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set F := cliTrustPassive kit.ss_vt ikit.id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActivePlaced ikit.id_vt (A.atState lim st s) s.sp x k ∗
        encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗
        (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x s0 ∗ R0) := by
      rw [hsp, encStoreExtraPlaced_retag]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
    rw [seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp,
        cliTrustPassive_atState] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra_placed (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  dsimp only [retagSessionStore] at hbound hm_join
  have hm_split : s.mem ⊨ (trustVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist0
        s.sp (encSubStackV (h45_kitF_placed kit) ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R) := by
    have hm' := trustVtablesAt_placed_intro envF.idVtables hcrl.2 hm_join
    dsimp only [R, h45_kitF_placed]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm'
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hboundF :
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.withStoresEncStackV (h45_kitF_placed kit) ikit ≤ s0.sp.toNat :=
    hbound
  refine h45_segExit_of_tempTwins_kitF_scope (Scope' := fun _ => False)
    (mid := fun sm =>
      ∃ (evs_trust : List AllocEvent) (ans : Except Unit Bool) (w0 w1 w2 w3 w4 w5 : BitVec 64)
        (H : SepProp),
        sm.pc = encEntryPlaced + 0xbc4#64 ∧
        sm.status = .Running ∧ sm.sp = s.sp ∧ sm.spAligned = true ∧
        LibsignalCodeRoLoaded lsmpl sm.mem ∧
        ikit.trustRel ist0 x.rem.val k .sending ans ∧
        sm.trace = s.trace ++ ikit.trustEvs x.rem.val k .sending ans ∧
        TrustStepEnv ikit (toTempTwinsIkitEnv ikitEnv) ist0 x.rem.val k evs_trust ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x27 = w0 ∧ sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        (match ans with
         | .ok t => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1.setWidth 8 = (if t then 1#8 else 0#8) ∧ H = emp
         | .error () => w0 = 0x800000000000001A#64 ∧ w2 = 10#64 ∧ w3 = 1#64 ∧ H = (w1 ↦ᵣ storeHookStr)) ∧
        (sm.mem ⊨ (trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs_trust st) sm) ikit)
            (ikit.trustUpdate ist0 x.rem.val k .sending ans)
            s.sp (encSubStackV (h45_kitF_placed kit) ikit) x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R)))
    (fun _ => False.elim)
    (trust_to_bc4_placed envF hbud.1.seq_left haddr
      (fun s' hst' htr' =>
        ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
          obtain ⟨⟨hl, -⟩, -⟩ := hq; simp only [hl]).2)
      hboundF hpc hrun hsp_al hx25' hpref0 hcrl hm_split
      (fun sm evs_trust ans w0 w1 w2 w3 w4 w5 H _hsteps_bc4 hpcm hrunm hspm hspm_al hcrlm htrustRel htrm
        htrustEnv hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act =>
        SegExitBudget.next
          ⟨evs_trust, ans, w0, w1, w2, w3, w4, w5, H,
           hpcm, hrunm, hspm, hspm_al, hcrlm, htrustRel, htrm, htrustEnv,
           hx19m, hx20m, hx25m, hx26m, hx28m, hx29m, hvregsm, hx27m, hx21m, hx23m, hans, hmm_act⟩))
    ?_
  rintro sm _hsteps_bc4
    ⟨evs_trust, ans, w0, w1, w2, w3, w4, w5, H,
     hpcm, hrunm, hspm, hspm_al, hcrlm, htrustRel, htrm, htrustEnv,
     hx19m, hx20m, hx25m, hx26m, hx28m, hx29m, hvregsm, hx27m, hx21m, hx23m, hans, hmm_act⟩
  set st_m := M.stepEvents evs_trust st
  have hbud_m := hbud.advance htrustEnv
  let R' : SepProp := encStoreExtraPlaced kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
      memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActivePlaced (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
            (ikit.trustUpdate ist0 x.rem.val k .sending ans) s.sp (encSubStackV kit ikit) x k ∗
          (retagSessionStore (A' := A.atState lim st_m sm) kit).storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F ∗ R0) := by
      dsimp only [R, retagSessionStore, h45_kitF_placed] at hmm_act ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra_placed (retagSessionStore (A' := A.atState lim st_m sm) kit) st0
        (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
        (ikit.trustUpdate ist0 x.rem.val k .sending ans) x k s0 s.sp hsp hbound)) hmm1
    rw [encStoreExtraPlaced_retag] at hmm2
    dsimp only [R', retagIdentityStore] at hmm2 ⊢
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm2
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++ ikit.trustEvs x.rem.val k .sending ans) := by
    rw [htrm, htr, List.append_assoc]
  have hpref_m : s0.trace <+: sm.trace := ⟨_, htrm'.symm⟩
  rcases ans with ⟨⟨⟩⟩ | (_ | _)
  ·
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm
    refine segExit_placed_of_sepWP hmm_emp (step_bc4_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ hsteps_err hpc_err hrun_err hm_err
      ⟨hvm_err, rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_err] at hm_err
    have hcrl_err : LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_err) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_err
      rw [← cliTrustPassive_atState kit.ss_vt ikit.id_vt A lim st_m s_err] at hm_err
      exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by sep_ac_rfl)) hm_err
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5))
      (memRegion (s.sp + 0x9d0#64) 24) (pollWith s.sp 0x970 [1#64, w4, w5]) (w1 ↦ᵣ storeHookStr)
      (trustPoll_merge_970 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.tailModel_trust_err
        (encRecord := encRecord) (s0 := s0) (s := s_err) h15 htrustRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.error ())) = draws :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.draws_eq
        h15 (answersOfTrust r (.error ())) rfl
    refine SegExitPlaced.of_false
      (hTails.tailStoreHookErr x st_init st_m R0 s0 s_err (answersOfTrust r (.error ())) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xc20 0x970 (Or.inl rfl)
        htm (speStaged_storeErr_placed A.repAlloc x.ret w1 w4 w5) ?_)
    refine ⟨hbud_m.narrow (fun _ h => Or.inl h), hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hcrl_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [encTail_mem_retag_eq (A' := A.atState lim st_m s_err) kit st0 ikit ist0 C ctl S x
      (answersOfTrust r (.error ())) _ R0 s0]
    rw [hdraws,
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.model_trust_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal,
      answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by sep_ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, hw1, rfl⟩ := hans
    have hbud_f0 := hbud_m.narrow (fun _ h => Or.inr (Or.inl h))
    have hmm_970 : sm.mem ⊨
        (((sm.sp + 0x970#64) ↦₆₄ w3) ∗ ((sm.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((sm.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) sm.sp x k ∗
          memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
          memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R')) := by
      rw [hspm]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm
    have hmm_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (sm.sp + 0x970#64) w3 w4 w5)) hmm_970
    have hmm_in : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) sm.sp x k ∗
        memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
        memRegion (sm.sp + 0x970#64) 24 ∗ memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R') :=
      Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm_fold
    refine h45_segExit_of_tempTwins_kitF_scope (Scope' := fun _ => False)
      (mid := fun s_d40 =>
        ∃ (evs_clone : List AllocEvent) (cap ptr devWord u9e0 : BitVec 64),
          s_d40.pc = encEntryPlaced + 0xd40#64 ∧
          s_d40.status = .Running ∧ s_d40.sp = sm.sp ∧ s_d40.spAligned = true ∧
          s_d40.trace = sm.trace ∧
          StringCloneEnv x.rem.name evs_clone ∧
          s_d40.readReg64 .x19 = sm.readReg64 .x19 ∧
          s_d40.readReg64 .x26 = sm.readReg64 .x26 ∧
          s_d40.readReg64 .x28 = sm.readReg64 .x28 ∧
          s_d40.readReg64 .x29 = sm.readReg64 .x29 ∧
          calleeSavedVRegs s_d40 = calleeSavedVRegs sm ∧
          s_d40.readReg64 .x27 = speWord 12 ∧
          s_d40.readReg64 .x21 = cap ∧
          s_d40.readReg64 .x23 = ptr ∧
          devWord.setWidth 8 = x.rem.device ∧
          (s_d40.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim (M.stepEvents evs_clone st_m) s_d40) sm.sp x k ∗
            memRegion (sm.sp + 0x470#64) 16 ∗
            memRegion (sm.sp + 0x580#64) 48 ∗
            memRegion (sm.sp + 0x970#64) 24 ∗
            (((sm.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
              ((sm.sp + 0x9d8#64) ↦₆₄ devWord) ∗
              ((sm.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
            vecU8Body A.repAlloc cap ptr x.rem.name.bytes) ∗ (F ∗ R')))
      (fun _ => False.elim)
      (trust_false_to_d40_placed envF hbud_f0.1.seq_left hpcm hrunm hspm_al hx27m hx21m hw1
        (by rw [hspm, hx25m, hx25']) (by rw [hspm, hx26m, hsp, hx26]) hpref_m hcrlm hmm_in
        (fun s_d40 evs_clone cap ptr devWord u9e0 _hsteps_d40 hpc_d40 hrun_d40 hsp_d40 hsp_d40_al htr_d40
          hcloneEnv hx19_d40 hx26_d40 hx28_d40 hx29_d40 hvregs_d40 hx27_d40 hx21_d40 hx23_d40 hdev hm_d40 =>
          SegExitBudget.next
            ⟨evs_clone, cap, ptr, devWord, u9e0,
             hpc_d40, hrun_d40, hsp_d40, hsp_d40_al, htr_d40, hcloneEnv,
             hx19_d40, hx26_d40, hx28_d40, hx29_d40, hvregs_d40,
             hx27_d40, hx21_d40, hx23_d40, hdev, hm_d40⟩))
      ?_
    rintro s_d40 hsteps_d40
      ⟨evs_clone, cap, ptr, devWord, u9e0,
       hpc_d40, hrun_d40, hsp_d40, hsp_d40_al, htr_d40, hcloneEnv,
       hx19_d40, hx26_d40, hx28_d40, hx29_d40, hvregs_d40,
       hx27_d40, hx21_d40, hx23_d40, hdev, hm_d40⟩
    set st_d40 := M.stepEvents evs_clone st_m
    have hbud_d40 := hbud_f0.advance hcloneEnv
    have hcrl_d40 : LibsignalCodeRoLoaded lsmpl s_d40.mem := hcrlm.of_keepsFrozen hsteps_d40.keepsFrozen
    rw [hspm] at hm_d40
    have hm_d40' : s_d40.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_d40 s_d40) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x970#64) 24 ∗
          (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
          vecU8Body A.repAlloc cap ptr x.rem.name.bytes) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_d40 s_d40) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_d40
      rw [← cliTrustPassive_atState kit.ss_vt ikit.id_vt A lim st_d40 s_d40] at hm_d40
      exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by sep_ac_rfl)) hm_d40
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_d40 s_d40) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp (memRegion (s.sp + 0x970#64) 24)
      (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
        ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0))
      (pollWith s.sp 0x9d0 [BitVec.ofNat 64 x.rem.name.bytes.length, devWord, u9e0])
      (vecU8Body A.repAlloc cap ptr x.rem.name.bytes)
      (trustPoll_merge_9d0 s.sp (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_d40'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.tailModel_trust_false
        (encRecord := encRecord) (s0 := s0) (s := s_d40) h15 htrustRel (htr_d40.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.ok false)) = draws :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.draws_eq
        h15 (answersOfTrust r (.ok false)) rfl
    refine SegExitPlaced.of_false
      (hTails.tailCmDrop x st_init st_d40 R0 s0 s_d40 (answersOfTrust r (.ok false)) (.untrustedIdentity x.rem.val)
        (speWord 12) cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0
        (vecU8Body A.repAlloc cap ptr x.rem.name.bytes) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m
        htm
        (speStaged_untrusted A.repAlloc x.ret x.rem.val cap ptr
          (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0 rfl hdev) ?_)
    refine ⟨hbud_d40, hpc_d40,
      ⟨hrun_d40, hsp_d40.trans hspm', hsp0_al, hsp_d40_al,
      by rw [hx29_d40, hx29m, hx29], by rw [hx19_d40, hx19m, hx19], hcrl_d40,
      by rw [hvregs_d40, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_d40, hx26m, hx26], by rw [hx28_d40, hx28m, hx28],
       hx27_d40, hx21_d40, hx23_d40⟩,
      hstk, ?_⟩
    rw [encTail_mem_retag_eq (A' := A.atState lim st_d40 s_d40) kit st0 ikit ist0 C ctl S x
      (answersOfTrust r (.ok false)) _ R0 s0]
    rw [hdraws,
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.model_trust_false h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal,
      answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by sep_ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm
    refine segExit_placed_of_sepWP hmm_emp (step_bc4_ok_true_placed hpcm hrunm hx27m hx21m hw1) ?_
    rintro s_ok _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨hvm_ok, rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx22_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_ok] at hm_ok
    have hcrl_ok : LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_970 : s_ok.mem ⊨
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((s.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x970#64) w3 w4 w5)) hm_ok_970
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      rw [← cliTrustPassive_atState kit.ss_vt ikit.id_vt A lim st_m s_ok] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok_fold
    rw [← seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    refine SegExitPlaced.next ⟨st_m, hbud_m.narrow (fun _ h => Or.inr (Or.inr h)),
      ⟨h15, htrustRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      htr_ok.trans htrm',
      ⟨by rw [hx20_ok, hx20m, hx20], by rw [hx22_ok, hspm'],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [sp, draws, R', retagSessionStore, retagIdentityStore,
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok_seam

theorem h45_segTrust_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hcm : CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st',
        SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') :=
  h45_segTrust_placed_okVT_of_tails hEnv
    (@hTails (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 (fun _ => False))
    (@hTails kit kitEnv st0 Scope)
    x st_init st r sess otr taken k m otr'
    pqCap' pqPtr' R0 s0 s haddr hfs hcm

end SegTrust

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
