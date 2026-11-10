/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded Stage P2 Callee Bundles and `withFds` Lifts

Defines `FdsGe3Closed`-carrying Stage P2 callee bundles (`StageP2BaseCalleesPlaced4KFd`,
`StageP2PureCalleesPlacedOfEnvFd`, `StageP2PureCalleesPlaced4KOfEnvFd`) and lifts them to
`AllocWithFds.withFds A` under `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives WellSizedAcceptKeysInput
  bytesToBv8 encodeEC pqxdhEntryStackExt
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  InitBobCallGhost bobParamsFieldsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2BobSession344Bv8V1 p2BobSpqrParams stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1OkAtPlacedOfEnv StageP2BaseCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
  dropProcessPrekeyImplState1Spec initializeBobSessionErr4KInnerPlacedSpec
  initializeBobSessionErr4KPlacedSpec promoteMatchingSessionEmptySpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  subroutine_ok_withLsCodeLoaded_mono withFds_pool_eq_of_fdsGe3Closed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctSpec isSameAccountDistinctSpecExt p2BobSpqrVecBufBudget
  promoteStateEmpty4KSpec promoteStateEmptySpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  initializeBobSessionInnerPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (
  initializeBobSessionErrInnerPlacedSpec initializeBobSessionErrPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  curveKeyPairSerdeBudgetSpec kemKeyPairFromPubPrivOkSpec preKeyRecordKeyPairBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  publicKeySerializeSpec publicKeySerializeSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec
)

theorem publicKeySerializeSpec_ok_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpec M A lim)))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M (withFds A) lim)) := by
  refine subroutine_ok_withLsCodeLoaded_mono h (fun ⟨x, st⟩ R s hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [publicKeySerializeSpec, publicKeySerializeSpecWithStack, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

theorem kemKeyPairFromPubPrivOkSpec_ok_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim)))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M (withFds A) lim)) := by
  refine subroutine_ok_withLsCodeLoaded_mono h
    (fun ⟨⟨pubPtr, pk, privPtr, sk, outPtr⟩, st⟩ R s hp => ?_)
    (fun ⟨⟨pubPtr, pk, privPtr, sk, outPtr⟩, st⟩ R s0 sf hq => ?_)
  · dsimp only [kemKeyPairFromPubPrivOkSpec,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
      CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
      RustCliAllocBudget.atState, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [kemKeyPairFromPubPrivOkSpec,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
      CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
      RustCliAllocBudget.atState, withFds_live]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

theorem dropSpeSpec_ok_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl
          (withFdsGe3Closed (dropSpeSpec M A lim))))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl
          (dropSpeSpec M (withFds A) lim))) := by
  refine subroutine_ok_withLsCodeLoaded_mono h (fun ⟨x, st⟩ R s hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded,
      dropSpeSpec, withFds_repAlloc, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded, withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [dropSpeSpec, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

theorem dropSessionStructureLocal2Spec_ok_withFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M (withFds A) lim)) := by
  refine subroutine_ok_withLsCodeLoaded_mono h (fun ⟨x, st⟩ R s hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [dropSessionStructureLocal2Spec, withFds_repAlloc, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [dropSessionStructureLocal2Spec, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

/-- `FdsGe3Closed`-preserving variant of `InitializeBobV1OkAtPlacedOfEnv`. -/
def InitializeBobV1OkAtPlacedOfEnvFd [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) (bobV1Stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp),
    LibsignalCodeRoLoaded lsmpl s0.mem → FdsGe3Closed s0.fs → s0.status = ExecStatus.Running →
    s0.pc = lsmpl.base 75 →
    s0.spAligned = true → s0.sp - 576#64 ≠ 0#64 →
    s0.readReg64 (.gpr 0#5) = argPtr → s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr →
    s0.readReg64 (.gpr 8#5) = outPtr →
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp → ikBPk.length = 32 → spkBPk.length = 32 →
    acceptKeys P inp = some drKey →
    FitsEnv M lim st (BobV1Env inp drKey) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp bobV1Stk ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        ∃ (evs : List AllocEvent),
          BobV1Env inp drKey evs ∧
          (∃ (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
              ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spqrCap spqrBufPtr : BitVec 64)
             (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64),
            localIkBoxPtr ≠ 0#64 ∧ remoteIkBoxPtr ≠ 0#64 ∧ rootKeyBoxPtr ≠ 0#64 ∧
            baseKeyBoxPtr ≠ 0#64 ∧ ratchetPubBoxPtr ≠ 0#64 ∧ ratchetPrivBoxPtr ≠ 0#64 ∧
            chainKeyBoxPtr ≠ 0#64 ∧
            (P_f ⊢
              (outPtr ↦ₛ p2BobSession344Bv8V1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
                spqrCap spqrBufPtr
                (BitVec.ofNat 64 (initialStateValue F (p2BobSpqrParams drKey.pqrKey)).length)
                ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
              p2BobSpqrVecBufBudget A
                spqrCap spqrBufPtr (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
              bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
                inp ikBPk spkBPk 0#8 ∗
              (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC ikBPk)) ∗ A.live localIkBoxPtr 33 1 ∗
              (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ikAPk)) ∗
              A.live remoteIkBoxPtr 33 1 ∗
              (rootKeyBoxPtr ↦ₛ bytesToBv8 drKey.rootKey) ∗ A.live rootKeyBoxPtr 32 1 ∗
              (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC inp.hdr.ekAPk)) ∗
              A.live baseKeyBoxPtr 33 1 ∗
              (ratchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC spkBPk)) ∗
              A.live ratchetPubBoxPtr 33 1 ∗
              (ratchetPrivBoxPtr ↦ₛ bytesToBv8 inp.spkBSk) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
              (chainKeyBoxPtr ↦ₛ bytesToBv8 drKey.chainKey) ∗ A.live chainKeyBoxPtr 32 1 ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              stackAt s0.sp bobV1Stk ∗ A.pool lim (M.stepEvents evs st) sf ∗ Frame) ∧
            sf.status = ExecStatus.Running ∧ sf.pc = s0.readReg64 (.gpr 30#5) ∧ sf.sp = s0.sp ∧
            CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧ FdsGe3Closed sf.fs))
      Qp

abbrev InitializeBobV1OkPlacedOfEnvFd [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlacedOfEnvFd P A lim F BobV1Env ext (stageP2bStack + 0x700)

abbrev InitializeBobV1OkPlaced4KOfEnvFd [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  InitializeBobV1OkAtPlacedOfEnvFd P A lim F BobV1Env ext (768 + pqxdhEntryStackExt)

theorem InitializeBobV1OkAtPlacedOfEnvFd.toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {bobV1Stk : Nat}
    (h : InitializeBobV1OkAtPlacedOfEnvFd P A lim F BobV1Env ext bobV1Stk) :
    InitializeBobV1OkAtPlacedOfEnv P (withFds A) lim F BobV1Env ext bobV1Stk := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
    R hm hL
  rw [withFds_pool_enforced A henf] at hm
  have hm_fds : s0.mem ⊨ ⌜FdsGe3Closed s0.fs⌝ ∗
      ((bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp bobV1Stk ∗ A.pool lim st s0 ∗ Frame) ∗ R) :=
    Satisfies.of_eq hm (by sep_ac_rfl)
  rw [satisfies_pure_sepConj] at hm_fds
  rcases hm_fds with ⟨hfds0, hm₀⟩
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey Frame
    hCode hfds0 hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
    hPf, hstf, hpcf, hspf, hcsf, htrf, hfdsf⟩ | hpan⟩ := hcall R hm₀ hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr, remoteIkBoxPtr,
      rootKeyBoxPtr, baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr,
      spqrCap, spqrBufPtr, pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, ?_, hstf, hpcf, hspf, hcsf, htrf⟩⟩
    dsimp only [withFds_live, p2BobSpqrVecBufBudget] at hPf ⊢
    rw [withFds_pool_enforced A henf, pure_sepConj_of_true hfdsf]
    exact hPf
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem initializeBobSessionErr4KPlacedSpec_ok_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Primitives}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (initializeBobSessionErr4KInnerPlacedSpec P A lim AcceptErrEnv)))) :
    subroutine_ok prog entry
      (initializeBobSessionErr4KPlacedSpec P (withFds A) lim AcceptErrEnv) := by
  refine subroutine_ok_mono h
    (fun ⟨g, st⟩ R s hp => ?_)
    (fun ⟨g, st⟩ R s0 sf hq => ?_)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq)
    (fun _ _ _ _ hq => hq)
  · dsimp only [initializeBobSessionErr4KPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      initializeBobSessionErr4KInnerPlacedSpec, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [initializeBobSessionErr4KPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [initializeBobSessionErr4KInnerPlacedSpec, withFds_live, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

theorem initializeBobSessionErrPlacedSpec_ok_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true) {P : Primitives}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (initializeBobSessionErrInnerPlacedSpec P A lim AcceptErrEnv)))) :
    subroutine_ok prog entry
      (initializeBobSessionErrPlacedSpec P (withFds A) lim AcceptErrEnv) := by
  refine subroutine_ok_mono h
    (fun ⟨g, st⟩ R s hp => ?_)
    (fun ⟨g, st⟩ R s0 sf hq => ?_)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq)
    (fun _ _ _ _ hq => hq)
  · dsimp only [initializeBobSessionErrPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      initializeBobSessionErrInnerPlacedSpec, withFdsGe3Closed] at hp ⊢
    rw [withFds_pool_enforced A henf] at hp
    exact Satisfies.of_eq hp (by sep_ac_rfl)
  · refine Satisfies.mono (sepConj_mono_left ?_) hq
    dsimp only [initializeBobSessionErrPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded, withFdsGe3Closed]
    refine Entails.pure_left fun hfds => ?_
    dsimp only [initializeBobSessionErrInnerPlacedSpec, initializeBobSessionInnerPlacedSpec,
      withFds_live, withFds_repAlloc]
    simp only [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds]
    exact Entails.refl _

/-- `FdsGe3Closed`-preserving variant of `StageP2BaseCalleesPlaced4K`. -/
structure StageP2BaseCalleesPlaced4KFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpec M A lim)))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim)))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl
          (withFdsGe3Closed (dropSpeSpec M A lim))))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse))
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)))

theorem StageP2BaseCalleesPlaced4KFd.toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ext : String → Option (State → State)}
    (h : StageP2BaseCalleesPlaced4KFd A lim ext) :
    StageP2BaseCalleesPlaced4K (withFds A) lim ext where
  publicKeySerialize := publicKeySerializeSpec_ok_withFds henf h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := kemKeyPairFromPubPrivOkSpec_ok_withFds henf h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := dropSpeSpec_ok_withFds henf h.dropSpe2
  isSameAccount := h.isSameAccount
  promoteStateEmpty := h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 :=
    dropSessionStructureLocal2Spec_ok_withFds henf h.dropSessionStructure3

/-- `FdsGe3Closed`-preserving variant of `StageP2PureCalleesPlacedOfEnv`. -/
structure StageP2PureCalleesPlacedOfEnvFd [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpec M A lim)))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim)))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl
          (withFdsGe3Closed (dropSpeSpec M A lim))))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))
  initializeBobV1 : InitializeBobV1OkPlacedOfEnvFd P A lim F BobV1Env ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (initializeBobSessionErrInnerPlacedSpec P A lim AcceptErrEnv)))
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmptySpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)))

/-- `FdsGe3Closed`-preserving variant of `StageP2PureCalleesPlaced4KOfEnv`. -/
structure StageP2PureCalleesPlaced4KOfEnvFd [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  publicKeySerialize :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (publicKeySerializeSpec M A lim)))
  promoteMatchingSessionEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec)
  curveKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec)
  kemKeyPairSerde :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (kemKeyPairFromPubPrivOkSpec M A lim)))
  preKeyRecordKeyPair :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec)
  dropSpe2 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 511)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalTripleRatchet.Getters.withLsRoLoaded lsmpl
          (withFdsGe3Closed (dropSpeSpec M A lim))))
  isSameAccount :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse))
  initializeBobV1 : InitializeBobV1OkPlaced4KOfEnvFd P A lim F BobV1Env ext
  initializeBobErr :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 75)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (initializeBobSessionErr4KInnerPlacedSpec P A lim AcceptErrEnv)))
  promoteStateEmpty :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec)
  dropProcessPrekeyImplState1 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)
  dropSessionStructure3 :
    subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim)))

theorem StageP2PureCalleesPlacedOfEnvFd.toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlacedOfEnvFd P A lim F BobV1Env AcceptErrEnv ext) :
    StageP2PureCalleesPlacedOfEnv P (withFds A) lim F BobV1Env AcceptErrEnv ext where
  publicKeySerialize := publicKeySerializeSpec_ok_withFds henf h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := kemKeyPairFromPubPrivOkSpec_ok_withFds henf h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := dropSpeSpec_ok_withFds henf h.dropSpe2
  isSameAccount := h.isSameAccount
  initializeBobV1 := InitializeBobV1OkAtPlacedOfEnvFd.toWithFds henf h.initializeBobV1
  initializeBobErr := initializeBobSessionErrPlacedSpec_ok_withFds henf h.initializeBobErr
  promoteStateEmpty := h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 :=
    dropSessionStructureLocal2Spec_ok_withFds henf h.dropSessionStructure3

theorem StageP2PureCalleesPlaced4KOfEnvFd.toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext) :
    StageP2PureCalleesPlaced4KOfEnv P (withFds A) lim F BobV1Env AcceptErrEnv ext where
  publicKeySerialize := publicKeySerializeSpec_ok_withFds henf h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := kemKeyPairFromPubPrivOkSpec_ok_withFds henf h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := dropSpeSpec_ok_withFds henf h.dropSpe2
  isSameAccount := h.isSameAccount
  initializeBobV1 := InitializeBobV1OkAtPlacedOfEnvFd.toWithFds henf h.initializeBobV1
  initializeBobErr := initializeBobSessionErr4KPlacedSpec_ok_withFds henf h.initializeBobErr
  promoteStateEmpty := h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 :=
    dropSessionStructureLocal2Spec_ok_withFds henf h.dropSessionStructure3

theorem StageP2PureCalleesPlaced4KOfEnvFd.toStageP2BaseCalleesPlaced4KFd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext) :
    StageP2BaseCalleesPlaced4KFd A lim ext where
  publicKeySerialize := h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := h.dropSpe2
  isSameAccount := h.isSameAccount
  promoteStateEmpty := h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 := h.dropSessionStructure3

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd
