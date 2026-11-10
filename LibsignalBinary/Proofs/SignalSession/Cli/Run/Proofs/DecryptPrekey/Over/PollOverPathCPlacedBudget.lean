/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.BodyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Placed CLI Poll Overwrite-Path (`Path C`) Top-Level Branch

Proves budget-threaded poll panic bridges, defines `StageP3Prev1VRegsAtPlacedStmt` and
`StageP3Prev1VRegsPlacedStmt` under `RustCliAllocBudget M`, and proves `closure_pathC_p4_cont_placed`
and `closure_pathC_placed_ok` from `dpPollEntryPlaced + 0x0868#64` (including `LibsignalFrozen`
counterparts).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 hiding
  ChainClone3OkPlaced SenderChainClone3OkPlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over hiding
  stageP4Prev1SharedPlaced stageP4Prev1PrePlaced stageP4Prev1ExitAtPlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliChainClone3_placed_ok cliSenderChainClone3_placed_ok cliDropSessionStructure4_placed_ok_at
  cliFsAt_of_files_eq_placed cliFiles_eq_of_trace_eq_placed
  cliPollStageP4Prev1_fsAt_placed storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
  pathC_recPrev1Ok_of_tryDecrypt_placed
  overGenP3S5PostFrame_placed
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
  stageP4PathCExit_entails_exit_placed stageP3ErrPathC_entails_exit_placed
  stageP3_exit_pathC_to_pollPost_placed
  StageP2OverErrPlaced StageP2OverQpanCliPlacedStmt
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
  overSepWPp_pollGoal_frame_placed overSepWPp_genP3_to_tailQpan_placed
  overPollTryDecryptPlacedSpecP overPollTryDecryptPlacedSpecTPTight
  OverCliTryDecryptPqV1PlacedStmt StageP3Prev1VRegsAtPlacedStmt StageP3Prev1VRegsA0PlacedStmt
  closure_pathC_p4_cont_placed closure_pathC_placed_ok
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollKStateBudget DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
  StageP3OkPrefixEnv StageP3ErrEnv
  pollTryDecryptPlacedSpecP pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  pathC_recPrev1Ok_of_tryDecrypt_placed
  overGenP3Pre_placed overGenP3S5PostFrame_placed overPathAP4RemAtPlaced
  overExit_entails_dpPollPost_placed stageP3MidPathC_entails_p4_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Budget-Threaded Poll Goal Frame & Model-Panic Bridges -/

private theorem x29_eq_sp_add_c70_pathC_placed {s0 s2 : State}
    (hx29 : s2.readReg64 .x29 = s0.sp - 0x60#64)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64) :
    s2.readReg64 .x29 = s2.sp + 0xc70#64 := by
  rw [hx29, hs2_sp]; bv_omega

theorem overSepWPp_pollGoal_frame_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {s0 s1 : State} {P1 Fr_tail R : SepProp}
    (hwp : SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1 P1
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic
            y s0 sf ∗ R))) :
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (P1 ∗ Fr_tail)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic
            y s0 sf ∗ R)) := by
  intro R' hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps1f,
    ⟨hpcm, hrunm, P_f, hmf, hpost, hspf, hcs⟩ | ⟨hpanf, P_f, hmf, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hwp (Fr_tail ∗ R') hm hL
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inl ⟨hpcm, hrunm, P_f ∗ Fr_tail, hmf, ?_, hspf, hcs⟩⟩
    intro hsteps0f hmR; rw [sepConj_assoc] at hmR; exact hpost hsteps0f hmR
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inr (Or.inl ⟨hpanf, P_f ∗ Fr_tail, hmf, ?_⟩)⟩
    intro hsteps0f hmR; rw [sepConj_assoc] at hmR; exact hpan hsteps0f hmR
  · exact (not_satisfies_false_sepConj hoom).elim

theorem dpPollOnPanic_of_modelPanic_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    {K : DpPollKStateBudget M} (stk' : Nat)
    (y : DpPollGhostStateBudget K)
    {C : Crypto} {Q : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 sf : State} {Pf Fr R : SepProp}
    (hmod : genP3S5ModelPanicProp C Q rem loc st msg msgVer rest s0 sf Pf)
    (hpan : st.version = msgVer →
      (genP3S5Model C Q rem loc msg rest st).1 = .error .panic → K.panics y.g)
    (hm : sf.mem ⊨ (Pf ∗ Fr) ∗ R) :
    sf.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R := by
  rw [sepConj_assoc] at hm
  have h1 := hmod (Fr ∗ R) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at h1
  obtain ⟨⟨hver, herr, htr⟩, hrest⟩ := h1
  have hkpan : K.panics y.g := hpan hver herr
  dsimp only [StoreKit.withLsCodeRoLoaded, dpPollSpecStateBudget]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, hkpan⟩, ?_⟩
  rw [← sepConj_assoc] at hrest
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ Fr))) hrest

theorem overSepWPp_genP3_to_tailQpan_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {P Fr_tail R : SepProp}
    {Q : State → SepProp → Prop}
    (hpan : st.version = msgVer →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g)
    (hwp : SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2 P Q
      (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s2 P Q
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic
            y s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hnorm | ⟨hpanf, P_f, hmf, hgp⟩ | ⟨_, hoom⟩⟩ := hwp R' hm hL
  · exact ⟨sf, hsteps, Or.inl hnorm⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpanf, P_f, hmf, ?_⟩)⟩
    intro _ hmR; rw [← sepConj_assoc] at hmR
    exact dpPollOnPanic_of_modelPanic_budget_placed stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Budget-Threaded `try_decrypt` & `Prev1` Stage P3 Interfaces -/

abbrev overPollTryDecryptPlacedSpecP :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.pollTryDecryptPlacedSpecP

abbrev overPollTryDecryptPlacedSpecTPTight :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.pollTryDecryptPlacedSpecTPTight

/-- Budget-threaded `OverCliTryDecryptPqV1PlacedStmt` at Block `507` on `dpPollProgPlaced`. -/
def OverCliTryDecryptPqV1PlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (ctl : BitVec 64),
    CliGhostAllocHooks M A lim g →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) (tdEnv W)))

/-- Budget-threaded `StageP3Prev1VRegsAtPlacedStmt` over `RustCliAllocBudget M` and `PrevEncOK`,
eliminating `allocFailedIn` from `onPanic` (`genP3S5ModelPanicProp`). -/
def StageP3Prev1VRegsAtPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (st_b : M.σ),
    CliGhostAllocHooks M A lim g →
    AllocContractsXCliPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (Coins.coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          Over.overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (Coins.coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          Over.overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env VerNeTopEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (Coins.coinsAtPlaced cur rest) ∗
          Over.overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          Over.overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

abbrev StageP3Prev1VRegsPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  StageP3Prev1VRegsAtPlacedStmt A lim tdEnv Over.OverPrevEncOK

/-! ## 3. Budget-Threaded Stage P4 Continuation & Top-Level Path C Composition -/

set_option maxHeartbeats 800000 in
private theorem p4_finish_dpPollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s' sf : State) (evs : List AllocEvent)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (Pf outAt preKeyMsgRem coinsPost R : SepProp)
    (opkId? : Option (BitVec 32)) (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (ans : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (sess1 oneTime1 : DirGhost) (id1 : IdGhost) (kyber1 : KyberGhost)
    (g' : StoresGhost)
    (hevs : DecPkEnv y.g evs)
    (hs'_sp0 : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout_ent : outAt ⊢ decResAt A.repAlloc y.out ans ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sess1)
    (hsigned : g'.signed = StoresGhost.opened.signed)
    (honeTime : g'.oneTime = oneTime1)
    (hid : g'.identity = id1)
    (hkyber : g'.kyber = kyber1)
    (hpub : g'.pub = StoresGhost.opened.pub)
    (hpost_f : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents evs y.st) 0#64
      (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F pid (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey (cliKitStk B))
      s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut opkId?) outAt kpkId spkId pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey sess1 id1 oneTime1 kyber1)
    (hsteps0f : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 sf)
    (htr_sf : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' ans s0.trace sf.trace)
    (hm_f : sf.mem ⊨
      (Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y (s0.sp - 0xcd0#64) rngPtr whisperMsgPtr whisperG
        msgVer pid kpkId spkId preKeyMsgRem coinsPost) ∗
      ((memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
        memRegion y.cx 32) ∗ R)) :
    sf.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗
      R := by
  let sp := s0.sp - 0xcd0#64
  have hexit := stageP4PathCExitAt_entails_exit_placed A lim (M.stepEvents evs y.st) B y s0 s' sf
    rngPtr 8#64 whisperMsgPtr ptCap ptPtr whisperG outAt preKeyMsgRem coinsPost opkId? msgVer
    pid kpkId spkId pt ans sess1 oneTime1 id1 kyber1 g' hs'_sp0 hsp_sub hout_ent hmsg_fold
    hsess hid honeTime hsigned hkyber hpub
  dsimp only at hexit
  have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f)) hm_f
  have hm_f2 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f1
  have hm_f3 : sf.mem ⊨
      (decResAt A.repAlloc y.out ans ∗
        storesAt A.repAlloc y.g.stores g' ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        FromRecordCallees.lsLogOff ∗
        A.pool lim (M.stepEvents evs y.st) sf ∗
        (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
        dpFutDoneAt y.fut ∗
        memRegion y.cx 32 ∗
        memRegion sp 3280 ∗
        stackAt sp (dpClosSubStack B) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
    Arm64.Satisfies.mono (by sep_frame) hm_f2
  have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
    s0 sf evs g' ans (LsTokenInit ∗ coinsPost ∗ anyHeap) hevs
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
  exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f3

set_option maxHeartbeats 1200000 in
theorem closure_pathC_p4_cont_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP4 : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    (B : RunBudgets) (S : RunSem)
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (evs_pre : List AllocEvent)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r))
    (hcur : r.currentSession = some s_old)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
    (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
    (recG G₁ G' : SessionGhost)
    (rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (pt : List (BitVec 8))
    (s0 s2 s' : State)
    (hFits4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents evs_pre y.st)
        (StageP4Prev1Env prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber y.g.peer.val y.g.msg.identityKey
          m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 :
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
      let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
      let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
      let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      ∀ evs4,
        StageP4Prev1Env prev1Kit envs.opsEnv ikit envs.ikitEnv pkKit envs.pkKitEnv
          kpkKit envs.kpkKitEnv StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber y.g.peer.val y.g.msg.identityKey
          m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
        DecPkEnv y.g (evs_pre ++ evs4))
    (hpm_eq : y.g.msg = pmOfE m i)
    (hi : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys y.g.F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
      (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hex : SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hfiles2 : s2.fs.files = y.g.F)
    (htr2 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hver : (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
      (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s'
        y.fut y.out 8#64 prevCap prevPtr ptCap ptPtr
        (E2E.Record.encSession (Over.clearPending s_old)) pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗
      overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.msg.message.senderRatchetKey y.g.coins)) ∗
      Over.overScratch s2.sp) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
    let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    let Fr_tail : SepProp :=
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s' (P_s' ∗ F_p3)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me st0 y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let st_pre := M.stepEvents evs_pre y.st
  let A_s : RustAlloc := A.atState lim st_pre s'
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let prev1Kit := cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ
  let ops : Over.StorePrev1Ops prev1Kit := cliPollStorePrev1OpsPlaced
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ
  let enc := E2E.Record.encSession (Over.clearPending s_old)
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
  dsimp only at hFits4 hEnv4
  generalize hst'_eq :
    (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 = st' at hent_s'
  generalize hcoins_eq :
    Coins.coinsAfterPlaced y.g.coinsP y.g.coins
      (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins) = coinsPost at hent_s'
  let ses' : Session (List (BitVec 8)) :=
    { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
      state := st', pendingPreKey := none, pendingKyberPreKey := none }
  rw [hst'_eq] at hFits4 hEnv4
  have hok_pair : genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0 =
      (.ok pt, st') := Prod.ext hok hst'_eq
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := sp_frame_sub_add s0.sp
  have hf' : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps2' (htr'.trans htr2.symm)).trans hfiles2
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp4_64 : stageP4CallStack prev1Kit ikit pkKit kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4Prev1CallStack_le_subStack_placed A.repAlloc y.g.F y.g.peer pid m.kpkId m.spkId
        y.g.msg.baseKey B)
      hsub64
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPathC_entails_p4_placed A lim st_pre B y s0 s2 s' rngPtr 8#64 prevCap
    prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem coinsPost m.opkId
    (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId enc pt G' st'
    hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hp5f : overGenP3S5PostFrame_placed A.repAlloc = overGenP3S5PostFrame_placed A_s := rfl
  have hk1 : kit.storeAt = (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt := rfl
  have hk2 : ikit.identityAt = (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt := rfl
  have hk3 : pkKit.storeAt = (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt := rfl
  have hk4 : spkKit.storeAt = (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt := rfl
  have hk5 : kpkKit.storeAt =
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt := rfl
  have hk6 : dirAt A.repAlloc = dirAt A_s := rfl
  have hm1' : s'.mem ⊨
      (Over.stageP3DispatchOkMidPrev1Placed A_s s0 s2 y.fut y.out 8#64
          prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
        overGenP3S5PostFrame_placed A_s sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
          (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
          coinsPost ∗
        Over.overScratch s2.sp) ∗
      (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A_s y.g.F m.spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' := by
    unfold stageP3DispatchOkMidPrev1At_placed at hm1
    rw [hp5f, hk1, hk2, hk3, hk4, hk5, hk6] at hm1
    simpa only [hs2_sp, sepConj_assoc] using hm1
  have hp4_pre_eq :
      Over.stageP4Prev1PrePlaced 0#64
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey σ)
        s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' =
      stageP4Prev1PrePlaced A lim st_pre 0#64 prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' := rfl
  have hp4_rem_eq :
      overPathAP4RemAtPlaced A_s B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost =
      overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem
        coinsPost := rfl
  have hm2 : s'.mem ⊨
      stageP4Prev1PrePlaced A lim st_pre 0#64 prev1Kit ikit pkKit kpkKit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
        prevCap prevPtr ptCap ptPtr 8#64 m.opkId m.kpkId m.spkId 0#8 pt enc
        y.g.peer y.g.msg.identityKey y.g.msg.baseKey
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        G' st' ∗
      (overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost ∗
        R') := by
    rw [← sepConj_assoc] at hm1' ⊢
    rw [← hp4_pre_eq, ← hp4_rem_eq]
    exact Arm64.Satisfies.mono (sepConj_mono_left hmid) hm1'
  have hm_sess : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G' st' ∗ anyHeap := by
    refine Arm64.Satisfies.mono ?_ hm2
    unfold stageP4Prev1PrePlaced Over.stageP4Prev1PrePlaced Over.stageP4Prev1RawPrePlaced
    have hss_eq : sessionStateAt A_s = sessionStateAt A.repAlloc := rfl
    rw [hss_eq]
    have hcomm : ∀ A1 A2 S A3 A4 : SepProp,
        (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 ⊢ S ∗ anyHeap := fun A1 A2 S A3 A4 =>
      Entails.trans (Entails.of_eq (by ac_rfl : (A1 ∗ A2 ∗ S ∗ A3) ∗ A4 = S ∗ (A1 ∗ A2 ∗ A3 ∗ A4)))
        (sepConj_mono_right (entails_anyHeap _))
    exact hcomm _ _ _ _ _
  have hex0 : SessionExtraRel G'
      { pathAInitSession ⟨W.C, W.Q⟩ meE k m dk with
        state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
        pendingPreKey := none
        pendingKyberPreKey := none } := by
    rw [hst'_eq]; exact hex'
  have hm_sess0 : s'.mem ⊨ sessionStateAt A.repAlloc (y.fut + 0xf8#64) G'
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2 ∗ anyHeap := by
    rw [hst'_eq]; exact hm_sess
  have hrecOk : ops.RecPrev1Ok G' ses' enc := by
    have hr := pathC_recPrev1Ok_of_tryDecrypt_placed (A := A.repAlloc) (σ := σ)
      hs_old hdecOk hver hok hex0 hm_sess0
    dsimp only at hr
    rw [hst'_eq] at hr
    exact hr
  have hwp4 := hP4 mmpl g W B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey st_pre hh
    s0 s'
    y.fut y.cx y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
    prevCap prevPtr ptCap ptPtr 8#64
    m.opkId m.kpkId m.spkId 0#8 pt enc
    y.g.msg.identityKey y.g.msg.baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber
    G' ses'
    hFits4 hex' hrecOk rfl rfl
    (cliPollKpk_markOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    (cliPollPk_removeIdOk_of_pmOfE (A := A.repAlloc) 0#64 y.g.F m i σ hpm_eq)
    hpt_le hpt_lt hpt_ne hp4_64
    (cliPollStageP4Prev1_fsAt_placed A.repAlloc hh y.g.F y.g.peer pid m.kpkId m.spkId
      y.g.msg.baseKey σ hf')
    hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  have hpre_id : y.g.msg.preKeyId = m.opkId := hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).1
  have hspk_id : y.g.msg.signedPreKeyId = m.spkId :=
    hpm_eq ▸ (pmOfE_preKeyId_spkId_baseKey_eq m i).2.1
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_, _, _, hpan_false⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, evs4, hevs4, _hsave, hmark, _hrem, _hstore, htr_f, hpost_f⟩ |
      ⟨_evs4, _hevs4, hsave, _, _⟩ |
      ⟨c, e, evs4, hevs4, _hsave, hmark, htr_f, hpost_f⟩ |
      ⟨opkId, _c, e, _evs4, hopk, _hevs4, _hsave, _hmark, hrem, _, _⟩ |
      ⟨_c, _evs4, _hevs4, _hsave, _hmark, _hrem, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) :=
        hEnv4 evs4 (Or.inr (Or.inr (Or.inr hevs4)))
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          0#64 prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (vecResultAt A.repAlloc y.out (.ok pt)) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ())) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId <;> intro _ _ _ hp <;> exact hp
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.ok ()) = [] := rfl
        have h4 : ops.storeEvsPrev1 y.g.peer.val G' ses' enc (.ok ()) = [] := rfl
        revert hevs4 _hrem htr_f hpost_f
        cases m.opkId with
        | none =>
          intro _ _ htr_f _
          dsimp only at htr_f
          rw [h1, h2, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
        | some opkId =>
          intro _ _ htr_f _
          have h3 : pkKit.removeEvs opkId (.ok ()) = [] := rfl
          dsimp only at htr_f
          rw [h1, h2, h3, h4, List.append_nil, List.append_nil, List.append_nil,
            List.append_nil, htr'] at htr_f
          exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let kyber' := (kpkMarkOf cliIo.rd y.g.F StoresGhost.opened.kyber
        m.kpkId m.spkId y.g.msg.baseKey).2
      have hmark_eq : StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
          y.g.msg.signedPreKeyId y.g.msg.baseKey = (.ok (), kyber') := by
        rw [hspk_id]
        exact cliKpk_markRel_ok_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      obtain ⟨hDec, hWr⟩ :=
        decPkDefD2c_pathC_ok X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hfPeer hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
          hmark_eq
      let oneTime' := match y.g.msg.preKeyId with
        | none => StoresGhost.opened.oneTime
        | some j => (Cli.removePreKey cliIo.rd y.g.F StoresGhost.opened.oneTime j).2
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          kyber := kyber'
          oneTime := oneTime'
          sessions := StoresGhost.opened.sessions.put (Cli.addressText y.g.peer.val)
            (Over.encodeRecordPrev1 ses' enc) }
      have hot_eq : g'.oneTime =
          (match m.opkId with
           | none => StoresGhost.opened.oneTime
           | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ())) := by
        dsimp only [g', oneTime', pkKit, cliPollPkKitPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          cliPreKeyStoreSpec]
        rw [hpre_id]
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (vecResultAt A.repAlloc y.out (.ok pt)) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.ok pt)
        (ops.storeUpdatePrev1 StoresGhost.opened.sessions y.g.peer.val G' ses' enc (.ok ()))
        (match m.opkId with
         | none => StoresGhost.opened.oneTime
         | some opkId => pkKit.removeUpdate StoresGhost.opened.oneTime opkId (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.ok ()))
        g' hevs_tot hs'_sp0 hsp_sub (decResultAt_ok_entails_decResAt_anyHeap A.repAlloc y.out pt)
        hmsg_fold rfl rfl hot_eq rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_accept hS hDec hWr) hm_f
    · exact False.elim (cliId_saveRel_not_err (A := A.repAlloc) (b := 0#64)
        (F0 := y.g.F) (peer := y.g.peer) (σ := σ) hsave)
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have hevs_tot : DecPkEnv y.g (evs_pre ++ evs4) :=
        hEnv4 evs4 (Or.inr (Or.inl hevs4))
      have hpost_f' : Pf ⊢ stageP4Prev1ExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs4) y.st)
          0#64 prev1Kit ikit pkKit kpkKit s0 s' sf
          y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
          ptCap ptPtr 8#64 (coroOpkIdAtP4 y.fut m.opkId)
          (speErrAt kpkKit.markErr y.out e) m.kpkId m.spkId pt
          y.g.peer y.g.msg.identityKey y.g.msg.baseKey
          StoresGhost.opened.sessions
          (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
          StoresGhost.opened.oneTime
          (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey
            (.error e)) := by
        rw [M.stepEvents_append evs_pre evs4 y.st]; exact hpost_f
      have htr_sf : sf.trace = s0.trace := by
        have h1 : ikit.saveEvs y.g.peer.val y.g.msg.identityKey (.ok c) = [] := rfl
        have h2 : kpkKit.markEvs m.kpkId m.spkId y.g.msg.baseKey (.error e) = [] := rfl
        rw [h1, h2, List.append_nil, List.append_nil, htr'] at htr_f
        exact htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ overPathAP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      have hmark_err :
          (StoresGhost.opened.kyber.mark cliIo.rd y.g.F m.kpkId
            y.g.msg.signedPreKeyId y.g.msg.baseKey).1 = .error () := by
        rw [hspk_id]
        exact cliKpk_markRel_error_to_mark (A := A.repAlloc) (b := 0#64)
          (s1 := σ.kpkGetShim) (s2 := σ.kpkGetPoll) (s3 := σ.kpkMarkShim) (s4 := σ.kpkMarkPoll)
          hmark
      have hDec := decPkDefD2c_pathC_mark_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg
        y.g.coins hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hok_pair
        hmark_err
      let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val
            y.g.msg.identityKey (.ok c)
          kyber := kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId
            y.g.msg.baseKey (.error e) }
      exact p4_finish_dpPollPost_placed A lim DecPkEnv B S hh stk' hneed hstk63 y s0 s' sf
        (evs_pre ++ evs4) rngPtr whisperMsgPtr ptCap ptPtr whisperG Pf
        (speErrAt kpkKit.markErr y.out e) preKeyMsgRem coinsPost R
        m.opkId (y.g.msg.message.messageVersion.zeroExtend 32) pid m.kpkId m.spkId pt (.error err)
        StoresGhost.opened.sessions StoresGhost.opened.oneTime
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        (kpkKit.markUpdate StoresGhost.opened.kyber m.kpkId m.spkId y.g.msg.baseKey (.error e))
        g' hevs_tot hs'_sp0 hsp_sub
        (cliPollKpk_markErr_entails_decResAt_anyHeap A.repAlloc 0#64 y.g.F m.kpkId m.spkId
          y.g.msg.baseKey σ y.out e err)
        hmsg_fold rfl rfl rfl rfl rfl rfl hpost_f' hsteps0f htr_sf
        (slotOutTr_d2c_of_reject g' hS nofun nofun hDec) hm_f
    · exact False.elim (cliPk_removeRel_not_err_of_pkStoreKeys (A := A.repAlloc) (b := 0#64)
        (pid := pid) (σ := σ) (e := e) hk hopk hrem)
    · exact False.elim (by cases hstore)
  · exact False.elim hpan_false
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
theorem closure_pathC_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP2O : StageP2OverQpanCliPlacedStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1VRegsPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : OverCliTryDecryptPqV1PlacedStmt A lim tdEnv)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hFits2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hEnvErr2 : ∀ evs2, P2OverErrEnv y.g r evs2 → DecPkEnv y.g (evs_p1 ++ evs2))
    (hFits3 : ∀ evs2 m i k kp reg dk recG whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2) y.st)
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me whisperG y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32)
          (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins))
    (hEnvErr3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG G₁ whisperG,
      P2OverOkEnv y.g r evs2 →
      CloneRel recG G₁ →
      StageP3ErrEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hEnvVerNe3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG,
      P2OverOkEnv y.g r evs2 →
      StageP3VerNePrev1Env VerNeTopEnv recG
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        (E2E.Record.encSession (Over.clearPending s_old)) evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hFits4 : ∀ evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2 ++ evs3) y.st)
        (StageP4Prev1Env
          (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 : ∀ evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      StageP4Prev1Env
        (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
        (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4))
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let st_p1 := M.stepEvents evs_p1 y.st
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic
            y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let st_p1 := M.stepEvents evs_p1 y.st
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
    loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
  have hr_eq : r = ⟨some s_old⟩ := by cases r; simpa using hcur
  have hs_old : Slots.scopeIn ⟨some s_old⟩ := hr_eq ▸ hsub r (scope_of_loadRec_some hfPeer hloadS)
  have hver_old : s_old.state.sessionVersion = 4#32 := by
    have hv := hdecOk.sessVer4 r s_old hloadS hcur
    unfold SessionState.version at hv
    split at hv <;> simp_all
  have hprevOK : Over.OverPrevEncOK (E2E.Record.encSession (Over.clearPending s_old)) :=
    Over.overPrevEncOK_clearPending_of_scopeIn_placed hs_old hver_old
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 :=
    cliFsAt_of_files_eq_placed hh trivial rfl hs1_files
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (overSepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2O X mmpl g W B S Scope y st_p1 r s_old StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hFits2 hcoins hdecOk hsub hfPeer hloadS hcur hnot_match htrusted rfl
    hfiles1 hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs2, hevs2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hstep_eq : M.stepEvents evs2 st_p1 = M.stepEvents (evs_p1 ++ evs2) y.st :=
      (M.stepEvents_append evs_p1 evs2 y.st).symm
    rw [hstep_eq] at hm1
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_d2c_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
      s0 sf (evs_p1 ++ evs2) StoresGhost.opened (.error err) anyHeap (hEnvErr2 evs2 hevs2)
      (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 evs_p2 m i k kp reg dk recG prevCap prevPtr whisperMsgPtr whisperG preKeyMsgRem
      hevs2 hcap_nz hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ hx29_2 hvregs2 hro2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    let st_p2 := M.stepEvents (evs_p1 ++ evs_p2) y.st
    have hst_p2_eq : M.stepEvents evs_p2 st_p1 = st_p2 :=
      (M.stepEvents_append evs_p1 evs_p2 y.st).symm
    obtain ⟨_hIn0, hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDefD2c_pathC_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_p1) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
        LsTokenInit ∗
         overGenP3Pre_placed A lim st_p2 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         Over.overScratch s2.sp ∗
         F_p3 := by
      rw [hst_p2_eq, stageP3StackFrameAt_eq_over sp (y.g.msgA + 0xc8#64) y.g.peerA, hs2_sp]
      dsimp only [F_p3, sp]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (overSepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3O mmpl g W st_p2 hG
      hh.alloc (cliChainClone3_placed_ok mmpl g W hh) (cliSenderChainClone3_placed_ok mmpl g W hh)
      (hTry mmpl g W 0#64 hG)
      (cliDropSessionStructure4_placed_ok_at mmpl g W hh
        (callerProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 prevCap prevPtr y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8
      (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (hFits3 evs_p2 m i k kp reg dk recG whisperG hevs2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) hcap_nz hprevOK hver4
      (Or.inr (distinctSid_of_decPkOk₀ hdecOk.toDecPkOk₀_emptyScope)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot)
      (x29_eq_sp_add_c70_pathC_placed hx29_2 hs2_sp) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
        y.g.stores hsub hfPeer hdecOk pid m.spkId m.kpkId y.g.msg.baseKey
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathC_p4_cont_placed A lim DecPkEnv hP4O B S hh hS stk' hneed hstk63 y
          (evs_p1 ++ evs_p2 ++ evs_p3)
          hfPeer hs_old hdecOk hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
          rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          (hFits4 evs_p2 evs_p3 m i k kp reg dk recG G₁ G' pt whisperG
            hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok)
          (fun evs4 hevs4 =>
            hEnv4 evs_p2 evs_p3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok hevs4)
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s')
    · intro G₁ _G' evs_p3 e sf P_f hver hcl _hdec_rel hevs3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      have hent_any : P_f ⊢
          ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
          memRegion (s2.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st)
            s0 s2 sf y.fut y.out e ∗
          overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
              (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) ∗
          Over.overScratch s2.sp ∗
          anyHeap := by
        refine Entails.trans hent_f ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_emp (Over.overScratch s2.sp)).symm)
              (sepConj_mono_right (entails_anyHeap emp))))))
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnvErr3 evs_p2 evs_p3 m k kp reg dk recG G₁ whisperG hevs2 hcl hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_any hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnvVerNe3 evs_p2 evs_p3 m k kp reg dk recG hevs2 hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f


/-! ## `LibsignalFrozen` Counterparts -/

open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (
  VerNeTopEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverQpanCliFrozenPlacedStmt
)

def StageP3Prev1VRegsAtFrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) (st_b : M.σ),
    CliGhostAllocHooks M A lim g →
    AllocContractsXCliPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    ChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    SenderChainClone3OkPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) (tdEnv W))) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG st rem loc msgG msg msgVer enc rest) →
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1At_placed A lim (M.stepEvents evs_p3 st_b) s0 s s'
            coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt b_2c0 G'
            (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (Coins.coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          Over.overScratch s.sp) →
        SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (evs_p3 : List AllocEvent)
          (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv (tdEnv W) recG G₁ st rem loc msgG msg rest evs_p3 →
        (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf
            coroPtr outPtr e ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg
            (Coins.coinsAfterPlaced cur rest
              (decryptDraws W.C st msg.senderRatchetKey rest)) ∗
          Over.overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_p3 : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNePrev1Env VerNeTopEnv recG st enc evs_p3 →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents evs_p3 st_b) s0 s sf coroPtr
            outPtr (.invalidMessage .preKey .decryptionFailed) ∗
          overGenP3S5PostFrame_placed A.repAlloc s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr msgVer rem loc msgG msg (Coins.coinsAtPlaced cur rest) ∗
          Over.overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          overGenP3Pre_placed A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr
            locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            enc b_2c0 ∗
          Over.overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5ModelPanicProp W.C W.Q.K rem loc st msg msgVer rest s0)

abbrev StageP3Prev1VRegsFrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  StageP3Prev1VRegsAtFrozenPlacedStmt A lim tdEnv Over.OverPrevEncOK

set_option maxHeartbeats 1200000 in
theorem closure_pathC_frozen_placed_ok [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hP2O : StageP2OverQpanCliFrozenPlacedStmt A lim P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1VRegsFrozenPlacedStmt A lim tdEnv)
    (hP4O : StageP4Prev1VRegsPlacedStmt A lim p4Envs)
    (hTry : OverCliTryDecryptPqV1PlacedStmt A lim tdEnv)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hFits2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2OverEnv P2OverErrEnv P2OverOkEnv y.g r))
    (hEnvErr2 : ∀ evs2, P2OverErrEnv y.g r evs2 → DecPkEnv y.g (evs_p1 ++ evs2))
    (hFits3 : ∀ evs2 m i k kp reg dk recG whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2) y.st)
        (StageP3Prev1Env (tdEnv W) VerNeTopEnv recG
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
          y.g.peer y.g.me whisperG y.g.msg.message
          (y.g.msg.message.messageVersion.zeroExtend 32)
          (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins))
    (hEnvErr3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG G₁ whisperG,
      P2OverOkEnv y.g r evs2 →
      CloneRel recG G₁ →
      StageP3ErrEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hEnvVerNe3 : ∀ evs2 evs3 m k (kp : RecordCodecs.IdentityKeyPair) reg dk recG,
      P2OverOkEnv y.g r evs2 →
      StageP3VerNePrev1Env VerNeTopEnv recG
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        (E2E.Record.encSession (Over.clearPending s_old)) evs3 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3))
    (hFits4 : ∀ evs2 evs3 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      FitsEnv M lim (M.stepEvents (evs_p1 ++ evs2 ++ evs3) y.st)
        (StageP4Prev1Env
          (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
          (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
          (E2E.Record.encSession (Over.clearPending s_old))))
    (hEnv4 : ∀ evs2 evs3 evs4 m i k kp reg dk recG G₁ G' pt whisperG,
      P2OverOkEnv y.g r evs2 →
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      StageP3OkPrefixEnv (tdEnv W) recG G₁
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
        y.g.peer y.g.me whisperG y.g.msg.message y.g.coins evs3 →
      (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins
        (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt →
      let σ := cliKitStk B
      let pid := pmPreKeyId y.g.msg
      let envs := p4Envs B y.g.F y.g.peer pid m.kpkId m.spkId y.g.msg.baseKey
      let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
      let ses' : Session (List (BitVec 8)) :=
        { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).2
          pendingPreKey := none
          pendingKyberPreKey := none }
      StageP4Prev1Env
        (cliPollSessPrev1KitPlaced A.repAlloc y.g.F y.g.peer σ) envs.opsEnv
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ) envs.ikitEnv
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ) envs.pkKitEnv
        (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ) envs.kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        y.g.peer.val y.g.msg.identityKey m.kpkId m.spkId y.g.msg.baseKey m.opkId G' ses'
        (E2E.Record.encSession (Over.clearPending s_old)) evs4 →
      DecPkEnv y.g (evs_p1 ++ evs2 ++ evs3 ++ evs4))
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hnot_match : ¬ SessMatchesPm s_old y.g.msg)
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    let st_p1 := M.stepEvents evs_p1 y.st
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post
            y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic
            y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let st_p1 := M.stepEvents evs_p1 y.st
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
    loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
  have hr_eq : r = ⟨some s_old⟩ := by cases r; simpa using hcur
  have hs_old : Slots.scopeIn ⟨some s_old⟩ := hr_eq ▸ hsub r (scope_of_loadRec_some hfPeer hloadS)
  have hver_old : s_old.state.sessionVersion = 4#32 := by
    have hv := hdecOk.sessVer4 r s_old hloadS hcur
    unfold SessionState.version at hv
    split at hv <;> simp_all
  have hprevOK : Over.OverPrevEncOK (E2E.Record.encSession (Over.clearPending s_old)) :=
    Over.overPrevEncOK_clearPending_of_scopeIn_placed hs_old hver_old
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s1 :=
    cliFsAt_of_files_eq_placed hh trivial rfl hs1_files
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At (A.atState lim st_p1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split
    (overSepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2O X mmpl g W B S Scope y st_p1 r s_old StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hFits2 hcoins hdecOk hsub hfPeer hloadS hcur hnot_match htrusted rfl
    hfiles1 hfr1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, evs2, hevs2, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hstep_eq : M.stepEvents evs2 st_p1 = M.stepEvents (evs_p1 ++ evs2) y.st :=
      (M.stepEvents_append evs_p1 evs2 y.st).symm
    rw [hstep_eq] at hm1
    have hm2 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs2) y.st) sf ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_d2c_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := overExit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y
      s0 sf (evs_p1 ++ evs2) StoresGhost.opened (.error err) anyHeap (hEnvErr2 evs2 hevs2)
      (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518) hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 evs_p2 m i k kp reg dk recG prevCap prevPtr whisperMsgPtr whisperG preKeyMsgRem
      hevs2 hcap_nz hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ hx29_2 hvregs2 hfr2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    let st_p2 := M.stepEvents (evs_p1 ++ evs_p2) y.st
    have hst_p2_eq : M.stepEvents evs_p2 st_p1 = st_p2 :=
      (M.stepEvents_append evs_p1 evs_p2 y.st).symm
    obtain ⟨_hIn0, hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDefD2c_pathC_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        LsTokenInit ∗
         overGenP3Pre_placed A lim (M.stepEvents evs_p2 st_p1) s2.sp (s2.readReg64 .x29) y.fut
           y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
           (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
        LsTokenInit ∗
         overGenP3Pre_placed A lim st_p2 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG st0 y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         Over.stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap prevPtr
           (E2E.Record.encSession (Over.clearPending s_old)) 0#8 ∗
         Over.overScratch s2.sp ∗
         F_p3 := by
      rw [hst_p2_eq, stageP3StackFrameAt_eq_over sp (y.g.msgA + 0xc8#64) y.g.peerA, hs2_sp]
      dsimp only [F_p3, sp]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3
      (overSepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_)
    refine hP3O mmpl g W st_p2 hG
      hh.alloc (cliChainClone3_placed_ok mmpl g W hh) (cliSenderChainClone3_placed_ok mmpl g W hh)
      (hTry mmpl g W 0#64 hG)
      (cliDropSessionStructure4_placed_ok_at mmpl g W hh
        (callerProg := dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 prevCap prevPtr y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8
      (E2E.Record.encSession (Over.clearPending s_old)) y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (hFits3 evs_p2 m i k kp reg dk recG whisperG hevs2 hpm_eq hi hk hkp hreg hacc hex)
      (by decide) hcap_nz hprevOK hver4
      (Or.inr (distinctSid_of_decPkOk₀ hdecOk.toDecPkOk₀_emptyScope)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot)
      (x29_eq_sp_add_c70_pathC_placed hx29_2 hs2_sp) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs3 hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
        y.g.stores hsub hfPeer hdecOk pid m.spkId m.kpkId y.g.msg.baseKey
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathC_p4_cont_placed A lim DecPkEnv hP4O B S hh hS stk' hneed hstk63 y
          (evs_p1 ++ evs_p2 ++ evs_p3)
          hfPeer hs_old hdecOk hloadS hcur htrusted hnot_match m i k kp reg dk recG G₁ G'
          rngPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          (hFits4 evs_p2 evs_p3 m i k kp reg dk recG G₁ G' pt whisperG
            hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok)
          (fun evs4 hevs4 =>
            hEnv4 evs_p2 evs_p3 evs4 m i k kp reg dk recG G₁ G' pt whisperG
              hevs2 hpm_eq hi hk hkp hreg hacc hex hcl hdec_rel hevs3 hok hevs4)
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s')
    · intro G₁ _G' evs_p3 e sf P_f hver hcl _hdec_rel hevs3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      have hent_any : P_f ⊢
          ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
          memRegion (s2.sp + 0x3e0#64) 344 ∗
          overStageP3ErrPostPrevEmptyAt_placed A lim (M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st)
            s0 s2 sf y.fut y.out e ∗
          overGenP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
              (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins)) ∗
          Over.overScratch s2.sp ∗
          anyHeap := by
        refine Entails.trans hent_f ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right
            (Entails.trans (Entails.of_eq (sepConj_emp (Over.overScratch s2.sp)).symm)
              (sepConj_mono_right (entails_anyHeap emp))))))
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e
        (hEnvErr3 evs_p2 evs_p3 m k kp reg dk recG G₁ whisperG hevs2 hcl hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_any hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs3 hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      have hstep_p3_eq : M.stepEvents evs_p3 st_p2 = M.stepEvents (evs_p1 ++ evs_p2 ++ evs_p3) y.st :=
        (M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st).symm
      rw [hstep_p3_eq] at hent_f
      exact stageP3_exit_pathC_to_pollPost_placed A lim DecPkEnv B S hh hS stk' hneed hstk63 y
        s0 s2 sf (evs_p1 ++ evs_p2 ++ evs_p3) rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAtPlaced y.g.coinsP y.g.coins) P_f R m.opkId m.kpkId m.spkId
        (.invalidMessage .preKey .decryptionFailed)
        (hEnvVerNe3 evs_p2 evs_p3 m k kp reg dk recG hevs2 hevs3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDefD2c_pathC_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hnot_match hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
