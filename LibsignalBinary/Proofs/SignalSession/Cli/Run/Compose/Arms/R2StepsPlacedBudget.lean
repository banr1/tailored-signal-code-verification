/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonCalleesExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.Disproof.Basic

/-!
# Budget-Threaded `signal_session::run` Arm `R2` Shared Steps and Free Tails

Provides exact deallocation `AllocEvent` lists (`FreeOnlyEvs`), VM-preserving straight-line stepping
and budget-threaded call/dealloc combinators, and shared address-free cleanup tails for Arm `R2` on
Block `579` (`runProgPlaced H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (NoFsEv withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (LayoutOk vecU8)
open CryptoVerification.SignalSession (Inputs lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk inputOf namedWrites ownedBytes_dealloc ownedBytes_zero_entails_emp
   runResAt runResSize sepWPp_weaken_pre stackAt_split_ge storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtJoinPlaced AtRejectPlaced Bytes InRunPlaced RejectKind RunHistOk
   addrNameHeap joinMem r2_SlotWords r2_addrNameHeap_eq_ownedBytes
   r2_ans_of_trace_eq r2_hold r2_hold_eq r2_localGaps r2_locals_join_eq
   r2_locals_none_eq r2_peerSlot_rejoin
   r2p_CodeOk r2p_cs_regs r2p_histOk_of_trace_files r2p_inRun_mk r2p_vregs_0 r2p_vregs_1
   r2p_vregs_2 rejectMem runFsp runLocals runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   VmPreserved rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro r3b_dealloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff r2_hold
attribute [local arm64_norm, local wp_norm]
  ProofLib.bv_sub_add_lit BitVec.toNat_zero r2p_vregs_0 r2p_vregs_1 r2p_vregs_2

/-! ## 1. Exact Deallocation Event Lists & `FreeOnlyEvs` Witnesses -/

def r2pbFreeCapEvs (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

def r2pbFreePeerEvs (peerG : AddrGhost) : List AllocEvent :=
  r2pbFreeCapEvs peerG.name.cap

def r2pbFreeMePeerEvs (meG peerG : AddrGhost) : List AllocEvent :=
  r2pbFreeCapEvs meG.name.cap ++ r2pbFreeCapEvs peerG.name.cap

def r2pbFreeSliceEvs (len : BitVec 64) : List AllocEvent :=
  if len = 0#64 then [] else rustDeallocEvents len.toNat 1

def r2pbFreeOptSliceEvs (ptr len : BitVec 64) : List AllocEvent :=
  if ptr = 0#64 then [] else r2pbFreeSliceEvs len

def r2pbSigFree3Evs (ws : r2_SlotWords) : List AllocEvent :=
  r2pbFreeSliceEvs ws.w5 ++ r2pbFreeSliceEvs ws.w1 ++ r2pbFreeOptSliceEvs ws.w12 ws.w13

def r2pbSigFreeEvs (ws : r2_SlotWords) (serLen : BitVec 64) : List AllocEvent :=
  r2pbSigFree3Evs ws ++ r2pbFreeSliceEvs serLen

theorem r2pbFreeCapEvs_freeOnly (cap : BitVec 64) : FreeOnlyEvs (r2pbFreeCapEvs cap) := by
  unfold r2pbFreeCapEvs
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

theorem r2pbFreePeerEvs_freeOnly (peerG : AddrGhost) : FreeOnlyEvs (r2pbFreePeerEvs peerG) :=
  r2pbFreeCapEvs_freeOnly peerG.name.cap

theorem r2pbFreeMePeerEvs_freeOnly (meG peerG : AddrGhost) :
    FreeOnlyEvs (r2pbFreeMePeerEvs meG peerG) :=
  FreeOnlyEvs.append (r2pbFreeCapEvs_freeOnly meG.name.cap) (r2pbFreeCapEvs_freeOnly peerG.name.cap)

theorem r2pbFreeSliceEvs_freeOnly (len : BitVec 64) : FreeOnlyEvs (r2pbFreeSliceEvs len) := by
  unfold r2pbFreeSliceEvs
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 len.toNat

theorem r2pbFreeOptSliceEvs_freeOnly (ptr len : BitVec 64) :
    FreeOnlyEvs (r2pbFreeOptSliceEvs ptr len) := by
  unfold r2pbFreeOptSliceEvs
  split
  · exact FreeOnlyEvs.nil
  · exact r2pbFreeSliceEvs_freeOnly len

theorem r2pbSigFree3Evs_freeOnly (ws : r2_SlotWords) : FreeOnlyEvs (r2pbSigFree3Evs ws) :=
  FreeOnlyEvs.append
    (FreeOnlyEvs.append (r2pbFreeSliceEvs_freeOnly ws.w5) (r2pbFreeSliceEvs_freeOnly ws.w1))
    (r2pbFreeOptSliceEvs_freeOnly ws.w12 ws.w13)

theorem r2pbSigFreeEvs_freeOnly (ws : r2_SlotWords) (serLen : BitVec 64) :
    FreeOnlyEvs (r2pbSigFreeEvs ws serLen) :=
  FreeOnlyEvs.append (r2pbSigFree3Evs_freeOnly ws) (r2pbFreeSliceEvs_freeOnly serLen)

theorem r2pb_freeOnlyEvs_of_forall :
    ∀ {evs : List AllocEvent}, (∀ ev ∈ evs, ∃ al sz, ev = .free al sz) → FreeOnlyEvs evs
  | [], _ => FreeOnlyEvs.nil
  | ev :: tl, h => by
    obtain ⟨al, sz, rfl⟩ := h ev List.mem_cons_self
    exact FreeOnlyEvs.append (FreeOnlyEvs.singleton al sz)
      (r2pb_freeOnlyEvs_of_forall fun e he => h e (List.mem_cons_of_mem _ he))

/-! ## 2. VM-Preserving Sequencer, Peeling, and Budget Call Combinators -/

def r2pb_stOf [LibsignalPlacement] {sm : State} (_ : r2p_CodeOk sm.mem) : State := sm

theorem r2pb_sepWP_with_vm_oom {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} {mid : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hPm, hvm, hp⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved (Hk := Hk) h) hm hL
  · exact ⟨sm, hsteps, Or.inl ⟨hpc, hrun, Pm, hPm, hp hvm⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply r2pb_sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn
        #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

theorem r2pb_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : r2p_CodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      r2p_CodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

theorem r2pb_sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x : α, P x) Q Qp oom := by
  intro R hm hL; rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hm⟩ := hm; exact h x R hm hL

class R2pbPeel (P : SepProp) (α : outParam Type) (R : outParam (α → SepProp)) : Prop where
  entails : P ⊢ ∃∗ x : α, R x
instance (priority := 100) {α : Type} {P : α → SepProp} : R2pbPeel (∃∗ x : α, P x) α P :=
  ⟨Entails.refl _⟩
instance (priority := 90) {α : Type} {A B : SepProp} {R : α → SepProp} [h : R2pbPeel A α R] :
    R2pbPeel (A ∗ B) α (fun x => R x ∗ B) :=
  ⟨by rw [← sepExists_sepConj_left]; exact sepConj_mono_left h.entails⟩
instance (priority := 80) {α : Type} {A B : SepProp} {R : α → SepProp} [h : R2pbPeel B α R] :
    R2pbPeel (A ∗ B) α (fun x => A ∗ R x) :=
  ⟨by rw [← sepExists_sepConj_right]; exact sepConj_mono_right h.entails⟩

theorem r2pb_peel_tc {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {R : α → SepProp} [h : R2pbPeel P α R]
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : ∀ x : α, SepWPp prog ret s (R x) Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (r2pb_sepWPp_exists_left k)

class R2pbPeelPure (P : SepProp) (φ : outParam Prop) (R : outParam SepProp) : Prop where
  entails : P ⊢ ⌜φ⌝ ∗ R
instance (priority := 100) {φ : Prop} : R2pbPeelPure ⌜φ⌝ φ emp :=
  ⟨Entails.of_eq (sepConj_emp _).symm⟩
instance (priority := 90) {φ : Prop} {A B R : SepProp} [h : R2pbPeelPure A φ R] :
    R2pbPeelPure (A ∗ B) φ (R ∗ B) :=
  ⟨Entails.trans (sepConj_mono_left h.entails) (Entails.of_eq (sepConj_assoc _ _ _))⟩
instance (priority := 80) {φ : Prop} {A B R : SepProp} [h : R2pbPeelPure B φ R] :
    R2pbPeelPure (A ∗ B) φ (A ∗ R) :=
  ⟨Entails.trans (sepConj_mono_right h.entails) (Entails.of_eq (sepConj_left_comm _ _ _))⟩

theorem r2pb_peel_pure_tc {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} [h : R2pbPeelPure P φ R]
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (k : φ → SepWPp prog ret s R Q Qp oom) : SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre h.entails (SepWPp.pure_left k)

scoped macro "r2pb_pc_done" : tactic => `(tactic| (
  try dsimp only [r2pb_stOf, runPcPlaced]
  try simp only [wp_norm, arm64_norm, runPcPlaced_eq, BitVec.add_assoc, BitVec.reduceAdd]
  try rfl))

scoped macro "r2pb_eq" : tactic => `(tactic| (
  try dsimp only [r2pb_stOf]
  try simp only [wp_norm, arm64_norm]
  try rfl))

scoped macro "r2pb_cond" : tactic => `(tactic| first
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32])
  | (simp only [arm64_norm, conditionHolds_mi_subsPState64, conditionHolds_pl_subsPState64,
        conditionHolds_mi_addsPState64, conditionHolds_pl_addsPState64,
        conditionHolds_mi_subsPState32, conditionHolds_pl_subsPState32,
        conditionHolds_mi_addsPState32, conditionHolds_pl_addsPState32]
     decide))

theorem r2pb_rejectMem_atState_postDispatch_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (g' : StoresGhost) (s0 : State) (resStack : Nat) :
    rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack =
      runLocals (runFsp s0) [] ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s ∗ anyHeap) := by
  have hlive :
      rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack =
        rejectMem { pool := A.pool lim st s, live := A.repAlloc.live }
          g g' .postDispatch s0 resStack := rfl
  rw [hlive]
  dsimp only [rejectMem]
  change _ =
    runLocals (runFsp s0) [] ∗
      (runResAt { pool := A.pool lim st s, live := A.repAlloc.live } cliWrOk g.res (some none) ∗
        memRegion g.call 56 ∗
        storesAt { pool := A.pool lim st s, live := A.repAlloc.live } g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
  sep_ac_rfl

theorem r2pb_joinMem_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (g' : StoresGhost) (out : Bytes) (s0 : State) (resStack : Nat) :
    joinMem (A.atState lim st s) g g' out s0 resStack =
      runLocals (runFsp s0) [(0x208, 24, vecU8 A.repAlloc (runFsp s0 + 0x208#64) out)] ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s ∗ anyHeap) := by
  have hlive :
      joinMem (A.atState lim st s) g g' out s0 resStack =
        joinMem { pool := A.pool lim st s, live := A.repAlloc.live }
          g g' out s0 resStack := rfl
  rw [hlive]
  dsimp only [joinMem]
  change _ =
    runLocals (runFsp s0)
      [(0x208, 24, vecU8 { pool := A.pool lim st s, live := A.repAlloc.live }
        (runFsp s0 + 0x208#64) out)] ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt { pool := A.pool lim st s, live := A.repAlloc.live } g.stores g' ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap)
  sep_ac_rfl

theorem r2pb_files_of_trace_eq [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {s sf : State} (hh : RunHooksPlaced A lim H)
    (hsteps : Steps (runProgPlaced H) s sf) (htr : sf.trace = s.trace) :
    sf.fs.files = s.fs.files :=
  (hh.fs (runProgPlaced H) 579).files_eq hsteps (htr.trans (List.append_nil _).symm) NoFsEv.nil

theorem r2pb_call [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {callee_pc ret_pc ret : BitVec 64} {spec : Spec α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (x : α)
    (hcall : subroutine_ok (runProgPlaced H) callee_pc (withLsCodeRoLoaded lsmpl spec))
    (hinv : r2p_CodeOk s.mem) (hpc : s.pc = callee_pc) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
        Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') →
        False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
        (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State, Steps (runProgPlaced H) s sf → r2p_CodeOk sf.mem →
        sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
        SepWPp (runProgPlaced H) ret sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp (runProgPlaced H) ret s P Q Qp oom :=
  r3b_call_lscro x hcall hinv hpc hrun hsp hlr hP hpanic hexit hoom hnext

theorem r2pb_call_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {i : Inputs} {s0 sRef s : State} {refOff nextOff sub : Nat} {ptr sz : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hextNeed : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (href : InRunPlaced r2p_CodeOk s0 sRef refOff)
    (hinv : r2p_CodeOk s.mem) (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hsp : s.sp = sRef.sp)
    (hfp : s.readReg64 .fp = sRef.readReg64 .fp)
    (hv : calleeSavedVRegs s = calleeSavedVRegs sRef)
    (hlr : s.readReg64 .lr = runPcPlaced nextOff)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = sz)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hpos : 0 < sz.toNat) (hlt : sz.toNat < 2 ^ 63)
    (htr : s0.trace <+: s.trace) (hhist : RunHistOk i s0 s)
    (hnext : ∀ sf : State,
      sf.trace = s.trace →
      InRunPlaced r2p_CodeOk s0 sf nextOff →
      CalleeSavedPreserved s sf →
      s0.trace <+: sf.trace →
      RunHistOk i s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (A.pool lim (M.stepEvents (rustDeallocEvents sz.toNat 1) st) sf ∗
          stackAt (runFsp s0) sub ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 (runPcPlaced nextOff) := by
      first
      | assumption
      | simp (config := { decide := true })
          [runPcPlaced, wp_norm, arm64_norm, LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsLen, *]) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat ∗
        A.pool lim st s ∗ stackAt (runFsp s0) sub ∗ F) Q Qp oom := by
  have hda := r3b_dealloc_ok hh
  have hlay : LayoutOk sz.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  have hsp_eq : s.sp = runFsp s0 := hsp.trans href.sp
  have hsp_al : s.spAligned = true := by
    have hr := href.spAligned_cur
    simpa only [State.spAligned, hsp] using hr
  have hsp_split := stackAt_split_ge (runFsp s0) hextNeed hsub64
  rw [hsp_split]
  refine r2pb_call (ptr, sz.toNat, 1, st) hda hinv hpc hrun hsp_al hlr
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F) ?_
    (hnext := fun sf _ hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [Spec.keepsFs,
      rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [hsp_eq]; simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, by simp [hx1], by simp [hx2], ⟨hlay, by decide⟩, hlr ▸ hlr_ls⟩
      (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [Spec.keepsFs,
      rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hfs_f => SepWPp.pure_left fun htr_f => ?_
    have hcs := r2p_cs_regs hcsm
    have hin_f : InRunPlaced r2p_CodeOk s0 sf nextOff :=
      r2p_inRun_mk href hpcm hrunm (hspm.trans hsp)
        (hcs.2.2.2.2.2.2.2.2.2.2.1.trans hfp) hinv_f
        (hcs.2.2.2.2.2.2.2.2.2.2.2.trans hv)
    have htr_sf : s0.trace <+: sf.trace := htr_f ▸ htr
    have hhist_sf : RunHistOk i s0 sf :=
      r2p_histOk_of_trace_files hhist htr_f (congrArg FsState.files hfs_f)
    refine sepWPp_weaken_pre ?_ (hnext sf htr_f hin_f hcsm htr_sf hhist_sf)
    rw [hsp_eq]
    have hmerge :
        A.pool lim (M.stepEvents (rustDeallocEvents sz.toNat 1) st) sf ∗
          (stackAt (runFsp s0) extHookStack ∗
            (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗ F)) =
        A.pool lim (M.stepEvents (rustDeallocEvents sz.toNat 1) st) sf ∗
          (memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack) ∗
            stackAt (runFsp s0) extHookStack) ∗ F := by sep_ac_rfl
    rw [hmerge, hsp_split.symm]; exact Entails.refl _

/-! ## 3. Shared Cleanup Tails (`r2pb_free_peer_*`, `r2pb_free_me_peer_join`) -/

set_option maxHeartbeats 800000 in
theorem r2pb_free_peer_reject [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG : AddrGhost} {g' : StoresGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 2984)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r2pbFreePeerEvs peerG) st))
    (hrej : RejectKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let restPeer (sPool : State) : SepProp :=
    runSaved s0 ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st sPool ∗ anyHeap
  let peerRest (stCur : M.σ) (sPool : State) : SepProp :=
    runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim stCur sPool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restPeer s)
    (by dsimp only [restPeer]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A.repAlloc peerG]
  have hpc : s.pc = runPcPlaced 2984 := hin.pc; change s.pc = (blkPl_579).base + 2984#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch st := by
      simpa [r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv
    rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A.repAlloc _ _ _)))))) ?_
    rw [emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 11388) hin.inv
    rw [← r2_hold_eq (restPeer s), ← hsp0, runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hsp0, r2_hold_eq]
      dsimp only [restPeer]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 11388 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hatRej : AtRejectPlaced r2p_CodeOk g g' .postDispatch s0 (r2pb_stOf hinv1) :=
        { base := hin1
          x19 := by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19
          preRegs := fun h => by cases h
          trace := by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr
          hist := r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)
          ans := hans }
      refine sepWPp_weaken_pre ?_ (hrej (r2pb_stOf hinv1) st g' .postDispatch hatRej henv0)
      rw [r2pb_rejectMem_atState_postDispatch_eq, r2_locals_none_eq fsp]
      have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
      refine Entails.trans (Entails.of_eq ?_)
        (Entails.trans (sepConj_mono_left (Q := peerRest st (r2pb_stOf hinv1)) hp32)
          (Entails.of_eq ?_))
      · dsimp only [peerRest, fsp]; sep_ac_rfl
      · dsimp only [peerRest, fsp]; sep_ac_rfl
    )
  · have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap)))))) ?_
    have hpull :
        runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restPeer s =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ restPeer s)) := by
      dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← r2_hold_eq (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗ _), ← hsp0]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hsp0, r2_hold_eq]
      dsimp only [restPeer]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      refine sepWPp_weaken_pre
        (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          A.pool lim st (r2pb_stOf hinv1) ∗ stackAt fsp (resStack - runFrame) ∗
          (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
            (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
        (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_call_dealloc (nextOff := 11388) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) hpos hlt63
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hatRej : AtRejectPlaced r2p_CodeOk g g' .postDispatch s0 sf :=
        { base := hin_f
          x19 := by
            rw [(r2p_cs_regs hcsm).1]
            dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19
          preRegs := fun h => by cases h
          trace := htr_f
          hist := hhist_f
          ans := r2_ans_of_trace_eq (htr_eq.trans (by r2pb_eq)) hans }
      refine sepWPp_weaken_pre ?_
        (hrej sf (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' .postDispatch hatRej henv1)
      rw [r2pb_rejectMem_atState_postDispatch_eq, r2_locals_none_eq fsp]
      have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
      dsimp only [fsp] at hp32
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
      refine Entails.trans (Entails.of_eq ?_)
        (Entails.trans
          (sepConj_mono_left
            (Q := peerRest (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sf) hp32)
          (Entails.of_eq ?_))
      · dsimp only [peerRest, fsp]; sep_ac_rfl
      · dsimp only [peerRest, fsp]; sep_ac_rfl
    )

set_option maxHeartbeats 800000 in
theorem r2pb_free_peer_join [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG : AddrGhost} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 3960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' out (M.stepEvents (r2pbFreePeerEvs peerG) st))
    (hjoin : JoinKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let restJoin (sPool : State) : SepProp :=
    runSaved s0 ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st sPool ∗ anyHeap
  let joinRest (stCur : M.σ) (sPool : State) : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim stCur sPool ∗ anyHeap
  refine sepWPp_weaken_pre
    (P' := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
      restJoin s)
    (by dsimp only [restJoin]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  rw [r2_addrNameHeap_eq_ownedBytes A.repAlloc peerG]
  have hpc : s.pc = runPcPlaced 3960 := hin.pc; change s.pc = (blkPl_579).base + 3960#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' out st := by
      simpa [r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv
    rw [hcap]
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ownedBytes_zero_entails_emp A.repAlloc _ _ _)))))) ?_
    rw [emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 3980) hin.inv
    rw [← r2_hold_eq (restJoin s), ← hsp0, runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hsp0, r2_hold_eq]
      dsimp only [restJoin]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 3980 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      have hatJoin : AtJoinPlaced r2p_CodeOk g g' out s0 (r2pb_stOf hinv1) :=
        { base := hin1
          x19 := by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19
          x20 := by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20
          trace := by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr
          hist := r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq)
          ans := hans
          wrOk := hwr }
      refine sepWPp_weaken_pre ?_ (hjoin (r2pb_stOf hinv1) st g' out hatJoin henv0)
      rw [r2pb_joinMem_atState_eq, r2_locals_join_eq fsp (vecU8 A.repAlloc (fsp + 0x208#64) out)]
      have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) 0#64 peerG.name.ptr
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
      refine Entails.trans (Entails.of_eq ?_)
        (Entails.trans (sepConj_mono_left (Q := joinRest st (r2pb_stOf hinv1)) hp32)
          (Entails.of_eq ?_))
      · dsimp only [joinRest, fsp]; sep_ac_rfl
      · dsimp only [joinRest, fsp]; sep_ac_rfl
    )
  · have henv1 : EnvAt g' out
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv
    refine sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap)))))) ?_
    have hpull :
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗ A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
            memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
          ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
          restJoin s =
        ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
            (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
              memRegion peerG.name.ptr peerG.name.cap.toNat ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ restJoin s)) := by
      dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
    rw [hpull]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : peerG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← r2_hold_eq (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗ _), ← hsp0]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [hsp0, r2_hold_eq]
      dsimp only [restJoin]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      refine sepWPp_weaken_pre
        (P' := A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          A.pool lim st (r2pb_stOf hinv1) ∗ stackAt fsp (resStack - runFrame) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
            (((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16) ∗
            memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
            vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
            memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
            memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap))
        (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine r2pb_call_dealloc (nextOff := 3980) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) hpos hlt63
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcs := r2p_cs_regs hcsm
      have hatJoin : AtJoinPlaced r2p_CodeOk g g' out s0 sf :=
        { base := hin_f
          x19 := by rw [hcs.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19
          x20 := by rw [hcs.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20
          trace := htr_f
          hist := hhist_f
          ans := r2_ans_of_trace_eq (htr_eq.trans (by r2pb_eq)) hans
          wrOk := hwr }
      refine sepWPp_weaken_pre ?_
        (hjoin sf (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' out hatJoin henv1)
      rw [r2pb_joinMem_atState_eq, r2_locals_join_eq fsp (vecU8 A.repAlloc (fsp + 0x208#64) out)]
      have hp32 := r2_peerSlot_rejoin (fsp + 0x320#64) peerG.name.cap peerG.name.ptr
      dsimp only [fsp] at hp32
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp32)
      refine Entails.trans (Entails.of_eq ?_)
        (Entails.trans
          (sepConj_mono_left
            (Q := joinRest (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sf) hp32)
          (Entails.of_eq ?_))
      · dsimp only [joinRest, fsp]; sep_ac_rfl
      · dsimp only [joinRest, fsp]; sep_ac_rfl
    )

set_option maxHeartbeats 800000 in
theorem r2pb_free_me_peer_join [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {g' : StoresGhost} {out : Bytes}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hextNeed : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hin : InRunPlaced r2p_CodeOk s0 s 3940)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, out)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' out (M.stepEvents (r2pbFreeMePeerEvs meG peerG) st))
    (hjoin : JoinKPlacedEnv r2p_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x330#64) 16 ∗
        memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
        vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
        memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
        memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  let tailMeJoin (stCur : M.σ) (sPool : State) : SepProp :=
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
      ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
      ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
      vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
      memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
      memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim stCur sPool ∗ anyHeap
  change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
    (addrNameHeap A.repAlloc meG ∗ tailMeJoin st s) Q Qp oom
  rw [r2_addrNameHeap_eq_ownedBytes A.repAlloc meG]
  have hpc : s.pc = runPcPlaced 3940 := hin.pc; change s.pc = (blkPl_579).base + 3940#64 at hpc
  have hrun0 : s.status = .Running := hin.run
  have hsp0 : s.sp = fsp := hin.sp
  have hsp_al : s.spAligned = true := hin.spAligned_cur
  by_cases hcap : meG.name.cap = 0#64
  · have henv0 : EnvAt g' out (M.stepEvents (r2pbFreePeerEvs peerG) st) := by
      simpa [r2pbFreeMePeerEvs, r2pbFreePeerEvs, r2pbFreeCapEvs, hcap] using henv
    rw [hcap]
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_zero_entails_emp A.repAlloc _ _ _)) ?_
    rw [emp_sepConj]
    apply r2pb_seq_lscro_oom (mid := runPcPlaced 3960) hin.inv
    have hx21_0 : s.readReg64 (.gpr 21#5) = 0#64 := hx21.trans hcap
    rw [← r2_hold_eq (tailMeJoin st s), runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [r2_hold_eq]
      dsimp only [tailMeJoin]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hin1 : InRunPlaced r2p_CodeOk s0 (r2pb_stOf hinv1) 3960 :=
        r2p_inRun_mk hin (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
          (by r2pb_eq) (by r2pb_eq) hinv1 (by r2pb_eq)
      exact r2pb_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin1
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20)
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        hans hwr henv0 hjoin
    )
  · have henv1 : EnvAt g' out
        (M.stepEvents (r2pbFreePeerEvs peerG)
          (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st)) := by
      simpa [r2pbFreeMePeerEvs, r2pbFreePeerEvs, r2pbFreeCapEvs, hcap,
        AllocCostModel.stepEvents_append] using henv
    refine sepWPp_weaken_pre (sepConj_mono_left (ownedBytes_dealloc A.repAlloc hcap)) ?_
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWPp.pure_left; rintro ⟨hpos, _, hlt⟩
    have hlt63 : meG.name.cap.toNat < 2 ^ 63 := by omega
    have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hx21_b : (s.readReg64 (.gpr 21#5) == 0#64) = false := hx21.symm ▸ hbeq
    apply r2pb_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hin.inv
    rw [← r2_hold_eq (A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗ _)]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by r2pb_pc_done) (by simp only [wp_norm, arm64_norm, hrun0])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
      change SepWPp (runProgPlaced H) _ (r2pb_stOf hinv1) _ _ _ _
      rw [r2_hold_eq]
      dsimp only [tailMeJoin, RustCliAllocBudget.repAlloc]
      rw [← A.pool_transport lim st s (r2pb_stOf hinv1) hvm]
      have hreord :
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            (memRegion meG.name.ptr meG.name.cap.toNat ∗
              (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt { pool := emp, live := A.live } g.stores g' ∗
                (g.inp ↦ₛ inputOf g.i g.c) ∗
                addrNameHeap { pool := emp, live := A.live } peerG ∗ runSaved s0 ∗
                ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x330#64) 16 ∗
                memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
                vecU8 { pool := emp, live := A.live } (fsp + 0x208#64) out ∗
                memRegion (fsp + 0x2a0#64) 8 ∗
                memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
                memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗
                stackAt fsp (resStack - runFrame) ∗
                A.pool lim st (r2pb_stOf hinv1) ∗ anyHeap)) =
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
            memRegion meG.name.ptr meG.name.cap.toNat ∗
            A.pool lim st (r2pb_stOf hinv1) ∗ stackAt fsp (resStack - runFrame) ∗
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) := by
        dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl
      rw [hreord]
      refine r2pb_call_dealloc (nextOff := 3960) hh hextNeed hsub64 hin hinv1
        (by r2pb_pc_done) (by simp only [r2pb_stOf, wp_norm, arm64_norm, hrun0])
        (by r2pb_eq) (by r2pb_eq) (by r2pb_eq) (by r2pb_pc_done)
        (by dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm, hx28])
        (by dsimp only [r2pb_stOf]; simp only [wp_norm, arm64_norm, hx21])
        (by r2pb_eq) hpos hlt63
        (by dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact htr)
        (r2p_histOk_of_trace_files hhist (by r2pb_eq) (by r2pb_eq))
        fun sf htr_eq hin_f hcsm htr_f hhist_f => ?_
      have hcs := r2p_cs_regs hcsm
      have hback :
          A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sf ∗
            stackAt fsp (resStack - runFrame) ∗
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              ((fsp + 0x320#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x328#64) ↦₆₄ peerG.name.ptr) ∗
              memRegion (fsp + 0x330#64) 16 ∗
              memRegion fsp 16 ∗ memRegion (fsp + 0x1d0#64) 16 ∗
              vecU8 A.repAlloc (fsp + 0x208#64) out ∗ memRegion (fsp + 0x2a0#64) 8 ∗
              memRegion (fsp + 0x4d0#64) 248 ∗ memRegion (fsp + 0x1750#64) 248 ∗
              memRegion (fsp + 0x23b0#64) 32 ∗ r2_localGaps fsp ∗ anyHeap) ⊢
          tailMeJoin (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sf := by
        dsimp only [tailMeJoin]; exact Entails.of_eq (by sep_ac_rfl)
      exact sepWPp_weaken_pre hback
        (r2pb_free_peer_join (peerG := peerG) hh hextNeed hsub64 hin_f
          (by rw [hcs.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx19)
          (by rw [hcs.2.1]; dsimp only [r2pb_stOf]; (try simp only [wp_norm, arm64_norm]); exact hx20)
          htr_f hhist_f
          (r2_ans_of_trace_eq (htr_eq.trans (by r2pb_eq)) hans)
          hwr henv1 hjoin)
    )


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2StepsPlacedBudget
