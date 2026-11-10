/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R3b`: Bad-Wire and Reject Sub-Hop

Proves `run_hop_recvBad_placed_ok` (`RunHopRecvBadPlaced`) and shared `Recv` dispatch-head /
reject-cleanup lemmas (including `CodeOk`-parametric variants) on Block `579` (`runProgPlaced H`)
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost noneCap uuidTryParse)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall addrWords callAt callHeap cliWrOk coinsInstalledPlaced inputOf ownedBytes parseArgs runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (AtDispatchPlaced AtRejectPlaced AtRunEntryPlaced InRunPlaced MeAtDispatch R3bCodeOk RejectKind RunHistOk RunLocalsFromWf RunNeeds RunSem addrNameHeap addrUpperAt addrValOf dispatchCells dispatchMeHeap r3b_addrNameHeap_dev_congr r3b_addrUpperAt_words r3b_call7_to_memRegion56 r3b_hist_of_eq r3b_inRun_step r3b_mem32_to_words4 r3b_memRegion_to_runLocalsFrom r3b_nameHeap_cap_ne_neg1 r3b_nameHeap_dealloc r3b_nameHeap_zero r3b_ownedBytes_entails_nameHeap r3b_perm r3b_perm_post r3b_pure1 r3b_pure2 r3b_sepWPp_exists_left r3b_sepWPp_pure_left r3b_sepWPp_weaken_pre r3b_stOf r3b_stackAt_split_ge r3b_words4_entails_mem32 rejectMem runFsp runLocalBytes runLocals runLocalsFrom runLocals_rejoin_empty runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   VmPreserved rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro r3b_dealloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
  (RunHopRecvBadPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (RejectKPlaced RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced runNeed_bounds_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

/-! ## 1. Exact Deallocation Event Lists & VM-Preserving Sequencer -/

/-- Exact deallocation event list for dropping an `AddrGhost` name buffer with capacity `cap`
(`align = 1`). -/
def r3bFreeCapEvs (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

/-- Exact deallocation event list for `r3b_reject_from_fec_placed` (`meG.name` then `peerG.name`). -/
def r3bFreeMePeerEvs (meG peerG : AddrGhost) : List AllocEvent :=
  r3bFreeCapEvs meG.name.cap ++ r3bFreeCapEvs peerG.name.cap

theorem r3bFreeCapEvs_freeOnly (cap : BitVec 64) : FreeOnlyEvs (r3bFreeCapEvs cap) := by
  unfold r3bFreeCapEvs
  split
  · exact LibsignalBinary.Heap.FreeOnlyEvs.nil
  · exact LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 cap.toNat

theorem r3bFreeMePeerEvs_freeOnly (meG peerG : AddrGhost) :
    FreeOnlyEvs (r3bFreeMePeerEvs meG peerG) :=
  LibsignalBinary.Heap.FreeOnlyEvs.append (r3bFreeCapEvs_freeOnly meG.name.cap) (r3bFreeCapEvs_freeOnly peerG.name.cap)

private theorem r3b_sepWP_with_vm_oom {P : Program} {b : BitVec 64}
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
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply r3b_sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
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

private theorem r3b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : R3bCodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      R3bCodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

private theorem rejectMem_atState_postDispatch_eq [LibsignalPlacement] {M : AllocCostModel}
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

private theorem dispatchMemPlaced_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (g : RunCall) (me : MeAtDispatch) (s0 s : State) (resStack : Nat) :
    dispatchMemPlaced A lim st g me s0 s resStack =
      memRegion g.res runResSize ∗
        callAt A.repAlloc g.call g.c ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        dispatchMeHeap A.repAlloc me ∗
        runSaved s0 ∗
        runLocals (runFsp s0) (dispatchCells (runFsp s0) me) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s := rfl

/-! ## 2. Error-Cleanup Tail `R+0x1008 → R+0x2c7c` and `R+0xfec → R+0x2c7c` -/

/-- Shared `peer` deallocation block `R+0x1008 → R+0x2c7c` (`AtRejectPlaced .postDispatch`). -/
theorem r3b_reject_from_1008_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0x1008)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st))
    (hrej : RejectKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have hloc_rejoin :
      memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [] := by
    have h4 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238) ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x230#64) (n := 8) (k := 8)
            (b' := fsp + 0x238#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (ProofLib.pointsTo64_entails_memRegion _ _)))
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have hrej0 := runLocals_rejoin_empty fsp [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; exact Entails.refl _)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at hrej0 ⊢
    rw [hz] at hrej0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl] at hrej0
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h4)) hrej0
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch st := by
      simpa [r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_seq_lscro_oom (mid := runPcPlaced 0x2c7c) hs.inv
    rw [runPcPlaced_eq, hcap, show runFsp s0 = s.sp from hsp.symm]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv') hvm]
      have hs' : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv') 0x2c7c :=
        r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have hat : AtRejectPlaced R3bCodeOk g g' .postDispatch s0 (r3b_stOf hinv') :=
        { base := hs'
          x19 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]
          preRegs := fun hk => nomatch hk
          trace := by simpa only [r3b_stOf, wp_norm, arm64_norm] using htr
          hist := r3b_hist_of_eq (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hhist
          ans := hans }
      refine r3b_sepWPp_weaken_pre ?_ (hrej (r3b_stOf hinv') st g' .postDispatch hat henv0)
      rw [rejectMem_atState_postDispatch_eq, hsp, ← hcap]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc peerG hcap)
            (sepConj_mono hloc_rejoin
              (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim st (r3b_stOf hinv') ∗ anyHeap))))
          (by rw [emp_sepConj]; dsimp only [fsp]; sep_ac_rfl))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc peerG hcap))))))
    rw [show (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply r3b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hs.inv
    rw [← hsp]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = s.sp := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
      refine r3b_call_lscro
        (F := runResAt A.repAlloc cliWrOk g.res (some none) ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion s.sp 0x220 ∗
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((s.sp + 0x230#64) ↦₆₄ u230) ∗
            ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (s.sp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (peerG.name.ptr, peerG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
        (retAddr := runPcPlaced 0x2c7c)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c).readReg64 .x0 = peerG.name.ptr ∧
            ((r3b_stOf hinv_c).readReg64 .x1).toNat = peerG.name.cap.toNat ∧
            ((r3b_stOf hinv_c).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk peerG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlay, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0x2c7c#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c, hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c).fs ∧ sm.trace = (r3b_stOf hinv_c).trace⌝ ∗
            (runResAt A.repAlloc cliWrOk g.res (some none) ∗
              memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion s.sp 0x220 ∗
              (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((s.sp + 0x230#64) ↦₆₄ u230) ∗
                ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt s.sp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced R3bCodeOk s0 sm 0x2c7c :=
          r3b_inRun_step hs hpcm hrunm (hspm.trans hsp_c)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = s.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = s.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hat : AtRejectPlaced R3bCodeOk g g' .postDispatch s0 sm :=
          { base := hs_m
            x19 := hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19])
            preRegs := fun hk => nomatch hk
            trace := htr_tot ▸ htr
            hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
            ans := hans }
        refine r3b_sepWPp_weaken_pre ?_
          (hrej sm (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st)
            g' .postDispatch hat henv1)
        rw [rejectMem_atState_postDispatch_eq, hsp]
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hloc_rejoin
              (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
                anyHeap)))
            (by dsimp only [fsp]))
          (by dsimp only [fsp]; sep_ac_rfl))

/-- Shared reject tail from `R+0xfec → R+0x2c7c` when `me = .some meV meG`:
writes `-1` to `[g.res]`, frees `meG.name`, and finishes via `r3b_reject_from_1008_placed`. -/
theorem r3b_reject_from_fec_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (meG peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0xfec)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro vr
  by_cases hcap : meG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st) := by
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    apply r3b_seq_lscro_oom (mid := runPcPlaced 0x1008) hs.inv
    rw [runPcPlaced_eq]
    rw [hcap] at hx21
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv') hvm]
      have hs1 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv') 0x1008 :=
        r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_1008_placed g' peerG u230 u238 hh hext_le hsub64 hs1
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19])
          (by simpa only [r3b_stOf, wp_norm, arm64_norm] using htr)
          (r3b_hist_of_eq (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hhist)
          hans henv0 hrej)
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc meG hcap)
            (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim st (r3b_stOf hinv') ∗ anyHeap)))
          (by rw [emp_sepConj]))
        (by dsimp only [runResAt, r3b_stOf]; sep_ac_rfl))
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (r3bFreeCapEvs peerG.name.cap)
          (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = runFsp s0 := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc meG hcap))))))
    rw [show (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply r3b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hs.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = runFsp s0 := by
        simpa only [r3b_stOf, wp_norm, arm64_norm] using hsp
      have hstk_split := r3b_stackAt_split_ge (runFsp s0) hext_le hsub64
      refine r3b_call_lscro
        (F := ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (meG.name.ptr, meG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
        (retAddr := runPcPlaced 0x1008)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c).readReg64 .x0 = meG.name.ptr ∧
            ((r3b_stOf hinv_c).readReg64 .x1).toNat = meG.name.cap.toNat ∧
            ((r3b_stOf hinv_c).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk meG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm, hx21],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlay, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0x1008#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c, hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c).fs ∧ sm.trace = (r3b_stOf hinv_c).trace⌝ ∗
            (runResAt A.repAlloc cliWrOk g.res (some none) ∗
              memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by
            rw [hstk_split]
            dsimp only [runResAt, r3b_stOf]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced R3bCodeOk s0 sm 0x1008 :=
          r3b_inRun_step hs hpcm hrunm ((hspm.trans hsp_c).trans hs.sp.symm)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = s.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = s.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        exact r3b_reject_from_1008_placed g' peerG u230 u238 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
          hans henv1 hrej)

/-! ## 3. Dispatch Head `me = .none` and `me = .some` Step Lemmas -/

/-- Shared `me = .none` path (`R+0x214 → R+0x4b0 → R+0x7a4 → R+0x86c → R+0x1008 → R+0x2c7c`). -/
theorem r3b_me_none_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {sEnvs : RunSlotEnvs}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced R3bCodeOk S g s0)
    (hd : AtDispatchPlaced R3bCodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (henv : ∀ cap : BitVec 64,
      EnvAt CryptoVerification.SignalSession.Cli.StoresGhost.opened .postDispatch (M.stepEvents (r3bFreeCapEvs cap) st))
    (hrej : RejectKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g .none s0 s resStack) Q Qp oom := by
  have hbnds :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget.runNeed_bounds_placed
      hres hres64
  have hext_le : extHookStack ≤ resStack - runFrame := by
    have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
  have hans : g.a = some none := hd.reject_of_me_none he
  let fsp := runFsp s0
  rw [dispatchMemPlaced_eq]
  dsimp only [dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hloc_split : runLocals fsp [] =
      memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have h0 := r3b_memRegion_to_runLocalsFrom fsp 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; rfl)
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at h0 ⊢
    rw [hz] at h0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl,
        show 0x220 + 32 = 0x240 from rfl] at h0
    exact h0
  rw [hres_split, hloc_split]
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hpre_prep :
      (((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ emp ∗
        runSaved s0 ∗
        (memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      ∃∗ vr, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3,
        (g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := by
    rw [← hcall, emp_sepConj]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_ownedBytes_entails_nameHeap A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name)
          (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
            (sepConj_mono
              (entails_anyHeap (⌜cw.w0 = 0x8000000000000003#64⌝ ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝ ∗
                coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
                tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff))
              (Entails.refl ((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
                (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)))))
        (by sep_ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vr
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [r3b_addrNameHeap_dev_congr A.repAlloc ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have ha8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have ha16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have ha24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    rw [ha8, ha16, ha24]
    exact Entails.sepExists_right vr (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.of_eq (by sep_ac_rfl))))))
  apply r3b_sepWPp_weaken_pre hpre_prep
  apply r3b_sepWPp_exists_left; intro vr
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag] using hd.x8
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
  have hx21 : s.readReg64 (.gpr 21#5) = noneCap := hd.meRegs
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply r3b_seq_lscro_oom (mid := runPcPlaced 0x1008) hd.base.inv
  dsimp only [noneCap] at hx21
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv1) hvm]
    have hs1 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv1) 0x1008 :=
      r3b_inRun_step hd.base (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    have hhist : RunHistOk g.i s0 (r3b_stOf hinv1) :=
      ⟨by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.fs,
       by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.stdout⟩
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_1008_placed CryptoVerification.SignalSession.Cli.StoresGhost.opened peerG cw.w3 cw.w4 hh hext_le hsub64 hs1
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x19])
        (by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.trace)
        hhist hans (henv peerG.name.cap) hrej)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
          (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗
            storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
            memRegion fsp 0x220 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ cw.w3) ∗
              ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
            memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt fsp (resStack - runFrame) ∗
            A.pool lim st (r3b_stOf hinv1) ∗ anyHeap)))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by rw [hsp]; dsimp only [fsp, runResAt, peerG, r3b_stOf]; sep_ac_rfl))

/-- Shared `me = .some meV meG` dispatch-head step `R+0x214 → R+0x4b0 → R+0x7a4 .. R+0x7c8`. -/
theorem r3b_recv_head_some_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {peerV meV : AddrV} {meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hd : AtDispatchPlaced R3bCodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hk : ∀ (s1 : State) (peerG : AddrGhost) (cw4 hiMe : BitVec 64),
      InRunPlaced R3bCodeOk s0 s1 0x7c8 →
      s1.readReg64 (.gpr 19#5) = g.stores →
      s1.readReg64 (.gpr 20#5) = g.res →
      s1.readReg64 (.gpr 21#5) = meG.name.cap →
      s1.readReg64 (.gpr 23#5) = g.inp →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length →
      s1.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64 →
      s1.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64 →
      s1.readReg64 (.gpr 28#5) = meG.name.ptr →
      s1.trace = s.trace →
      s1.fs = s.fs →
      peerG.val = addrValOf peerV →
      meG.val = addrValOf meV →
      cw4.setWidth 8 = peerG.device →
      hiMe.setWidth 8 = meG.device →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
          tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
          runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (runFsp s0 + 0x240#64) 0x20 ∗
          (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (runFsp s0 + 0x280#64) (runLocalBytes - 0x280) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g (.some meV meG) s0 s resStack) Q Qp oom := by
  let fsp := runFsp s0
  rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
  have hme_val : meG.val = addrValOf meV := by
    cases meG with
    | mk nm dv =>
      dsimp only [CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost.val, addrValOf] at hme_bytes hme_dev ⊢
      rw [hme_bytes, hme_dev]
  rw [dispatchMemPlaced_eq]
  dsimp only [dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hloc_split :
      runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] =
        memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) := by
    have hwf : RunLocalsFromWf 0x1e0
        [(0x220, 32, memRegion (fsp + 0x220#64) 32),
         (0x260, 32, memRegion (fsp + 0x260#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have htail := r3b_memRegion_to_runLocalsFrom fsp 0x1e0
      [(0x220, 32, memRegion (fsp + 0x220#64) 32),
       (0x260, 32, memRegion (fsp + 0x260#64) 32)]
      hwf (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl)
    dsimp only [runLocals, runLocalsFrom] at htail ⊢
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, ← htail]
  rw [hloc_split]
  have hprep :
      (memRegion g.res runResSize ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
        (memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      ∃∗ hiMe, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3, ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ⌜meG.name.cap ≠ 0xffffffffffffffff#64 ∧ cw.w3 = BitVec.ofNat 64 peerV.name.length ∧
          cw.w4.setWidth 8 = peerV.device ∧ hiMe.setWidth 8 = meG.device⌝ ∗
        memRegion g.res runResSize ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        ((fsp + 0x260#64) ↦₆₄ v0) ∗ ((fsp + 0x268#64) ↦₆₄ v1) ∗
        ((fsp + 0x270#64) ↦₆₄ v2) ∗ ((fsp + 0x278#64) ↦₆₄ v3) ∗
        memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s := by
    rw [← hcall]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono
          (Entails.refl (⌜cw.w0 = 0x8000000000000003#64⌝ ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝))
          (sepConj_mono (r3b_nameHeap_cap_ne_neg1 A.repAlloc meG)
            (sepConj_mono (r3b_ownedBytes_entails_nameHeap A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name)
              (sepConj_mono (r3b_addrUpperAt_words (fsp + 0x1d0#64) meG)
                (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
                  (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x260#64))
                    (Entails.refl (memRegion g.res runResSize ∗
                      (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
                      ((g.call + 16#64) ↦₆₄ cw.w2) ∗ ((g.call + 24#64) ↦₆₄ cw.w3) ∗
                      ((g.call + 32#64) ↦₆₄ cw.w4) ∗ ((g.call + 40#64) ↦₆₄ cw.w5) ∗
                      ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                      storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
                      (g.inp ↦ₛ inputOf g.i g.c) ∗
                      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
                      tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
                      runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 0x40 ∗
                      memRegion (fsp + 0x240#64) 0x20 ∗
                      memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s))))))))
        (by sep_ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    apply Entails.sepExists_elim; intro hiMe
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    apply Entails.pure_left; intro hdev_cw4
    apply Entails.pure_left; intro hne1
    apply r3b_pure1; intro hlen_cw3
    apply r3b_pure2; intro hhi
    rw [r3b_addrNameHeap_dev_congr A.repAlloc ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have hd8 : fsp + 0x1d0#64 + 8#64 = fsp + 0x1d8#64 := by bv_omega
    have hu8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have hu16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have hu24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    have hv8 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
    have hv16 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
    have hv24 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
    rw [hd8, hu8, hu16, hu24, hv8, hv16, hv24]
    exact Entails.sepExists_right hiMe (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.sepExists_right v0
          (Entails.sepExists_right v1 (Entails.sepExists_right v2
            (Entails.sepExists_right v3
              (Entails.pure_right ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
                (Entails.of_eq (by sep_ac_rfl)))))))))))
  apply r3b_sepWPp_weaken_pre hprep
  apply r3b_sepWPp_exists_left; intro hiMe
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  apply r3b_sepWPp_exists_left; intro v0
  apply r3b_sepWPp_exists_left; intro v1
  apply r3b_sepWPp_exists_left; intro v2
  apply r3b_sepWPp_exists_left; intro v3
  apply r3b_sepWPp_pure_left; rintro ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
  have hcmn : meG.name.cap + 1#64 ≠ 0#64 := fun h0 => hne1 (by bv_omega)
  have hbeq_cmn : ((meG.name.cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag] using hd.x8
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply r3b_seq_lscro_oom (mid := runPcPlaced 0x7c8) hd.base.inv
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv1) hvm]
    have hs1 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv1) 0x7c8 :=
      r3b_inRun_step hd.base (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (hk (r3b_stOf hinv1) peerG cw.w4 hiMe hs1
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x19])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x20])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x23])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x24])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x26])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x27])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        rfl hme_val hdev_cw4 hhi)
    have h1d0_collapse :
        memRegion fsp 0x1d0 ∗
          ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
          memRegion (fsp + 0x1e0#64) 0x40 ⊢
        memRegion fsp 0x220 := by
      have h16 :
          ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x1d8#64) ↦₆₄ hiMe) ⊢ memRegion (fsp + 0x1d0#64) 16 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
          (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _)
      rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x50)
            (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x40)
            (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono_left h16))
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
          (sepConj_mono h1d0_collapse
            (Entails.refl (memRegion g.res runResSize ∗
              storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
              tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
                ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool lim st (r3b_stOf hinv1)))))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by rw [hsp]; dsimp only [fsp, peerG, r3b_stOf]; rw [hlen_cw3, hme_bytes]; sep_ac_rfl))

/-! ## 4. Bad-Wire Hop (`run_hop_recvBad_placed_ok`) -/

theorem run_hop_recvBad_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvBadPlaced
      (CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A lim sEnvs H B S needs resStack := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvBadPlaced
  intro g st s0 s me peerV Q Qp hh hres hres64 he hd hcall hbad hrej
  cases me with
  | none =>
    exact r3b_me_none_placed hh hres hres64 he hd hcall
      (fun cap => ⟨r3bFreeCapEvs cap, r3bFreeCapEvs_freeOnly cap, rfl⟩) hrej
  | some meV meG =>
    have hbnds :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget.runNeed_bounds_placed
      hres hres64
    have hext_le : extHookStack ≤ resStack - runFrame := by
      have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
    have hans : g.a = some none := hd.recvBad_reject he hcall hbad
    refine r3b_recv_head_some_placed hd hcall ?_
    intro s1 peerG cw4 hiMe hs1 hx19 hx20 hx21 hx23 hx24 _ _ hx28 htr1 hfs1 _ _ _ _
    let fsp := runFsp s0
    have htail_collapse :
        memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ⊢
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
      dsimp only [runLocalBytes]
      rw [ProofLib.memRegion_split' (b := fsp + 0x240#64) (n := 0x20) (k := 0x29f0 - 0x260)
            (b' := fsp + 0x260#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x260#64) (n := 32) (k := 0x29f0 - 0x280)
            (b' := fsp + 0x280#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono_left (r3b_words4_entails_mem32 _ _ _ _ _)))
    apply r3b_sepWPp_weaken_pre
      (r3b_perm
        (r3b_perm_post
          (sepConj_mono htail_collapse
            (sepConj_mono
              (entails_anyHeap (coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
                tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff))
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
                memRegion fsp 0x220 ∗
                (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                  ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                  ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                  ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1))))
          (by dsimp only [fsp]))
        (by dsimp only [fsp]; sep_ac_rfl))
    have henv_mp :
        (fun _ _ st' => ∃ evs, FreeOnlyEvs evs ∧ st' = M.stepEvents evs st)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened CryptoVerification.SignalSession.Cli.RunCompose.RejectKind.postDispatch (M.stepEvents (r3bFreeMePeerEvs meG peerG) st) :=
      ⟨r3bFreeMePeerEvs meG peerG, r3bFreeMePeerEvs_freeOnly meG peerG, rfl⟩
    rcases hbad with hnil | ⟨t, rest, hcons, ht2, ht3⟩
    · have hinp0 : inputOf g.i g.c = [] := by simp [hcall, inputOf, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag, hnil]
      rw [hinp0] at hx24
      dsimp only [List.length] at hx24
      have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
      change s1.pc = (blkPl_579).base + 0x7c8#64 at hpc1
      have hrun1 : s1.status = .Running := hs1.run
      apply r3b_seq_lscro_oom (mid := runPcPlaced 0xfec) hs1.inv
      rw [runPcPlaced_eq]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, hrun1])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv2 => ?_⟩
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        rw [← A.pool_transport lim st s1 (r3b_stOf hinv2) hvm]
        have hs2 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv2) 0xfec :=
          r3b_inRun_step hs1 (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
            (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv2
            (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
        have htr2 : s0.trace <+: (r3b_stOf hinv2).trace :=
          by simpa only [r3b_stOf, wp_norm, arm64_norm, htr1] using hd.trace
        have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
          ⟨by simpa only [r3b_stOf, wp_norm, arm64_norm, hfs1] using hd.fs,
            by simpa only [r3b_stOf, wp_norm, arm64_norm, htr1] using hd.stdout⟩
        refine r3b_sepWPp_weaken_pre (Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl))
          (r3b_reject_from_fec_placed CryptoVerification.SignalSession.Cli.StoresGhost.opened meG peerG
            (BitVec.ofNat 64 peerG.name.bytes.length) cw4
            hh hext_le hsub64 hs2
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28])
            htr2 hhist2 hans henv_mp hrej))
    · have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
        hcall ▸ he.parse
      have htail_lt : rest.length < 2 ^ 32 := by
        have ht0 := he.rel.2.1.2.2.1 peerV hparse
        simpa [hcons] using ht0
      have hinp_c : inputOf g.i g.c = t :: rest := by simp [hcall, inputOf, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag, hcons]
      have hlen_ne : BitVec.ofNat 64 (t :: rest).length ≠ 0#64 := by
        rw [List.length_cons]
        intro h0
        have hv := congrArg BitVec.toNat h0
        have hzero : (0#64).toNat = 0 := rfl
        rw [BitVec.toNat_ofNat, hzero] at hv
        have hmod : (rest.length + 1) % 2 ^ 64 = rest.length + 1 := Nat.mod_eq_of_lt (by omega)
        omega
      have hbeq_len : (BitVec.ofNat 64 (t :: rest).length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      have hne3 : (t.zeroExtend 32 == 3#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht3 (by bv_omega)
      have hne2 : (t.zeroExtend 32 == 2#32) = false :=
        beq_eq_false_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      have hne2b : (t.zeroExtend 32 != 2#32) = true :=
        bne_iff_ne.mpr fun h0 => ht2 (by bv_omega)
      rw [hinp_c] at hx24
      rw [hinp_c, pointsToBytes_cons]
      have hpc1 : s1.pc = runPcPlaced 0x7c8 := hs1.pc
      change s1.pc = (blkPl_579).base + 0x7c8#64 at hpc1
      have hrun1 : s1.status = .Running := hs1.run
      apply r3b_seq_lscro_oom (mid := runPcPlaced 0xfec) hs1.inv
      rw [runPcPlaced_eq]
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, hrun1])
          ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv2 => ?_⟩
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        rw [← A.pool_transport lim st s1 (r3b_stOf hinv2) hvm]
        have hs2 : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv2) 0xfec :=
          r3b_inRun_step hs1 (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun1])
            (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv2
            (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
        have htr2 : s0.trace <+: (r3b_stOf hinv2).trace :=
          by simpa only [r3b_stOf, wp_norm, arm64_norm, htr1] using hd.trace
        have hhist2 : RunHistOk g.i s0 (r3b_stOf hinv2) :=
          ⟨by simpa only [r3b_stOf, wp_norm, arm64_norm, hfs1] using hd.fs,
            by simpa only [r3b_stOf, wp_norm, arm64_norm, htr1] using hd.stdout⟩
        refine r3b_sepWPp_weaken_pre ?_
          (r3b_reject_from_fec_placed CryptoVerification.SignalSession.Cli.StoresGhost.opened meG peerG
            (BitVec.ofNat 64 peerG.name.bytes.length) cw4
            hh hext_le hsub64 hs2
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21])
            (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28])
            htr2 hhist2 hans henv_mp hrej)
        rw [hinp_c, pointsToBytes_cons]
        exact Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl))


theorem r3b_reject_from_1008_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x1008)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have hloc_rejoin :
      memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [] := by
    have h4 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238) ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x230#64) (n := 8) (k := 8)
            (b' := fsp + 0x238#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (ProofLib.pointsTo64_entails_memRegion _ _)))
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have hrej0 := runLocals_rejoin_empty fsp [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; exact Entails.refl _)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at hrej0 ⊢
    rw [hz] at hrej0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl] at hrej0
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h4)) hrej0
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch st := by
      simpa [r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0x2c7c) hs.inv
    rw [runPcPlaced_eq, hcap, show runFsp s0 = s.sp from hsp.symm]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv') hvm]
      have hs' : InRunPlaced CodeOk s0 (r3b_stOf hinv') 0x2c7c :=
        r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have hat : AtRejectPlaced CodeOk g g' .postDispatch s0 (r3b_stOf hinv') :=
        { base := hs'
          x19 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]
          preRegs := fun hk => nomatch hk
          trace := by simpa only [r3b_stOf, wp_norm, arm64_norm] using htr
          hist := r3b_hist_of_eq (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hhist
          ans := hans }
      refine r3b_sepWPp_weaken_pre ?_ (hrej (r3b_stOf hinv') st g' .postDispatch hat henv0)
      rw [rejectMem_atState_postDispatch_eq, hsp, ← hcap]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc peerG hcap)
            (sepConj_mono hloc_rejoin
              (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim st (r3b_stOf hinv') ∗ anyHeap))))
          (by rw [emp_sepConj]; dsimp only [fsp]; sep_ac_rfl))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0x1008 := hs.pc
    change s.pc = (blkPl_579).base + 0x1008#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = fsp := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc peerG hcap))))))
    rw [show (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ u230) ∗ ((fsp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    rw [← hsp]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = s.sp := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge s.sp hext_le hsub64
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
        (F := runResAt A.repAlloc cliWrOk g.res (some none) ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗
          memRegion s.sp 0x220 ∗
          (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((s.sp + 0x230#64) ↦₆₄ u230) ∗
            ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (s.sp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (peerG.name.ptr, peerG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
        (retAddr := runPcPlaced 0x2c7c)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c).readReg64 .x0 = peerG.name.ptr ∧
            ((r3b_stOf hinv_c).readReg64 .x1).toNat = peerG.name.cap.toNat ∧
            ((r3b_stOf hinv_c).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk peerG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlay, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0x2c7c#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c, hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c).fs ∧ sm.trace = (r3b_stOf hinv_c).trace⌝ ∗
            (runResAt A.repAlloc cliWrOk g.res (some none) ∗
              memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion s.sp 0x220 ∗
              (((s.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((s.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((s.sp + 0x230#64) ↦₆₄ u230) ∗
                ((s.sp + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (s.sp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt s.sp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced CodeOk s0 sm 0x2c7c :=
          r3b_inRun_step hs hpcm hrunm (hspm.trans hsp_c)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = s.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = s.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hat : AtRejectPlaced CodeOk g g' .postDispatch s0 sm :=
          { base := hs_m
            x19 := hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19])
            preRegs := fun hk => nomatch hk
            trace := htr_tot ▸ htr
            hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
            ans := hans }
        refine r3b_sepWPp_weaken_pre ?_
          (hrej sm (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st)
            g' .postDispatch hat henv1)
        rw [rejectMem_atState_postDispatch_eq, hsp]
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hloc_rejoin
              (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
                anyHeap)))
            (by dsimp only [fsp]))
          (by dsimp only [fsp]; sep_ac_rfl))

/-- Shared reject tail from `R+0xfec → R+0x2c7c` when `me = .some meV meG`:
writes `-1` to `[g.res]`, frees `meG.name`, and finishes via `r3b_reject_from_1008_placed`. -/
theorem r3b_reject_from_fec_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (meG peerG : AddrGhost) (u230 u238 : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xfec)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro vr
  by_cases hcap : meG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st) := by
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0x1008) hs.inv
    rw [runPcPlaced_eq]
    rw [hcap] at hx21
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv') hvm]
      have hs1 : InRunPlaced CodeOk s0 (r3b_stOf hinv') 0x1008 :=
        r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_1008_placed_codeOk g' peerG u230 u238 hh hext_le hsub64 hs1
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19])
          (by simpa only [r3b_stOf, wp_norm, arm64_norm] using htr)
          (r3b_hist_of_eq (by simp only [r3b_stOf, wp_norm, arm64_norm])
            (by simp only [r3b_stOf, wp_norm, arm64_norm]) hhist)
          hans henv0 hrej)
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc meG hcap)
            (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim st (r3b_stOf hinv') ∗ anyHeap)))
          (by rw [emp_sepConj]))
        (by dsimp only [runResAt, r3b_stOf]; sep_ac_rfl))
  · have hbeq : (meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (r3bFreeCapEvs peerG.name.cap)
          (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r3bFreeMePeerEvs, r3bFreeCapEvs, hcap] using henv
    have hpc : s.pc = runPcPlaced 0xfec := hs.pc
    change s.pc = (blkPl_579).base + 0xfec#64 at hpc
    have hrun : s.status = .Running := hs.run
    have hsp : s.sp = runFsp s0 := hs.sp
    have hsp_al : s.spAligned = true := hs.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc meG hcap))))))
    rw [show (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
          ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) =
      ⌜LayoutOk meG.name.cap.toNat 1⌝ ∗
        (((g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live meG.name.ptr meG.name.cap.toNat 1 ∗
          memRegion meG.name.ptr meG.name.cap.toNat ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlay
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := lsρ lsRustDeallocSymCli) hs.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = runFsp s0 := by
        simpa only [r3b_stOf, wp_norm, arm64_norm] using hsp
      have hstk_split := r3b_stackAt_split_ge (runFsp s0) hext_le hsub64
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
        (F := ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
          memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (meG.name.ptr, meG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
        (retAddr := runPcPlaced 0x1008)
        (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        ?_
        (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        have hpure : (r3b_stOf hinv_c).readReg64 .x0 = meG.name.ptr ∧
            ((r3b_stOf hinv_c).readReg64 .x1).toNat = meG.name.cap.toNat ∧
            ((r3b_stOf hinv_c).readReg64 .x2).toNat = 1 ∧
            RustLayoutOk meG.name.cap.toNat 1 ∧
            LsRetAddr624 ((r3b_stOf hinv_c).readReg64 .lr) :=
          ⟨by simp only [r3b_stOf, wp_norm, arm64_norm],
           by simp only [r3b_stOf, wp_norm, arm64_norm, hx21],
           by simp only [r3b_stOf, wp_norm, arm64_norm],
           ⟨hlay, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0x1008#64 (by decide) (by decide)⟩
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c, hstk_split]
        conv => rhs; rw [sepConj_assoc]
        refine Entails.pure_right hpure ?_
        exact Entails.of_eq (by dsimp only [r3b_stOf]; sep_ac_rfl)
      · dsimp only [Spec.keepsFs,
          LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        dsimp only [r3b_stOf] at hsp_c
        rw [hsp_c]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        refine r3b_sepWPp_weaken_pre
          (P' := ⌜sm.fs = (r3b_stOf hinv_c).fs ∧ sm.trace = (r3b_stOf hinv_c).trace⌝ ∗
            (runResAt A.repAlloc cliWrOk g.res (some none) ∗
              memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ u230) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ u238)) ∗
              memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents meG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by
            rw [hstk_split]
            dsimp only [runResAt, r3b_stOf]
            exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced CodeOk s0 sm 0x1008 :=
          r3b_inRun_step hs hpcm hrunm ((hspm.trans hsp_c).trans hs.sp.symm)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = s.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = s.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        exact r3b_reject_from_1008_placed_codeOk g' peerG u230 u238 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
          hans henv1 hrej)

/-! ## 5. `CodeOk`-Parametric Dispatch Head Step Lemmas -/

/-- Shared `me = .none` path (`R+0x214 → R+0x4b0 → R+0x7a4 → R+0x86c → R+0x1008 → R+0x2c7c`). -/
theorem r3b_me_none_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {sEnvs : RunSlotEnvs}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (henv : ∀ cap : BitVec 64,
      EnvAt CryptoVerification.SignalSession.Cli.StoresGhost.opened .postDispatch (M.stepEvents (r3bFreeCapEvs cap) st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g .none s0 s resStack) Q Qp oom := by
  have hbnds :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget.runNeed_bounds_placed
      hres hres64
  have hext_le : extHookStack ≤ resStack - runFrame := by
    have := hbnds.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnds.2.2.1
  have hans : g.a = some none := hd.reject_of_me_none he
  let fsp := runFsp s0
  rw [dispatchMemPlaced_eq]
  dsimp only [dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  have hres_split : memRegion g.res runResSize =
      (∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    rw [← ProofLib.memRegion_eight g.res]
    exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
  have hloc_split : runLocals fsp [] =
      memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
    have hwf : RunLocalsFromWf 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have h0 := r3b_memRegion_to_runLocalsFrom fsp 0 [(0x220, 32, memRegion (fsp + 0x220#64) 32)]
      hwf (by intro c hc; simp at hc; subst hc; rfl)
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero] at h0 ⊢
    rw [hz] at h0 ⊢
    rw [show BitVec.ofNat 64 (0x220 + 32) = 0x240#64 from rfl,
        show 0x220 + 32 = 0x240 from rfl] at h0
    exact h0
  rw [hres_split, hloc_split]
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hpre_prep :
      (((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ emp ∗
        runSaved s0 ∗
        (memRegion fsp 0x220 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      ∃∗ vr, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3,
        (g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := by
    rw [← hcall, emp_sepConj]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono (r3b_ownedBytes_entails_nameHeap A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name)
          (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
            (sepConj_mono
              (entails_anyHeap (⌜cw.w0 = 0x8000000000000003#64⌝ ∗ ⌜cw.w4.setWidth 8 = peerV.device⌝ ∗
                coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
                tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff))
              (Entails.refl ((∃∗ vr, g.res ↦₆₄ vr) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
                (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
                ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
                ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)))))
        (by sep_ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vr
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    rw [r3b_addrNameHeap_dev_congr A.repAlloc ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have ha8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have ha16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have ha24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    rw [ha8, ha16, ha24]
    exact Entails.sepExists_right vr (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.of_eq (by sep_ac_rfl))))))
  apply r3b_sepWPp_weaken_pre hpre_prep
  apply r3b_sepWPp_exists_left; intro vr
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag] using hd.x8
  have hx20 : s.readReg64 (.gpr 20#5) = g.res := hd.x20
  have hx21 : s.readReg64 (.gpr 21#5) = noneCap := hd.meRegs
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0x1008) hd.base.inv
  dsimp only [noneCap] at hx21
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv1) hvm]
    have hs1 : InRunPlaced CodeOk s0 (r3b_stOf hinv1) 0x1008 :=
      r3b_inRun_step hd.base (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    have hhist : RunHistOk g.i s0 (r3b_stOf hinv1) :=
      ⟨by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.fs,
       by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.stdout⟩
    refine r3b_sepWPp_weaken_pre ?_
      (r3b_reject_from_1008_placed_codeOk CryptoVerification.SignalSession.Cli.StoresGhost.opened peerG cw.w3 cw.w4 hh hext_le hsub64 hs1
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x19])
        (by simpa only [r3b_stOf, wp_norm, arm64_norm] using hd.trace)
        hhist hans (henv peerG.name.cap) hrej)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
          (Entails.refl (runResAt A.repAlloc cliWrOk g.res (some none) ∗
            storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
            memRegion fsp 0x220 ∗
            (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
              ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
              ((fsp + 0x230#64) ↦₆₄ cw.w3) ∗
              ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
            memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
            stackAt fsp (resStack - runFrame) ∗
            A.pool lim st (r3b_stOf hinv1) ∗ anyHeap)))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by rw [hsp]; dsimp only [fsp, runResAt, peerG, r3b_stOf]; sep_ac_rfl))

/-- Shared `me = .some meV meG` dispatch-head step `R+0x214 → R+0x4b0 → R+0x7a4 .. R+0x7c8`. -/
theorem r3b_recv_head_some_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {peerV meV : AddrV} {meG : AddrGhost}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .recv peerV)
    (hk : ∀ (s1 : State) (peerG : AddrGhost) (cw4 hiMe : BitVec 64),
      InRunPlaced CodeOk s0 s1 0x7c8 →
      s1.readReg64 (.gpr 19#5) = g.stores →
      s1.readReg64 (.gpr 20#5) = g.res →
      s1.readReg64 (.gpr 21#5) = meG.name.cap →
      s1.readReg64 (.gpr 23#5) = g.inp →
      s1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (inputOf g.i g.c).length →
      s1.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64 →
      s1.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64 →
      s1.readReg64 (.gpr 28#5) = meG.name.ptr →
      s1.trace = s.trace →
      s1.fs = s.fs →
      peerG.val = addrValOf peerV →
      meG.val = addrValOf meV →
      cw4.setWidth 8 = peerG.device →
      hiMe.setWidth 8 = meG.device →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
          tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗
          runSaved s0 ∗
          memRegion (runFsp s0) 0x220 ∗
          (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (runFsp s0 + 0x240#64) 0x20 ∗
          (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
            ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((runFsp s0 + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (runFsp s0 + 0x280#64) (runLocalBytes - 0x280) ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g (.some meV meG) s0 s resStack) Q Qp oom := by
  let fsp := runFsp s0
  rcases hd.meRegs with ⟨hx21, hx28, hme_bytes, _, hme_dev⟩
  have hme_val : meG.val = addrValOf meV := by
    cases meG with
    | mk nm dv =>
      dsimp only [CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost.val, addrValOf] at hme_bytes hme_dev ⊢
      rw [hme_bytes, hme_dev]
  rw [dispatchMemPlaced_eq]
  dsimp only [dispatchMeHeap, dispatchCells]
  rw [hcall]
  dsimp only [callAt, callHeap, addrWords]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r3b_sepWPp_exists_left; intro cw
  let peerG : AddrGhost := ⟨⟨cw.w1, cw.w2, peerV.name⟩, peerV.device⟩
  have hloc_split :
      runLocals fsp [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] =
        memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) := by
    have hwf : RunLocalsFromWf 0x1e0
        [(0x220, 32, memRegion (fsp + 0x220#64) 32),
         (0x260, 32, memRegion (fsp + 0x260#64) 32)] := by
      dsimp only [RunLocalsFromWf, runLocalBytes]; omega
    have htail := r3b_memRegion_to_runLocalsFrom fsp 0x1e0
      [(0x220, 32, memRegion (fsp + 0x220#64) 32),
       (0x260, 32, memRegion (fsp + 0x260#64) 32)]
      hwf (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl)
    dsimp only [runLocals, runLocalsFrom] at htail ⊢
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, ← htail]
  rw [hloc_split]
  have hprep :
      (memRegion g.res runResSize ∗
        ((g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
          ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
          ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
          ⌜cw.w0 = 0x8000000000000003#64⌝ ∗
          (ownedBytes A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝)) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i (.recv peerV)) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        addrNameHeap A.repAlloc meG ∗ runSaved s0 ∗
        (memRegion fsp 0x1d0 ∗ addrUpperAt (fsp + 0x1d0#64) meG ∗
          memRegion (fsp + 0x1e0#64) 0x40 ∗ memRegion (fsp + 0x220#64) 32 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗ memRegion (fsp + 0x260#64) 32 ∗
          memRegion (fsp + 0x280#64) (runLocalBytes - 0x280)) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) ⊢
      ∃∗ hiMe, ∃∗ u0, ∃∗ u1, ∃∗ u2, ∃∗ u3, ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        ⌜meG.name.cap ≠ 0xffffffffffffffff#64 ∧ cw.w3 = BitVec.ofNat 64 peerV.name.length ∧
          cw.w4.setWidth 8 = peerV.device ∧ hiMe.setWidth 8 = meG.device⌝ ∗
        memRegion g.res runResSize ∗
        (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗ ((g.call + 16#64) ↦₆₄ cw.w2) ∗
        ((g.call + 24#64) ↦₆₄ cw.w3) ∗ ((g.call + 32#64) ↦₆₄ cw.w4) ∗
        ((g.call + 40#64) ↦₆₄ cw.w5) ∗ ((g.call + 48#64) ↦₆₄ cw.w6) ∗
        storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x1d0 ∗
        ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
        ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
        memRegion (fsp + 0x1e0#64) 0x40 ∗
        ((fsp + 0x220#64) ↦₆₄ u0) ∗ ((fsp + 0x228#64) ↦₆₄ u1) ∗
        ((fsp + 0x230#64) ↦₆₄ u2) ∗ ((fsp + 0x238#64) ↦₆₄ u3) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        ((fsp + 0x260#64) ↦₆₄ v0) ∗ ((fsp + 0x268#64) ↦₆₄ v1) ∗
        ((fsp + 0x270#64) ↦₆₄ v2) ∗ ((fsp + 0x278#64) ↦₆₄ v3) ∗
        memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s := by
    rw [← hcall]
    refine Entails.trans
      (r3b_perm
        (sepConj_mono
          (Entails.refl (⌜cw.w0 = 0x8000000000000003#64⌝ ∗
            ⌜cw.w4.setWidth 8 = peerV.device⌝))
          (sepConj_mono (r3b_nameHeap_cap_ne_neg1 A.repAlloc meG)
            (sepConj_mono (r3b_ownedBytes_entails_nameHeap A.repAlloc cw.w1 cw.w2 cw.w3 peerV.name)
              (sepConj_mono (r3b_addrUpperAt_words (fsp + 0x1d0#64) meG)
                (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x220#64))
                  (sepConj_mono (r3b_mem32_to_words4 (fsp + 0x260#64))
                    (Entails.refl (memRegion g.res runResSize ∗
                      (g.call ↦₆₄ cw.w0) ∗ ((g.call + 8#64) ↦₆₄ cw.w1) ∗
                      ((g.call + 16#64) ↦₆₄ cw.w2) ∗ ((g.call + 24#64) ↦₆₄ cw.w3) ∗
                      ((g.call + 32#64) ↦₆₄ cw.w4) ∗ ((g.call + 40#64) ↦₆₄ cw.w5) ∗
                      ((g.call + 48#64) ↦₆₄ cw.w6) ∗
                      storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
                      (g.inp ↦ₛ inputOf g.i g.c) ∗
                      coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
                      tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
                      runSaved s0 ∗ memRegion fsp 0x1d0 ∗ memRegion (fsp + 0x1e0#64) 0x40 ∗
                      memRegion (fsp + 0x240#64) 0x20 ∗
                      memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
                      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s))))))))
        (by sep_ac_rfl))
      ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro u0
    apply Entails.sepExists_elim; intro u1
    apply Entails.sepExists_elim; intro u2
    apply Entails.sepExists_elim; intro u3
    apply Entails.sepExists_elim; intro hiMe
    simp only [sepConj_assoc]
    apply Entails.pure_left; intro _
    apply Entails.pure_left; intro hdev_cw4
    apply Entails.pure_left; intro hne1
    apply r3b_pure1; intro hlen_cw3
    apply r3b_pure2; intro hhi
    rw [r3b_addrNameHeap_dev_congr A.repAlloc ⟨cw.w1, cw.w2, peerV.name⟩ 0#8 peerV.device]
    have hd8 : fsp + 0x1d0#64 + 8#64 = fsp + 0x1d8#64 := by bv_omega
    have hu8 : fsp + 0x220#64 + 8#64 = fsp + 0x228#64 := by bv_omega
    have hu16 : fsp + 0x220#64 + 16#64 = fsp + 0x230#64 := by bv_omega
    have hu24 : fsp + 0x220#64 + 24#64 = fsp + 0x238#64 := by bv_omega
    have hv8 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
    have hv16 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
    have hv24 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
    rw [hd8, hu8, hu16, hu24, hv8, hv16, hv24]
    exact Entails.sepExists_right hiMe (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
        (Entails.sepExists_right u3 (Entails.sepExists_right v0
          (Entails.sepExists_right v1 (Entails.sepExists_right v2
            (Entails.sepExists_right v3
              (Entails.pure_right ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
                (Entails.of_eq (by sep_ac_rfl)))))))))))
  apply r3b_sepWPp_weaken_pre hprep
  apply r3b_sepWPp_exists_left; intro hiMe
  apply r3b_sepWPp_exists_left; intro u0
  apply r3b_sepWPp_exists_left; intro u1
  apply r3b_sepWPp_exists_left; intro u2
  apply r3b_sepWPp_exists_left; intro u3
  apply r3b_sepWPp_exists_left; intro v0
  apply r3b_sepWPp_exists_left; intro v1
  apply r3b_sepWPp_exists_left; intro v2
  apply r3b_sepWPp_exists_left; intro v3
  apply r3b_sepWPp_pure_left; rintro ⟨hne1, hlen_cw3, hdev_cw4, hhi⟩
  have hcmn : meG.name.cap + 1#64 ≠ 0#64 := fun h0 => hne1 (by bv_omega)
  have hbeq_cmn : ((meG.name.cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
  have hpc : s.pc = runPcPlaced 0x214 := hd.base.pc
  change s.pc = (blkPl_579).base + 0x214#64 at hpc
  have hrun : s.status = .Running := hd.base.run
  have hsp : s.sp = fsp := hd.base.sp
  have hsp_al : s.spAligned = true := hd.base.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa [hcall, CryptoVerification.SignalSession.Cli.MainHops.CallV.tag] using hd.x8
  have hx25 : s.readReg64 (.gpr 25#5) = g.call := hd.x25
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0x7c8) hd.base.inv
  rw [runPcPlaced_eq, ← hsp]
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv1 => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv1) hvm]
    have hs1 : InRunPlaced CodeOk s0 (r3b_stOf hinv1) 0x7c8 :=
      r3b_inRun_step hd.base (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv1
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (hk (r3b_stOf hinv1) peerG cw.w4 hiMe hs1
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x19])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x20])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x23])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x24])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x26])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hd.x27])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        rfl hme_val hdev_cw4 hhi)
    have h1d0_collapse :
        memRegion fsp 0x1d0 ∗
          ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x1d8#64) ↦₆₄ hiMe) ∗
          memRegion (fsp + 0x1e0#64) 0x40 ⊢
        memRegion fsp 0x220 := by
      have h16 :
          ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x1d8#64) ↦₆₄ hiMe) ⊢ memRegion (fsp + 0x1d0#64) 16 := by
        rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 8) (k := 8)
          (b' := fsp + 0x1d8#64) rfl (by bv_omega) (by decide)]
        exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _)
      rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x50)
            (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 16) (k := 0x40)
            (b' := fsp + 0x1e0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono_right (sepConj_mono_left h16))
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (r3b_call7_to_memRegion56 g.call cw)
          (sepConj_mono h1d0_collapse
            (Entails.refl (memRegion g.res runResSize ∗
              storesAt A.repAlloc g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (CryptoVerification.SignalSession.Cli.MainHops.coinsOf g.i) ∗
              tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw.w4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗
                ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) (runLocalBytes - 0x280) ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool lim st (r3b_stOf hinv1)))))
        (by dsimp only [fsp]; sep_ac_rfl))
      (by rw [hsp]; dsimp only [fsp, peerG, r3b_stOf]; rw [hlen_cw3, hme_bytes]; sep_ac_rfl))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
