/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R3b`: `PreKeySignalMessage::try_from` and Shuffle Steps

Provides the VM- and `R3bCodeOk`-preserving multi-instruction segment stepper on Block `579`, the
budget-threaded `PreKeySignalMessage::try_from` `Err` path (`r3b_recvP_parse_err_placed`), and the
first half of the `Ok` 240-byte stack shuffle (`r3b_recvP_shuf1_placed`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost errTag)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall inputOf runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (InRunPlaced R3bCodeOk RejectKind RunHistOk addrNameHeap pksmResAt r3b_W30 r3b_W5
   r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1 r3b_calleeSavedVRegs_q2
   r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPC r3b_calleeSavedVRegs_setPState
   r3b_calleeSavedVRegs_writeReg64 r3b_collapse30_flat r3b_collapse5_flat
   r3b_extractLsb_append_hi r3b_extractLsb_append_lo r3b_files_of_trace_eq r3b_fs_setMem
   r3b_fs_setPC r3b_fs_setPState r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_hist_of_eq
   r3b_inRun_step r3b_mem40_to_slot5 r3b_mem_setPState r3b_perm r3b_perm_post r3b_pt64_eq
   r3b_readReg64_setPState r3b_sepWPp_exists_left r3b_sepWPp_pure_left r3b_sepWPp_weaken_pre
   r3b_shufMid r3b_slot30 r3b_slot5 r3b_slot5_to_mem40 r3b_slot6 r3b_sp_setPState r3b_split_at
   r3b_stOf r3b_status_setPState r3b_symtab_setPState r3b_trace_setPState
   r3b_with_speOwned_words6 r3b_words4_entails_mem32 runFsp runLocalBytes runPcPlaced
   runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs (pksmResAt_err_owned)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (r3bFreeMePeerEvs r3b_reject_from_fec_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (RejectKPlaced RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  runPcPlaced_eq BitVec.ofNat_eq_ofNat
  r3b_extractLsb_append_lo r3b_extractLsb_append_hi
  r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1 r3b_calleeSavedVRegs_q2
  r3b_calleeSavedVRegs_writeReg64
  r3b_calleeSavedVRegs_setPC r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPState
  r3b_readReg64_setPState r3b_sp_setPState r3b_mem_setPState r3b_status_setPState
  r3b_trace_setPState r3b_symtab_setPState r3b_fs_setPState
  r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_fs_setPC r3b_fs_setMem

/-! ## 1. VM- & `R3bCodeOk`-Preserving Segment Stepper on Block `579` -/

theorem r3b_sepWP_with_vm_oom {P : Program} {b : BitVec 64}
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

theorem r3b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : R3bCodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      R3bCodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

/-! ## 2. `PreKeySignalMessage::try_from` `Err` Path (`r3b_recvP_parse_err_placed`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded `PreKeySignalMessage::try_from` `Err` path
(`R+0x994 → R+0xeb8 → R+0xfe0 → (blkPl_553).base → R+0xfec → R+0x2c7c`). -/
theorem r3b_recvP_parse_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (meG peerG : AddrGhost) (cw4 hiMe : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0x994)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_drop, FreeOnlyEvs evs_drop →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
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
        memRegion (runFsp s0 + 0x280#64) (0x4d0 - 0x280) ∗
        pksmResAt A.repAlloc (runFsp s0 + 0x4d0#64) none ∗
        memRegion (runFsp s0 + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
        memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) := by
    rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by omega) (by omega),
        r3b_split_at fsp 0x2a0 40 0x4d0 (by omega) (by omega)]
  rw [h280]
  have hpkm_err :
      pksmResAt A.repAlloc (fsp + 0x4d0#64) none ∗ memRegion (fsp + 0x2a0#64) 40 ∗ anyHeap ⊢
      ∃∗ k : SpeOwned, ∃∗ t : r3b_W5,
        speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap := by
    have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
    have ha508 : fsp + 0x4d0#64 + 56#64 = fsp + 0x508#64 := by bv_omega
    refine Entails.trans
      (sepConj_mono (pksmResAt_err_owned A.repAlloc (fsp + 0x4d0#64))
        (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64)) (Entails.refl anyHeap)))
      ?_
    rw [ha4d8, ha508]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro t
    apply Entails.sepExists_elim; intro k
    refine Entails.sepExists_right k (Entails.sepExists_right t ?_)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (entails_anyHeap (anyHeap ∗ anyHeap))
          (Entails.refl (speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
            ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
            r3b_slot5 (fsp + 0x2a0#64) t ∗
            memRegion (fsp + 0x508#64) 192)))
        (by ac_rfl))
      (by ac_rfl)
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
        hpkm_err)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro t
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (A := A.repAlloc) (src := fsp + 0x4d8#64)
    (dst := fsp + 0x4d0#64) (k := k) (fun sw _ _ => ?_)
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          r3b_slot5 (fsp + 0x2a0#64) t ∗
          memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)) ⊢
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) from Entails.of_eq (by ac_rfl))
  have herr_eq : ((errTag + 1#64) == 0#64) = true := rfl
  apply r3b_seq_lscro_oom (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
    refine r3b_call_lscro
      (spec := dropSpeOwnedSpec A lim (resStack - runFrame))
      (F := ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
        r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
        memRegion (fsp + 0x508#64) 192 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)
      (⟨fsp + 0x4d0#64, k⟩, st)
      (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
      (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
      (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
      (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0xfec)
      (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
      ?_
      (hnext := fun sm hsteps_m hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [dropSpeOwnedSpec, r3b_stOf]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · refine ⟨?_, ⟨579, by decide, 0xfec, by decide, ?_⟩⟩
        · simp only [wp_norm, arm64_norm]; try rw [hsp]
        · simp only [wp_norm, arm64_norm]
      simp only [wp_norm, arm64_norm]
      try rw [hsp]
      have hwand :
          r3b_slot6 (fsp + 0x4d0#64) sw ∗
            (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ⊢
          speOwnedAt A.repAlloc (fsp + 0x4d0#64) k := Entails.wand_elim _ _
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hwand
            (Entails.refl (A.pool lim st (r3b_stOf hinv_c) ∗ stackAt fsp (resStack - runFrame) ∗
              ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
              r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
              memRegion (fsp + 0x508#64) 192 ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x220 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)))
          (by dsimp only [r3b_stOf]; sep_ac_rfl))
        (by
          dsimp only [r3b_slot6, r3b_slot5, r3b_stOf]
          have o1 : fsp + 0x4d0#64 + 8#64 = fsp + 1240#64 := by bv_omega
          have o2 : fsp + 0x4d0#64 + 16#64 = fsp + 1248#64 := by bv_omega
          have o3 : fsp + 0x4d0#64 + 24#64 = fsp + 1256#64 := by bv_omega
          have o4 : fsp + 0x4d0#64 + 32#64 = fsp + 1264#64 := by bv_omega
          have o5 : fsp + 0x4d0#64 + 40#64 = fsp + 1272#64 := by bv_omega
          have t1 : fsp + 672#64 + 8#64 = fsp + 680#64 := by bv_omega
          have t2 : fsp + 672#64 + 16#64 = fsp + 688#64 := by bv_omega
          have t3 : fsp + 672#64 + 24#64 = fsp + 696#64 := by bv_omega
          have t4 : fsp + 672#64 + 32#64 = fsp + 704#64 := by bv_omega
          have z0 : fsp + 1232#64 = fsp + 0x4d0#64 := rfl
          rw [o1, o2, o3, o4, o5, t1, t2, t3, t4, z0]
          sep_ac_rfl)
    · dsimp only [dropSpeOwnedSpec]
      simp only [sepExists_sepConj_left]
      apply r3b_sepWPp_exists_left; intro evs_drop
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; rintro ⟨htr_m, hfree_drop⟩
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
      have hfs_tot : sm.fs.files = s.fs.files :=
        (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_m htr_m).trans
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
      have hs_m : InRunPlaced R3bCodeOk s0 sm 0xfec :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
      have henv_drop : EnvAt StoresGhost.opened .postDispatch
          (M.stepEvents (r3bFreeMePeerEvs meG peerG) (M.stepEvents evs_drop st)) := by
        rw [← M.stepEvents_append]
        exact henv evs_drop hfree_drop
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_fec_placed StoresGhost.opened meG peerG
          (BitVec.ofNat 64 peerG.name.bytes.length) cw4 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]))
          (hcsm.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]))
          (hcsm.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]))
          (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot hfs_tot hhist)
          hans henv_drop hrej)
      have hloc_back :
          memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗
            r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
            memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
            memRegion (fsp + 0x4d0#64) 48 ∗
            ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            memRegion (fsp + 0x508#64) 192 ∗
            memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
        have hpkm_back :
            memRegion (fsp + 0x4d0#64) 48 ∗ ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
              memRegion (fsp + 0x508#64) 192 ⊢
            memRegion (fsp + 0x4d0#64) 248 := by
          rw [ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 48) (k := 200)
                (b' := fsp + 1280#64) rfl (by bv_omega) (by decide),
              ProofLib.memRegion_split' (b := fsp + 1280#64) (n := 8) (k := 192)
                (b' := fsp + 0x508#64) rfl (by bv_omega) (by decide)]
          exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
        have hm1 := sepConj_mono (Entails.refl (memRegion (fsp + 0x240#64) 0x20))
          (sepConj_mono (r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
                (BitVec.ofNat 64 meG.name.bytes.length) hiMe)
            (sepConj_mono (Entails.refl (memRegion (fsp + 0x280#64) 0x20))
              (sepConj_mono (r3b_slot5_to_mem40 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩)
                (sepConj_mono (Entails.refl (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8)))
                  (sepConj_mono hpkm_back
                    (Entails.refl (memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))))))
        have heq_all : memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
            memRegion (fsp + 0x240#64) 0x20 ∗
              (memRegion (fsp + 0x260#64) 32 ∗
                (memRegion (fsp + 0x280#64) 0x20 ∗
                  (memRegion (fsp + 672#64) 40 ∗
                    (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
                      (memRegion (fsp + 0x4d0#64) 248 ∗
                        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8)))))) := by
          rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x280 0x20 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x2a0 40 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x2c8 (0x4d0 - 0x2c8) runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
        rw [heq_all]
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1
        exact r3b_perm hm1 (by ac_rfl)
      subst hfsp
      rw [← hspm, hs_m.sp]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hloc_back
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs_drop st) sm ∗ anyHeap)))
          (by sep_ac_rfl))
        (by sep_ac_rfl))

theorem r3b_recvP_parse_err_placed_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall}
    (meG peerG : AddrGhost) (cw4 hiMe : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0x994)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R3bCodeOk H A lim g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
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
        memRegion (runFsp s0 + 0x280#64) (0x4d0 - 0x280) ∗
        pksmResAt A.repAlloc (runFsp s0 + 0x4d0#64) none ∗
        memRegion (runFsp s0 + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom :=
  r3b_recvP_parse_err_placed (EnvAt := fun _ _ _ => True) meG peerG cw4 hiMe hh hdrop hstk32
    hext_le hsub64 hs hx19 hx20 hx21 hx26 hx28 htr hhist hans (fun _ _ => trivial)
    (fun s' st' g'' rk hat _ => hrej s' st' g'' rk hat)

/-! ## 3. `PreKeySignalMessage::try_from` `Ok` Shuffle (`r3b_recvP_shuf1_placed`, `r3b_recvP_shuf2_placed`) -/

set_option maxHeartbeats 800000 in
/-- First half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0x994 → R+0xaa0`),
delivering `VmPreserved s s'` to the continuation. -/
theorem r3b_recvP_shuf1_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (pqCap : BitVec 64) (w : r3b_W30) (t : r3b_W5) (z m : r3b_W30) (F : SepProp)
    (hs : InRunPlaced R3bCodeOk s0 s 0x994)
    (hcap : pqCap.toNat < 2 ^ 63)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hk : ∀ s' : State,
      VmPreserved s s' →
      InRunPlaced R3bCodeOk s0 s' 0xaa0 →
      s'.readReg64 (.gpr 8#5) = w.b0.w0 →
      s'.readReg64 (.gpr 9#5) = pqCap →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
          memRegion (runFsp s0 + 0x2a0#64) 40 ∗
          r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
          memRegion (runFsp s0 + 0x1750#64) 240 ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
        r3b_slot5 (runFsp s0 + 0x2a0#64) t ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) z ∗
        r3b_slot30 (runFsp s0 + 0x1750#64) m ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hcmn : ((pqCap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  generalize hfsp : runFsp s0 = fsp at hsp hx26 hx27 ⊢
  apply r3b_seq_lscro_oom (mid := runPcPlaced 0xaa0) hs.inv
  rw [runPcPlaced_eq]
  dsimp only [r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hx26 hx27 ⊢
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    subst hfsp
    let fsp := runFsp s0
    have hs' : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv') 0xaa0 :=
      r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (hk (r3b_stOf hinv') hvm hs'
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]))
    try rw [hsp]
    have hc5 : ∀ (T : SepProp),
        ((fsp + 672#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 680#64) ↦₆₄ w.b0.w2) ∗
        ((fsp + 688#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 696#64) ↦₆₄ w.b0.w4) ∗
        ((fsp + 704#64) ↦₆₄ w.b1.w0) ∗ T ⊢ memRegion (fsp + 0x2a0#64) 40 ∗ T :=
      fun T => r3b_collapse5_flat (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (Entails.refl _)
    have hc30 : ∀ (T : SepProp),
        ((fsp + 5968#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 5976#64) ↦₆₄ w.b0.w2) ∗
        ((fsp + 5984#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 5992#64) ↦₆₄ w.b0.w4) ∗
        ((fsp + 6000#64) ↦₆₄ w.b1.w0) ∗ ((fsp + 6008#64) ↦₆₄ w.b1.w1) ∗
        ((fsp + 6016#64) ↦₆₄ w.b1.w2) ∗ ((fsp + 6024#64) ↦₆₄ w.b1.w3) ∗
        ((fsp + 6032#64) ↦₆₄ w.b1.w4) ∗ ((fsp + 6040#64) ↦₆₄ w.b2.w0) ∗
        ((fsp + 6048#64) ↦₆₄ w.b2.w1) ∗ ((fsp + 6056#64) ↦₆₄ w.b2.w2) ∗
        ((fsp + 6064#64) ↦₆₄ w.b2.w3) ∗ ((fsp + 6072#64) ↦₆₄ w.b2.w4) ∗
        ((fsp + 6080#64) ↦₆₄ w.b3.w0) ∗ ((fsp + 6088#64) ↦₆₄ w.b3.w1) ∗
        ((fsp + 6096#64) ↦₆₄ w.b3.w2) ∗ ((fsp + 6104#64) ↦₆₄ w.b3.w3) ∗
        ((fsp + 6112#64) ↦₆₄ w.b3.w4) ∗ ((fsp + 6120#64) ↦₆₄ w.b4.w0) ∗
        ((fsp + 6128#64) ↦₆₄ w.b4.w1) ∗ ((fsp + 6136#64) ↦₆₄ w.b4.w2) ∗
        ((fsp + 6144#64) ↦₆₄ w.b4.w3) ∗ ((fsp + 6152#64) ↦₆₄ w.b4.w4) ∗
        ((fsp + 6160#64) ↦₆₄ w.b5.w0) ∗ ((fsp + 6168#64) ↦₆₄ w.b5.w1) ∗
        ((fsp + 6176#64) ↦₆₄ w.b5.w2) ∗ ((fsp + 6184#64) ↦₆₄ w.b5.w3) ∗
        ((fsp + 6192#64) ↦₆₄ w.b5.w4) ∗ ((fsp + 6200#64) ↦₆₄ m.b5.w4) ∗ T ⊢
        memRegion (fsp + 0x1750#64) 240 ∗ T :=
      fun T => r3b_collapse30_flat
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (Entails.refl _)
    dsimp only [fsp, r3b_slot30, r3b_slot5, r3b_shufMid] at hc5 hc30 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hc5 hc30 ⊢
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (Entails.trans (hc5 _) (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (hc30 _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


set_option maxHeartbeats 800000 in
/-- Budget-threaded `PreKeySignalMessage::try_from` `Err` path
(`R+0x994 → R+0xeb8 → R+0xfe0 → (blkPl_553).base → R+0xfec → R+0x2c7c`). -/
theorem r3b_recvP_parse_err_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (meG peerG : AddrGhost) (cw4 hiMe : BitVec 64)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0x994)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_drop, FreeOnlyEvs evs_drop →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
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
        memRegion (runFsp s0 + 0x280#64) (0x4d0 - 0x280) ∗
        pksmResAt A.repAlloc (runFsp s0 + 0x4d0#64) none ∗
        memRegion (runFsp s0 + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h280 : memRegion (fsp + 0x280#64) (0x4d0 - 0x280) =
      memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2a0#64) 40 ∗
        memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) := by
    rw [r3b_split_at fsp 0x280 0x20 0x4d0 (by omega) (by omega),
        r3b_split_at fsp 0x2a0 40 0x4d0 (by omega) (by omega)]
  rw [h280]
  have hpkm_err :
      pksmResAt A.repAlloc (fsp + 0x4d0#64) none ∗ memRegion (fsp + 0x2a0#64) 40 ∗ anyHeap ⊢
      ∃∗ k : SpeOwned, ∃∗ t : r3b_W5,
        speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap := by
    have ha4d8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
    have ha508 : fsp + 0x4d0#64 + 56#64 = fsp + 0x508#64 := by bv_omega
    refine Entails.trans
      (sepConj_mono (pksmResAt_err_owned A.repAlloc (fsp + 0x4d0#64))
        (sepConj_mono (r3b_mem40_to_slot5 (fsp + 0x2a0#64)) (Entails.refl anyHeap)))
      ?_
    rw [ha4d8, ha508]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro t
    apply Entails.sepExists_elim; intro k
    refine Entails.sepExists_right k (Entails.sepExists_right t ?_)
    exact r3b_perm
      (r3b_perm_post
        (sepConj_mono (entails_anyHeap (anyHeap ∗ anyHeap))
          (Entails.refl (speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
            ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
            r3b_slot5 (fsp + 0x2a0#64) t ∗
            memRegion (fsp + 0x508#64) 192)))
        (by ac_rfl))
      (by ac_rfl)
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
        hpkm_err)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro t
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (A := A.repAlloc) (src := fsp + 0x4d8#64)
    (dst := fsp + 0x4d0#64) (k := k) (fun sw _ _ => ?_)
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
          r3b_slot5 (fsp + 0x2a0#64) t ∗
          memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
          memRegion fsp 0x220 ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
            ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
          memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
          memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)) ⊢
      (((fsp + 0x4d0#64) ↦₆₄ errTag) ∗
        r3b_slot6 (fsp + 0x4d8#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        r3b_slot5 (fsp + 0x2a0#64) t ∗
        memRegion (fsp + 0x508#64) 192 ∗ anyHeap) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) from Entails.of_eq (by ac_rfl))
  have herr_eq : ((errTag + 1#64) == 0#64) = true := rfl
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hx26 ⊢
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    rw [← A.pool_transport lim st s (r3b_stOf hinv_c) hvm]
    refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
      (spec := dropSpeOwnedSpec A lim (resStack - runFrame))
      (F := ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
        r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
        memRegion (fsp + 0x508#64) 192 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
        memRegion fsp 0x220 ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
          ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
        memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)
      (⟨fsp + 0x4d0#64, k⟩, st)
      (hdrop (resStack - runFrame) hstk32 hsub64) hinv_c
      (by simp only [r3b_stOf, wp_norm, arm64_norm]; rfl)
      (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
      (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
      (retAddr := runPcPlaced 0xfec)
      (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
      ?_
      (hnext := fun sm hsteps_m hinv_m hpcm hrunm hspm hcsm => ?_)
    · dsimp only [dropSpeOwnedSpec, r3b_stOf]
      simp only [sepConj_assoc]
      apply Entails.pure_right
      · refine ⟨?_, ⟨579, by decide, 0xfec, by decide, ?_⟩⟩
        · simp only [wp_norm, arm64_norm]; try rw [hsp]
        · simp only [wp_norm, arm64_norm]
      simp only [wp_norm, arm64_norm]
      try rw [hsp]
      have hwand :
          r3b_slot6 (fsp + 0x4d0#64) sw ∗
            (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ⊢
          speOwnedAt A.repAlloc (fsp + 0x4d0#64) k := Entails.wand_elim _ _
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hwand
            (Entails.refl (A.pool lim st (r3b_stOf hinv_c) ∗ stackAt fsp (resStack - runFrame) ∗
              ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
              r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
              memRegion (fsp + 0x508#64) 192 ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion fsp 0x220 ∗
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ cw4)) ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
                ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
              memRegion (fsp + 0x280#64) 0x20 ∗ memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
              memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ∗ anyHeap)))
          (by dsimp only [r3b_stOf]; sep_ac_rfl))
        (by
          dsimp only [r3b_slot6, r3b_slot5, r3b_stOf]
          have o1 : fsp + 0x4d0#64 + 8#64 = fsp + 1240#64 := by bv_omega
          have o2 : fsp + 0x4d0#64 + 16#64 = fsp + 1248#64 := by bv_omega
          have o3 : fsp + 0x4d0#64 + 24#64 = fsp + 1256#64 := by bv_omega
          have o4 : fsp + 0x4d0#64 + 32#64 = fsp + 1264#64 := by bv_omega
          have o5 : fsp + 0x4d0#64 + 40#64 = fsp + 1272#64 := by bv_omega
          have t1 : fsp + 672#64 + 8#64 = fsp + 680#64 := by bv_omega
          have t2 : fsp + 672#64 + 16#64 = fsp + 688#64 := by bv_omega
          have t3 : fsp + 672#64 + 24#64 = fsp + 696#64 := by bv_omega
          have t4 : fsp + 672#64 + 32#64 = fsp + 704#64 := by bv_omega
          have z0 : fsp + 1232#64 = fsp + 0x4d0#64 := rfl
          rw [o1, o2, o3, o4, o5, t1, t2, t3, t4, z0]
          sep_ac_rfl)
    · dsimp only [dropSpeOwnedSpec]
      simp only [sepExists_sepConj_left]
      apply r3b_sepWPp_exists_left; intro evs_drop
      simp only [sepConj_assoc]
      apply r3b_sepWPp_pure_left; rintro ⟨htr_m, hfree_drop⟩
      have htr_tot : sm.trace = s.trace := htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
      have hfs_tot : sm.fs.files = s.fs.files :=
        (r3b_files_of_trace_eq (hh.fs (runProgPlaced H) 579) hsteps_m htr_m).trans
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
      have hs_m : InRunPlaced CodeOk s0 sm 0xfec :=
        r3b_inRun_step hs hpcm hrunm (hspm.trans (by simp only [r3b_stOf, wp_norm, arm64_norm]))
          (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])) hinv_m
          (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm]))
      have henv_drop : EnvAt StoresGhost.opened .postDispatch
          (M.stepEvents (r3bFreeMePeerEvs meG peerG) (M.stepEvents evs_drop st)) := by
        rw [← M.stepEvents_append]
        exact henv evs_drop hfree_drop
      refine r3b_sepWPp_weaken_pre ?_
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget.r3b_reject_from_fec_placed_codeOk StoresGhost.opened meG peerG
          (BitVec.ofNat 64 peerG.name.bytes.length) cw4 hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]))
          (hcsm.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]))
          (hcsm.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]))
          (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot hfs_tot hhist)
          hans henv_drop hrej)
      have hloc_back :
          memRegion (fsp + 0x240#64) 0x20 ∗
            (((fsp + 0x260#64) ↦₆₄ meG.name.cap) ∗ ((fsp + 0x268#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
              ((fsp + 0x278#64) ↦₆₄ hiMe)) ∗
            memRegion (fsp + 0x280#64) 0x20 ∗
            r3b_slot5 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩ ∗
            memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
            memRegion (fsp + 0x4d0#64) 48 ∗
            ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
            memRegion (fsp + 0x508#64) 192 ∗
            memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8) ⊢
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
        have hpkm_back :
            memRegion (fsp + 0x4d0#64) 48 ∗ ((fsp + 1280#64) ↦₆₄ sw.w5) ∗
              memRegion (fsp + 0x508#64) 192 ⊢
            memRegion (fsp + 0x4d0#64) 248 := by
          rw [ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 48) (k := 200)
                (b' := fsp + 1280#64) rfl (by bv_omega) (by decide),
              ProofLib.memRegion_split' (b := fsp + 1280#64) (n := 8) (k := 192)
                (b' := fsp + 0x508#64) rfl (by bv_omega) (by decide)]
          exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
        have hm1 := sepConj_mono (Entails.refl (memRegion (fsp + 0x240#64) 0x20))
          (sepConj_mono (r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
                (BitVec.ofNat 64 meG.name.bytes.length) hiMe)
            (sepConj_mono (Entails.refl (memRegion (fsp + 0x280#64) 0x20))
              (sepConj_mono (r3b_slot5_to_mem40 (fsp + 672#64) ⟨sw.w1, sw.w2, sw.w3, sw.w4, sw.w5⟩)
                (sepConj_mono (Entails.refl (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8)))
                  (sepConj_mono hpkm_back
                    (Entails.refl (memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8))))))))
        have heq_all : memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) =
            memRegion (fsp + 0x240#64) 0x20 ∗
              (memRegion (fsp + 0x260#64) 32 ∗
                (memRegion (fsp + 0x280#64) 0x20 ∗
                  (memRegion (fsp + 672#64) 40 ∗
                    (memRegion (fsp + 0x2c8#64) (0x4d0 - 0x2c8) ∗
                      (memRegion (fsp + 0x4d0#64) 248 ∗
                        memRegion (fsp + 0x5c8#64) (runLocalBytes - 0x5c8)))))) := by
          rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x280 0x20 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x2a0 40 runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x2c8 (0x4d0 - 0x2c8) runLocalBytes (by decide) (by decide),
              r3b_split_at fsp 0x4d0 248 runLocalBytes (by decide) (by decide)]
        rw [heq_all]
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1
        exact r3b_perm hm1 (by ac_rfl)
      subst hfsp
      rw [← hspm, hs_m.sp]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono hloc_back
            (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG ∗ runSaved s0 ∗
              memRegion (runFsp s0) 0x220 ∗
              (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((runFsp s0 + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((runFsp s0 + 0x238#64) ↦₆₄ cw4)) ∗
              stackAt (runFsp s0) (resStack - runFrame) ∗
              A.pool lim (M.stepEvents evs_drop st) sm ∗ anyHeap)))
          (by sep_ac_rfl))
        (by sep_ac_rfl))


set_option maxHeartbeats 800000 in
/-- First half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0x994 → R+0xaa0`),
delivering `VmPreserved s s'` to the continuation. -/
theorem r3b_recvP_shuf1_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (pqCap : BitVec 64) (w : r3b_W30) (t : r3b_W5) (z m : r3b_W30) (F : SepProp)
    (hs : InRunPlaced CodeOk s0 s 0x994)
    (hcap : pqCap.toNat < 2 ^ 63)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hk : ∀ s' : State,
      VmPreserved s s' →
      InRunPlaced CodeOk s0 s' 0xaa0 →
      s'.readReg64 (.gpr 8#5) = w.b0.w0 →
      s'.readReg64 (.gpr 9#5) = pqCap →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      s'.trace = s.trace →
      s'.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s'
        (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
          memRegion (runFsp s0 + 0x2a0#64) 40 ∗
          r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
          memRegion (runFsp s0 + 0x1750#64) 240 ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗
        r3b_slot5 (runFsp s0 + 0x2a0#64) t ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) z ∗
        r3b_slot30 (runFsp s0 + 0x1750#64) m ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0x994 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  have hcmn : ((pqCap + 1#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; bv_omega)
  generalize hfsp : runFsp s0 = fsp at hsp hx26 hx27 ⊢
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0xaa0) hs.inv
  rw [runPcPlaced_eq]
  dsimp only [r3b_slot30, r3b_slot5]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hx26 hx27 ⊢
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    subst hfsp
    let fsp := runFsp s0
    have hs' : InRunPlaced CodeOk s0 (r3b_stOf hinv') 0xaa0 :=
      r3b_inRun_step hs (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
        (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
    refine r3b_sepWPp_weaken_pre ?_
      (hk (r3b_stOf hinv') hvm hs'
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm]))
    try rw [hsp]
    have hc5 : ∀ (T : SepProp),
        ((fsp + 672#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 680#64) ↦₆₄ w.b0.w2) ∗
        ((fsp + 688#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 696#64) ↦₆₄ w.b0.w4) ∗
        ((fsp + 704#64) ↦₆₄ w.b1.w0) ∗ T ⊢ memRegion (fsp + 0x2a0#64) 40 ∗ T :=
      fun T => r3b_collapse5_flat (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (Entails.refl _)
    have hc30 : ∀ (T : SepProp),
        ((fsp + 5968#64) ↦₆₄ w.b0.w1) ∗ ((fsp + 5976#64) ↦₆₄ w.b0.w2) ∗
        ((fsp + 5984#64) ↦₆₄ w.b0.w3) ∗ ((fsp + 5992#64) ↦₆₄ w.b0.w4) ∗
        ((fsp + 6000#64) ↦₆₄ w.b1.w0) ∗ ((fsp + 6008#64) ↦₆₄ w.b1.w1) ∗
        ((fsp + 6016#64) ↦₆₄ w.b1.w2) ∗ ((fsp + 6024#64) ↦₆₄ w.b1.w3) ∗
        ((fsp + 6032#64) ↦₆₄ w.b1.w4) ∗ ((fsp + 6040#64) ↦₆₄ w.b2.w0) ∗
        ((fsp + 6048#64) ↦₆₄ w.b2.w1) ∗ ((fsp + 6056#64) ↦₆₄ w.b2.w2) ∗
        ((fsp + 6064#64) ↦₆₄ w.b2.w3) ∗ ((fsp + 6072#64) ↦₆₄ w.b2.w4) ∗
        ((fsp + 6080#64) ↦₆₄ w.b3.w0) ∗ ((fsp + 6088#64) ↦₆₄ w.b3.w1) ∗
        ((fsp + 6096#64) ↦₆₄ w.b3.w2) ∗ ((fsp + 6104#64) ↦₆₄ w.b3.w3) ∗
        ((fsp + 6112#64) ↦₆₄ w.b3.w4) ∗ ((fsp + 6120#64) ↦₆₄ w.b4.w0) ∗
        ((fsp + 6128#64) ↦₆₄ w.b4.w1) ∗ ((fsp + 6136#64) ↦₆₄ w.b4.w2) ∗
        ((fsp + 6144#64) ↦₆₄ w.b4.w3) ∗ ((fsp + 6152#64) ↦₆₄ w.b4.w4) ∗
        ((fsp + 6160#64) ↦₆₄ w.b5.w0) ∗ ((fsp + 6168#64) ↦₆₄ w.b5.w1) ∗
        ((fsp + 6176#64) ↦₆₄ w.b5.w2) ∗ ((fsp + 6184#64) ↦₆₄ w.b5.w3) ∗
        ((fsp + 6192#64) ↦₆₄ w.b5.w4) ∗ ((fsp + 6200#64) ↦₆₄ m.b5.w4) ∗ T ⊢
        memRegion (fsp + 0x1750#64) 240 ∗ T :=
      fun T => r3b_collapse30_flat
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
        (Entails.refl _)
    dsimp only [fsp, r3b_slot30, r3b_slot5, r3b_shufMid] at hc5 hc30 ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hc5 hc30 ⊢
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (Entails.trans (hc5 _) (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (hc30 _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux
