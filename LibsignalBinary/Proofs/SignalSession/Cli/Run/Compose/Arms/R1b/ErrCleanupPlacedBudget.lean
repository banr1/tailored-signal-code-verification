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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded OOM Stubs and Error Cleanup Tail for Arm `R1b`

Verifies the OOM panic stubs (`2d44`, `2d68`, `2d5c`, `2d74`) and budget-threaded cleanup tail
(`r1b_cleanup_2c34_placed`, `r1b_cleanup_2bf0_placed` and `RejectKPlacedEnv` wrappers, emitting
`FreeOnlyEvs`) on Block `579` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc allocFailedIn)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk inputOf ownedBytes runResAt runResSize sepWPp_weaken_pre storesAt)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data InRunPlaced PanicK RejectKind addrNameHeap addrUpperAt
   addrUpperAt_entails_memRegion protocolAddressAt_eq_parts r1b_CodeOk r1b_ErrCtxPlaced
   r1b_SpePayload r1b_StackBounds r1b_allocFailedIn_mono r1b_bind_state_placed
   r1b_cell64_cons r1b_errCommon r1b_errCore r1b_errFrameRest r1b_fsp_align
   r1b_pack_speOwnedAt r1b_region48_to_cells r1b_rejoin_errFrame rejectMem
   runFsp runLocals runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed r1b_call_dropSpeOwned_placed r1b_handle_error_panic_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

theorem sepWP_with_vm_oom {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp}
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
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
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

private theorem r1b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

private theorem r1b_addrNameHeap_to_ownedBytes_placed (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  dsimp only [addrNameHeap, ownedBytes]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hne⟩
  refine Entails.pure_right ⟨by simp, hle, hlt, hne⟩ (Entails.refl _)

theorem r1b_errCore_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : RunCall) (d : Init1Data) (s0 : State) :
    r1b_errCore (A.atState lim st s) g d s0 = r1b_errCore A.repAlloc g d s0 := rfl

theorem r1b_errCommon_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : RunCall) (d : Init1Data) (s0 : State)
    (resStack : Nat) :
    r1b_errCommon (A.atState lim st s) g d s0 resStack =
      r1b_errCore A.repAlloc g d s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ anyHeap := rfl

theorem r1b_SpePayload_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (x12 x9 x23 x27 x16 x14 x15 x28 x22 : BitVec 64) :
    r1b_SpePayload (A.atState lim st s) x12 x9 x23 x27 x16 x14 x15 x28 x22 =
      r1b_SpePayload A.repAlloc x12 x9 x23 x27 x16 x14 x15 x28 x22 := rfl

/-! ## OOM Panic Stubs (`2d44`, `2d68`, `2d5c`, `2d74`) -/

theorem r1b_oom_2d44_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d44) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  change s.pc = (blkPl_579).base + 0x2d44#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm]; exact List.prefix_rfl))

theorem r1b_oom_2d68_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d68) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  change s.pc = (blkPl_579).base + 0x2d68#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm]; exact List.prefix_rfl))

theorem r1b_oom_2d5c_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d5c) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x120#64) ↦₆₄ v0) ∗ F) Q Qp oom := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2d5c#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm]; exact List.prefix_rfl))

theorem r1b_oom_2d74_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d74) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x158#64) ↦₆₄ v0) ∗ F) Q Qp oom := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2d74#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm]; exact List.prefix_rfl))

/-! ## Budget-Threaded Cleanup Tail (`2c68 ← 2c54 ← 2c34 ← 2bf0`) -/

private theorem r1b_cleanup_2c68_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htrace : s0.trace <+: s.trace)
    (hhist : CryptoVerification.SignalSession.Cli.RunCompose.RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion ((runFsp s0) + 0x110#64) 8 ∗ memRegion ((runFsp s0) + 0x11c#64) 4 ∗
        memRegion ((runFsp s0) + 0x120#64) 16 ∗ memRegion ((runFsp s0) + 0x150#64) 16 ∗
        memRegion ((runFsp s0) + 0x168#64) 24 ∗ memRegion ((runFsp s0) + 0x188#64) 48 ∗
        memRegion ((runFsp s0) + 0x1b8#64) 24 ∗
        protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  have haddr : protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) =
      ((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ∗ addrNameHeap A.repAlloc d.peerG := by
    rw [protocolAddressAt_eq_parts A.repAlloc d.peerG (fsp + 0x2a0#64)]
    have h2a8 : fsp + 0x2a0#64 + 8#64 = fsp + 0x2a8#64 := by bv_omega
    have h2b0 : fsp + 0x2a0#64 + 16#64 = fsp + 0x2b0#64 := by bv_omega
    rw [h2a8, h2b0]
  have hpeer32 : ∀ capv ptrv : BitVec 64,
      ((fsp + 0x2a0#64) ↦₆₄ capv) ∗ ((fsp + 0x2a8#64) ↦₆₄ ptrv) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ⊢ memRegion (fsp + 0x2a0#64) 32 := by
    intro capv ptrv
    have hup := addrUpperAt_entails_memRegion (fsp + 0x2b0#64) d.peerG
    have h2a8 : fsp + 0x2b0#64 = (fsp + 0x2a8#64) + 8#64 := by bv_omega
    have h2a0 : fsp + 0x2a8#64 = (fsp + 0x2a0#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hup)) ?_
    refine Entails.trans (sepConj_mono_right (by rw [h2a8]; exact r1b_cell64_cons ptrv (by decide))) ?_
    rw [h2a0]; exact r1b_cell64_cons capv (by decide)
  rw [haddr]
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2c68#64 at hpc
  by_cases hcap : d.peerG.name.cap = 0#64
  · rw [hcap]
    apply r1b_seq_lscro_oom (mid := runPcPlaced 0x2c7c) hinv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hpool_eq : A.pool lim st s = A.pool lim st sm := by simp only [hsm, wp_norm, arm64_norm]
    have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c7c := {
      pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    have hrej_m : AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sm := {
      base := hst_m
      x19 := by simpa [hsm, arm64_norm] using hx19
      preRegs := fun h => by cases h
      trace := by simpa [hsm, arm64_norm] using htrace
      hist := ⟨by simpa [hsm, arm64_norm] using hhist.1,
        by simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine sepWPp_weaken_pre ?_ (hrej sm [] FreeOnlyEvs.nil hrej_m)
    have hrej_eq :
        rejectMem (A.atState lim (M.stepEvents [] st) sm)
          g StoresGhost.opened .postDispatch s0 resStack =
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗ anyHeap := rfl
    rw [hrej_eq, hpool_eq]
    have h1 := hpeer32 0#64 d.peerG.name.ptr
    have h2 : addrNameHeap A.repAlloc d.peerG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗
        memRegion (runFsp s0 + 0x11c#64) 4 ∗ memRegion (runFsp s0 + 0x120#64) 16 ∗
        memRegion (runFsp s0 + 0x150#64) 16 ∗ memRegion (runFsp s0 + 0x168#64) 24 ∗
        memRegion (runFsp s0 + 0x188#64) 48 ∗ memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
      (addrNameHeap A.repAlloc d.peerG ∗ anyHeap) by sep_ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_
        (sepConj_mono_right (sepConj_mono_right h2))))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))
  · have hcap_f : (d.peerG.name.cap == 0#64) = false := beq_false_of_ne hcap
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hpool_eq : A.pool lim st s = A.pool lim st sm := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_sp : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c7c := by simp only [hsm, arm64_norm]
    dsimp only [fsp]
    rw [hpool_eq]
    apply sepWPp_weaken_pre
    · refine Entails.trans (Entails.of_eq (show _ =
        addrNameHeap A.repAlloc d.peerG ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          memRegion (runFsp s0 + 0x1b8#64) 24 ∗
          (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗
            ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by sep_ac_rfl))
        (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes_placed A.repAlloc d.peerG))
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := d.peerG.name.cap)
      (ptr := d.peerG.name.ptr) (len := BitVec.ofNat 64 d.peerG.name.bytes.length)
      (bs := d.peerG.name.bytes) hh hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm])
      (by simp only [hsm, arm64_norm]) hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    have hrej_f : AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf := {
      base := hin_f
      x19 := hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19)
      preRegs := fun h => by cases h
      trace := htr_f ▸ (by simpa [hsm, arm64_norm] using htrace)
      hist := ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
        by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine sepWPp_weaken_pre ?_
      (hrej sf (rustDeallocEvents d.peerG.name.cap.toNat 1)
        (FreeOnlyEvs.singleton 1 d.peerG.name.cap.toNat) hrej_f)
    have hrej_eq :
        rejectMem
          (A.atState lim (M.stepEvents (rustDeallocEvents d.peerG.name.cap.toNat 1) st) sf)
          g StoresGhost.opened .postDispatch s0 resStack =
        (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ runLocals (runFsp s0) [] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents d.peerG.name.cap.toNat 1) st) sf ∗
          anyHeap := rfl
    rw [hrej_eq]
    have h1 := hpeer32 d.peerG.name.cap d.peerG.name.ptr
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗
        memRegion (runFsp s0 + 0x11c#64) 4 ∗ memRegion (runFsp s0 + 0x120#64) 16 ∗
        memRegion (runFsp s0 + 0x150#64) 16 ∗ memRegion (runFsp s0 + 0x168#64) 24 ∗
        memRegion (runFsp s0 + 0x188#64) 48 ∗ memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗
          ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗
      A.pool lim (M.stepEvents (rustDeallocEvents d.peerG.name.cap.toNat 1) st) sf ∗
      anyHeap by sep_ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))

private theorem r1b_cleanup_2c54_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htrace : s0.trace <+: s.trace)
    (hhist : CryptoVerification.SignalSession.Cli.RunCompose.RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        runSaved s0 ∗ r1b_errFrameRest fsp ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x1b8#64) 24 ∗
        protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  change s.pc = (blkPl_579).base + 0x2c54#64 at hpc
  by_cases hcap : d.dirCap = 0#64
  · rw [hcap] at hx24 ⊢
    apply r1b_seq_lscro_oom (mid := runPcPlaced 0x2c68) hinv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hpool_eq : A.pool lim st s = A.pool lim st sm := by simp only [hsm, wp_norm, arm64_norm]
    have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c68 := {
      pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    rw [hpool_eq]
    refine sepWPp_weaken_pre ?_ (r1b_cleanup_2c68_placed (d := d) hh hbnd hst_m
      (by simpa [hsm, arm64_norm] using hx19) (by simpa [hsm, arm64_norm] using htrace)
      ⟨by simpa [hsm, arm64_norm] using hhist.1, by simpa [hsm, arm64_norm] using hhist.2⟩
      hans hpanic hrej)
    have hdrop_dir :
        ownedBytes A.repAlloc 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap ⊢
          anyHeap := entails_anyHeap _
    dsimp only [fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        protocolAddressAt A.repAlloc d.peerG (runFsp s0 + 0x2a0#64) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (ownedBytes A.repAlloc 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap)
      by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hdrop_dir))))))))))))))))
  · have hcap_f : (d.dirCap == 0#64) = false := beq_false_of_ne hcap
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hpool_eq : A.pool lim st s = A.pool lim st sm := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_sp : sm.sp = fsp := by simpa [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c68 := by simp [hsm, arm64_norm]
    dsimp only [fsp] at hsm_sp ⊢
    rw [hpool_eq]
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
      (runResAt A.repAlloc cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        protocolAddressAt A.repAlloc d.peerG (runFsp s0 + 0x2a0#64) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by sep_ac_rfl)) ?_
    refine r1b_call_dealloc_ownedBytes_placed (cap := d.dirCap) (ptr := d.dirPtr)
      (len := BitVec.ofNat 64 d.dir.length) (bs := d.dir) (Q := Q) hh hbnd hinv_m hsm_pc
      (by simp [hsm, arm64_norm, hrun]) hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (r1b_cleanup_2c68_placed (d := d) hh hbnd hin_f
        (hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19))
        (htr_f ▸ (by simpa [hsm, arm64_norm] using htrace))
        ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
          by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
        hans hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
    rw [← M.stepEvents_append]
    exact hrej sf2 (rustDeallocEvents d.dirCap.toNat 1 ++ evs2)
      (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 d.dirCap.toNat) hfo2) hrej2

theorem r1b_cleanup_2c34_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2c34)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  dsimp only [r1b_errCore]
  rw [hfsp_eq]
  have h1b8_24 :
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ⊢ memRegion (fsp + 0x1b8#64) 24 := by
    have hc8 : fsp + 0x1c8#64 = (fsp + 0x1c0#64) + 8#64 := by bv_omega
    have hc0 : fsp + 0x1c0#64 = (fsp + 0x1b8#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _))) ?_
    refine Entails.trans (sepConj_mono_right (by rw [hc8]; exact r1b_cell64_cons d.dirCap (by decide))) ?_
    rw [hc0]; exact r1b_cell64_cons d.meG.name.ptr (by decide)
  have hres_split : memRegion g.res runResSize =
      (∃∗ vres : BitVec 64, g.res ↦₆₄ vres) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    conv_lhs => rw [show runResSize = 8 + (runResSize - 8) from rfl]
    rw [ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide), ProofLib.memRegion_eight]
  have hx19 := hc.x19; have hx20 := hc.x20; have hx21 := hc.x21
  have htrace := hc.trace; have hhist := hc.hist; have hans := hc.ans
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun vres => ?_
  generalize hstP : storesAt A.repAlloc g.stores StoresGhost.opened = stProp
  generalize hpeerP : protocolAddressAt A.repAlloc d.peerG (fsp + 0x2a0#64) = peerProp
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2c34#64 at hpc
  by_cases hcap : d.meG.name.cap = 0#64
  · rw [hcap] at hx21
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2c54#64) hinv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
      rw [← hsm] at hvm
      refine SepWPp.transport_budgetPool hvm (hnext := ?_)
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c54 := {
        pc := by simp only [hsm, wp_norm, arm64_norm]
        run := by simp only [hsm, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
        fp := by simpa only [hsm, wp_norm, arm64_norm] using hfp
        inv := hinv_m
        vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0
      }
      refine sepWPp_weaken_pre ?_ (r1b_cleanup_2c54_placed (d := d) hh hbnd hst_m
        (by simpa only [hsm, wp_norm, arm64_norm] using hx19)
        (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm])
        (by simpa only [hsm, wp_norm, arm64_norm] using htrace)
        ⟨by simpa only [hsm, wp_norm, arm64_norm] using hhist.1,
          by simpa only [hsm, wp_norm, arm64_norm] using hhist.2⟩
        hans hpanic hrej)
      have hdrop_me : addrNameHeap A.repAlloc d.meG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
      dsimp only [runResAt]
      rw [hstP, hpeerP]
      dsimp only [fsp] at h1b8_24 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
        memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
          ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
        peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (addrNameHeap A.repAlloc d.meG ∗ anyHeap) by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono h1b8_24 (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hdrop_me)))))))))))))))))
    )
  · have hcap_f : (d.meG.name.cap == 0#64) = false := beq_false_of_ne hcap
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
      refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
      rw [← hsm] at hvm
      refine SepWPp.transport_budgetPool hvm (hnext := ?_)
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hsm_sp : sm.sp = fsp := by simpa only [hsm, wp_norm, arm64_norm] using hsp
      have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 :=
        by simpa only [hsm, wp_norm, arm64_norm] using hfp
      have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
        simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
      have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, wp_norm, arm64_norm]
      have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c54 := by simp only [hsm, wp_norm, arm64_norm]
      dsimp only [fsp] at hsm_sp h1b8_24 ⊢
      apply sepWPp_weaken_pre
      · refine Entails.trans (Entails.of_eq (show _ =
          addrNameHeap A.repAlloc d.meG ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
          (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
            memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
            runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
            memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
            memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
            memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
            (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
              ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
            peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
            anyHeap) by sep_ac_rfl))
          (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes_placed A.repAlloc d.meG))
      refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := d.meG.name.cap)
        (ptr := d.meG.name.ptr) (len := BitVec.ofNat 64 d.meG.name.bytes.length)
        (bs := d.meG.name.bytes) hh hbnd hinv_m hsm_pc (by simp only [hsm, wp_norm, arm64_norm, hrun])
        hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) hcap hpanic ?_
      intro sf hin_f hcs_f hfs_f htr_f
      refine sepWPp_weaken_pre ?_
        (r1b_cleanup_2c54_placed (st := M.stepEvents (rustDeallocEvents d.meG.name.cap.toNat 1) st)
          (d := d) hh hbnd hin_f
          (hcs_f.1.trans (by simpa only [hsm, wp_norm, arm64_norm] using hx19))
          (hcs_f.2.2.2.1.trans (by simp only [hsm, wp_norm, arm64_norm]))
          (hcs_f.2.2.2.2.2.1.trans (by simp only [hsm, wp_norm, arm64_norm]))
          (htr_f ▸ (by simpa only [hsm, wp_norm, arm64_norm] using htrace))
          ⟨by rw [hfs_f]; simpa only [hsm, wp_norm, arm64_norm] using hhist.1,
            by rw [htr_f]; simpa only [hsm, wp_norm, arm64_norm] using hhist.2⟩
          hans hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
      · dsimp only [runResAt]
        rw [hstP, hpeerP]
        refine Entails.trans (Entails.of_eq (show _ =
          ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
            ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents d.meG.name.cap.toNat 1) st) sf ∗
          anyHeap by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left h1b8_24)))))))))))))
      · rw [← M.stepEvents_append]
        exact hrej sf2 (rustDeallocEvents d.meG.name.cap.toNat 1 ++ evs2)
          (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 d.meG.name.cap.toNat) hfo2) hrej2
    )

theorem r1b_cleanup_2bf0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2bf0)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq]
  rw [r1b_region48_to_cells (fsp + 0x4d0#64)]
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have ho8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
  have ho16 : fsp + 0x4d0#64 + 16#64 = fsp + 0x4e0#64 := by bv_omega
  have ho24 : fsp + 0x4d0#64 + 24#64 = fsp + 0x4e8#64 := by bv_omega
  have ho32 : fsp + 0x4d0#64 + 32#64 = fsp + 0x4f0#64 := by bv_omega
  have ho40 : fsp + 0x4d0#64 + 40#64 = fsp + 0x4f8#64 := by bv_omega
  rw [ho8, ho16, ho24, ho32, ho40]
  apply sepWPp_weaken_pre
  · exact Entails.of_eq (show _ =
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        ((fsp + 0x4d0#64) ↦₆₄ w0 ∗ (fsp + 0x4d8#64) ↦₆₄ w1 ∗
          (fsp + 0x4e0#64) ↦₆₄ w2 ∗ (fsp + 0x4e8#64) ↦₆₄ w3 ∗
          (fsp + 0x4f0#64) ↦₆₄ w4 ∗ (fsp + 0x4f8#64) ↦₆₄ w5)) ∗
      (errCore ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48) by sep_ac_rfl)
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2bf0#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsmpl.base 553) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    refine SepWPp.transport_budgetPool hvm (hnext := ?_)
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_sp : sm.sp = fsp := by simpa only [hsm, wp_norm, arm64_norm] using hsp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 :=
      by simpa only [hsm, wp_norm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsmpl.base 553 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c34 := by simp only [hsm, wp_norm, arm64_norm]
    have hpack_all : ∀ w1' w2' w3' : BitVec 64,
        w1' = ((s.readReg64 (.gpr 9#5) &&& 0xffffffff#64) ||| (s.readReg64 (.gpr 23#5) <<< 32)) →
        w2' = ((s.readReg64 (.gpr 27#5) &&& 0x00ffffffffffffff#64) |||
          ((s.readReg64 (.gpr 16#5) &&& 0xff#64) <<< 56)) →
        w3' = ((((s.readReg64 (.gpr 14#5) &&& 16777215#64) <<< 32) |||
          (s.readReg64 (.gpr 28#5) <<< 56)) |||
          (((s.readReg64 (.gpr 15#5) <<< 8) &&& 0xffffff00#64) |||
            (s.readReg64 (.gpr 22#5) &&& 0xff#64))) →
        r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        ((fsp + 0x4d0#64) ↦₆₄ s.readReg64 (.gpr 12#5) ∗
          (fsp + 0x4d8#64) ↦₆₄ w1' ∗ (fsp + 0x4e0#64) ↦₆₄ w2' ∗
          (fsp + 0x4e8#64) ↦₆₄ w3' ∗ (fsp + 0x4f0#64) ↦₆₄ s.readReg64 (.gpr 11#5) ∗
          (fsp + 0x4f8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ⊢
        ∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x4d0#64) k := by
      intro w1' w2' w3' h1 h2 h3
      have hp := r1b_pack_speOwnedAt A.repAlloc (fsp + 0x4d0#64) (s.readReg64 (.gpr 12#5))
        w1' w2' w3' (s.readReg64 (.gpr 11#5)) (s.readReg64 (.gpr 13#5))
        (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) h1 h2 h3
      rw [ho8, ho16, ho24, ho32, ho40] at hp
      exact hp
    have hgroup : ∀ (P0 P1 C0 C1 C2 C3 C4 C5 Rest : SepProp),
        P0 ∗ P1 ∗ C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5 ∗ Rest =
          P0 ∗ (P1 ∗ (C0 ∗ C1 ∗ C2 ∗ C3 ∗ C4 ∗ C5)) ∗ Rest :=
      fun _ _ _ _ _ _ _ _ _ => by sep_ac_rfl
    rw [hgroup]
    apply sepWPp_weaken_pre
    · exact sepConj_mono_right
        (sepConj_mono_left (hpack_all _ _ _ (by bv_bits) (by bv_bits) (by bv_bits)))
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun k => ?_
    dsimp only [fsp] at hsm_sp ⊢
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) k ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
      (errCore ∗ anyHeap ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗
        memRegion (runFsp s0 + 0x11c#64) 4 ∗ memRegion (runFsp s0 + 0x120#64) 16 ∗
        memRegion (runFsp s0 + 0x150#64) 16 ∗ memRegion (runFsp s0 + 0x168#64) 24 ∗
        memRegion (runFsp s0 + 0x188#64) 48) by sep_ac_rfl)) ?_
    refine r1b_call_dropSpeOwned_placed (a := runFsp s0 + 0x4d0#64) (k := k) (Q := Q) hh hdrop
      hbnd hinv_m hsm_pc (by simp only [hsm, wp_norm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, wp_norm, arm64_norm]; dsimp only [fsp, runFsp, runFrame]; bv_omega)
      hpanic ?_
    intro sf evs1 hfo1 hin_f hcs_f hfs_f htr_f
    have hc_f : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf 0x2c34 := {
      st := hin_f
      x19 := hcs_f.1.trans (by simpa only [hsm, wp_norm, arm64_norm] using hc.x19)
      x20 := hcs_f.2.1.trans (by simpa only [hsm, wp_norm, arm64_norm] using hc.x20)
      x21 := hcs_f.2.2.1.trans (by simpa only [hsm, wp_norm, arm64_norm] using hc.x21)
      trace := htr_f ▸ (by simpa only [hsm, wp_norm, arm64_norm] using hc.trace)
      hist := ⟨by rw [hfs_f]; simpa only [hsm, wp_norm, arm64_norm] using hc.hist.1,
        by rw [htr_f]; simpa only [hsm, wp_norm, arm64_norm] using hc.hist.2⟩
      ans := hc.ans
    }
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2c34_placed (st := M.stepEvents evs1 st) hh hbnd hc_f hpanic
        fun sf2 evs2 hfo2 hrej2 => ?_)
    · rw [r1b_errCommon_atState_eq, herrCore]
      exact Entails.of_eq (by sep_ac_rfl)
    · rw [← M.stepEvents_append]
      exact hrej sf2 (evs1 ++ evs2) (FreeOnlyEvs.append hfo1 hfo2) hrej2
  )

/-! ## `RejectKPlacedEnv` Wrappers -/

theorem r1b_cleanup_2c34_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2c34)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2c34_placed hh hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_cleanup_2bf0_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2bf0)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2bf0_placed hh hdrop hbnd hc hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
