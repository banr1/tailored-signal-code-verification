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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R1c` Placed Tail Stepping

Relocatable (`[LibsignalPlacement]`) stepping proofs on Block `579` (`runProgPlaced H`) with exact
`FreeOnlyEvs` deallocation event lists under `RustCliAllocBudget M` for the Arm `R1c` success tail
(`R+0x2908 → R+0xf8c`) and error deallocation tail (`R+0x2a20 → R+0x2c7c`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliWrOk namedWrites)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (AtJoinPlaced AtRejectPlaced Bytes InRunPlaced Init2Data RejectKind RunHistOk addrNameHeap joinMem rejectMem runFsp runLocalBytes runLocals runLocalsFrom runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers (R1cCodeOk r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2 r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState r1c_calleeSavedVRegs_writeReg64 r1c_empty_vecU8 r1c_errCore r1c_extractLsb_append_hi r1c_extractLsb_append_lo r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_hist_of_eq r1c_lowCells r1c_lowCells_to_mem1d0 r1c_lowGaps r1c_lowNoDir r1c_lowNoMePtr r1c_mem_setPState r1c_nameHeap_dealloc r1c_nameHeap_zero r1c_okCore r1c_readReg64_setPState r1c_rewrite_front r1c_sepWPp_exists_left r1c_sepWPp_pure_left r1c_sepWPp_weaken_pre r1c_spAligned r1c_sp_setPState r1c_split_at r1c_status_setPState r1c_symtab_setPState r1c_trace_setPState)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cHelpersPlacedBudget
  (r1c_call_dealloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlaced JoinKPlacedEnv RejectKPlaced RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r1c_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runPcPlaced_eq, BitVec.ofNat_eq_ofNat, runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

/-! ## 1. Exact Deallocation Event Lists & `FreeOnlyEvs` Proofs -/

/-- Exact deallocation event list for dropping a `String`/`Vec<u8>` buffer with capacity `cap`
(`align = 1`). -/
def r1cFreeCapEvs (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

def r1cFreePeerEvs (peerG : AddrGhost) : List AllocEvent :=
  r1cFreeCapEvs peerG.name.cap

def r1cFreeDirPeerEvs (d : Init2Data) : List AllocEvent :=
  r1cFreeCapEvs d.dirCap ++ r1cFreePeerEvs d.peerG

def r1cFreeNamesEvs (d : Init2Data) : List AllocEvent :=
  r1cFreeCapEvs d.meG.name.cap ++ r1cFreeDirPeerEvs d

/-- Exact deallocation event list for `r1c_ok_tail` (`spkSig` 64 B, `kpk` 1568 B, `kpkSig` 64 B,
followed by `me`, `dir`, `peer` names). -/
def r1cOkTailEvs (d : Init2Data) : List AllocEvent :=
  rustDeallocEvents 64 1 ++ rustDeallocEvents 1568 1 ++ rustDeallocEvents 64 1 ++
    r1cFreeNamesEvs d

theorem r1cFreeCapEvs_freeOnly (cap : BitVec 64) : FreeOnlyEvs (r1cFreeCapEvs cap) := by
  unfold r1cFreeCapEvs
  split
  · exact LibsignalBinary.Heap.FreeOnlyEvs.nil
  · exact LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 cap.toNat

theorem r1cFreePeerEvs_freeOnly (peerG : AddrGhost) : FreeOnlyEvs (r1cFreePeerEvs peerG) :=
  r1cFreeCapEvs_freeOnly peerG.name.cap

theorem r1cFreeDirPeerEvs_freeOnly (d : Init2Data) : FreeOnlyEvs (r1cFreeDirPeerEvs d) :=
  LibsignalBinary.Heap.FreeOnlyEvs.append (r1cFreeCapEvs_freeOnly d.dirCap) (r1cFreePeerEvs_freeOnly d.peerG)

theorem r1cFreeNamesEvs_freeOnly (d : Init2Data) : FreeOnlyEvs (r1cFreeNamesEvs d) :=
  LibsignalBinary.Heap.FreeOnlyEvs.append (r1cFreeCapEvs_freeOnly d.meG.name.cap) (r1cFreeDirPeerEvs_freeOnly d)

theorem r1cOkTailEvs_freeOnly (d : Init2Data) : FreeOnlyEvs (r1cOkTailEvs d) :=
  LibsignalBinary.Heap.FreeOnlyEvs.append
    (LibsignalBinary.Heap.FreeOnlyEvs.append
      (LibsignalBinary.Heap.FreeOnlyEvs.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 64) (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 1568))
      (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 64))
    (r1cFreeNamesEvs_freeOnly d)

/-! ## 2. VM-Preserving Frame Sequencer & `atState` Footprint Bridges -/

private theorem r1c_frame_seq_vm [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : R1cCodeOk s.mem) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post s1 ∧ P1 = P'))
    (hk : ∀ s1 : State, VmPreserved s s1 → R1cCodeOk s1.mem → s1.pc = mid →
      s1.status = .Running → post s1 → SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hvm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 hvm1 (hinv.of_keepsFrozen hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

private theorem joinMem_atState_empty_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (g' : StoresGhost) (s0 : State) (resStack : Nat) :
    joinMem (A.atState lim st s) g g' [] s0 resStack =
      runLocals (runFsp s0) [(0x208, 24, vecU8 A.repAlloc (runFsp s0 + 0x208#64) [])] ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0) := by
  have hlive :
      joinMem (A.atState lim st s) g g' [] s0 resStack =
        joinMem { pool := A.pool lim st s, live := A.repAlloc.live } g g' [] s0 resStack := rfl
  rw [hlive]
  dsimp only [joinMem, r1c_okCore]
  change _ =
    runLocals (runFsp s0)
        [(0x208, 24, vecU8 { pool := A.pool lim st s, live := A.repAlloc.live }
          (runFsp s0 + 0x208#64) [])] ∗
      (stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗
        r1c_okCore { pool := A.pool lim st s, live := A.repAlloc.live } g g' s0)
  dsimp only [r1c_okCore]
  sep_ac_rfl

private theorem rejectMem_atState_postDispatch_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (g' : StoresGhost) (s0 : State) (resStack : Nat) :
    rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack =
      runLocals (runFsp s0) [] ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0) := by
  have hlive :
      rejectMem (A.atState lim st s) g g' .postDispatch s0 resStack =
        rejectMem { pool := A.pool lim st s, live := A.repAlloc.live }
          g g' .postDispatch s0 resStack := rfl
  rw [hlive]
  dsimp only [rejectMem, r1c_errCore]
  change _ =
    runLocals (runFsp s0) [] ∗
      (stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗
        r1c_errCore { pool := A.pool lim st s, live := A.repAlloc.live } g g' s0)
  dsimp only [r1c_errCore]
  sep_ac_rfl

/-! ## 3. Success Tail (`R+0x2908 → R+0x2960 → R+0x2974 → R+0x2988 → R+0xf8c`) -/

theorem r1c_ok_free_peer [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2988)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' [] (M.stepEvents (r1cFreePeerEvs peerG) st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp
  let mid := memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_okCore A.repAlloc g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢
      runLocals fsp [(0x208, 24, vecU8 A.repAlloc (fsp + 0x208#64) [])] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero, mid]
    rw [show fsp + BitVec.ofNat 64 0 = fsp by bv_omega,
        show (0x208 : Nat) + 24 = 0x220 from rfl,
        r1c_split_at fsp 0x220 (0x2a0 - 0x220) runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide)]
    exact r1c_rewrite_front
      (memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by sep_ac_rfl) (by sep_ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' [] st := by
      simpa [r1cFreePeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0xf8c) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]
      clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hat : AtJoinPlaced R1cCodeOk g g' [] s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1, x20 := hx20_1
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_ (hjoin s1 st g' [] hat henv0)
    rw [joinMem_atState_empty_eq]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗ core)
      hrejoin_peer (by sep_ac_rfl) (by dsimp only [core, fsp])
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' [] (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r1cFreePeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced 0xf8c ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hat : AtJoinPlaced R1cCodeOk g g' [] s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1
        x20 := hx20_2.trans hx20_1
        trace := (htr2.trans htr1) ▸ htr
        hist := r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_
      (hjoin s2 (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' [] hat henv1)
    rw [joinMem_atState_empty_eq]
    exact r1c_rewrite_front
      (stackAt fsp (resStack - runFrame) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) s2 ∗ core)
      hrejoin_peer (by sep_ac_rfl) (by dsimp only [core, fsp])

theorem r1c_ok_free_dir [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2974)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' [] (M.stepEvents (r1cFreeDirPeerEvs d) st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  let rest := memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A.repAlloc d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0
  have hlow208 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ⊢
      memRegion fsp 0x208 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x208 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  have hlow_eq : (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      r1c_lowNoDir fsp d = r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoDir]; sep_ac_rfl
  by_cases hcap : d.dirCap = 0#64
  · have henv0 : EnvAt g' [] (M.stepEvents (r1cFreePeerEvs d.peerG) st) := by
      simpa [r1cFreeDirPeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2988) s
        ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowNoDir fsp d ∗ rest)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc dirG hcap))
        (Entails.of_eq (by dsimp only [rest]; rw [emp_sepConj, ← hlow_eq]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    dsimp only [rest]
    rw [← A.pool_transport lim st s s1 hvm1]
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2988 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 hs1 hx19_1 hx20_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr henv0 hjoin)
    exact r1c_rewrite_front
      (vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗ r1c_okCore A.repAlloc g g' s0)
      hlow208 (by rw [← hlow_eq]; sep_ac_rfl) (by dsimp only [fsp]; sep_ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' []
        (M.stepEvents (r1cFreePeerEvs d.peerG)
          (M.stepEvents (rustDeallocEvents d.dirCap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r1cFreeDirPeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced 0x2988 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        r1c_lowNoDir fsp d ∗ rest)
      hs.inv (Entails.of_eq (by dsimp only [dirG, rest, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; rw [← hlow_eq]; sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    dsimp only [rest]
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        ((((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          r1c_lowNoDir fsp d ∗
          memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
          vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
          memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
          addrNameHeap A.repAlloc d.peerG ∗
          (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗
          memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_okCore A.repAlloc g g' s0))
      (Entails.of_eq (by sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2988 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1) (hx20_2.trans hx20_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans hwr henv1 hjoin)
    exact r1c_rewrite_front
      (vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents d.dirCap.toNat 1) st) s2 ∗
        r1c_okCore A.repAlloc g g' s0)
      hlow208 (by rw [← hlow_eq]; sep_ac_rfl) (by dsimp only [fsp]; sep_ac_rfl)

theorem r1c_ok_free_me [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' [] (M.stepEvents (r1cFreeNamesEvs d) st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  let afterLow := memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A.repAlloc d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hlow_eq : ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowNoMePtr fsp d =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoMePtr]; sep_ac_rfl
  by_cases hcap : d.meG.name.cap = 0#64
  · have henv0 : EnvAt g' [] (M.stepEvents (r1cFreeDirPeerEvs d) st) := by
      simpa [r1cFreeNamesEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2974) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = emp) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq]; rw [hcap] at hx21
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := addrNameHeap A.repAlloc dirG ∗ r1c_lowCells fsp d ∗ afterLow ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc d.meG hcap))
        (Entails.of_eq (by dsimp only [afterLow]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2974 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 hs1 hx19_1 hx20_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans hwr henv0 hjoin)
    exact Entails.of_eq (by dsimp only [afterLow, dirG, fsp]; rw [emp_sepConj]; sep_ac_rfl)
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' []
        (M.stepEvents (r1cFreeDirPeerEvs d)
          (M.stepEvents (rustDeallocEvents d.meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r1cFreeNamesEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced 0x2974 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)) := by
      have hpc := hs.pc
      rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        addrNameHeap A.repAlloc dirG ∗ r1c_lowNoMePtr fsp d ∗ afterLow ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [afterLow, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; rw [← hlow_eq]; sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        (((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
          addrNameHeap A.repAlloc dirG ∗ r1c_lowNoMePtr fsp d ∗ afterLow ∗
          r1c_okCore A.repAlloc g g' s0))
      (Entails.of_eq (by sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2974 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1) (hx20_2.trans hx20_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans hwr henv1 hjoin)
    exact Entails.of_eq (by dsimp only [afterLow, dirG, fsp]; rw [← hlow_eq]; sep_ac_rfl)

theorem r1c_ok_tail [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2908)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' [] (M.stepEvents (r1cOkTailEvs d) st))
    (hjoin : JoinKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  have hcarve : memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2)) ∗
          memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
          memRegion (fsp + 0x220#64) (0x2a0 - 0x220) := by
    rw [r1c_split_at fsp 0x1d0 (0x208 - 0x1d0) 0x2a0 (by decide) (by decide),
        show (0x1d0 : Nat) + (0x208 - 0x1d0) = 0x208 from rfl,
        r1c_split_at fsp 0x208 24 0x2a0 (by decide) (by decide),
        show (0x208 : Nat) + 24 = 0x220 from rfl]
    rw [ProofLib.memRegion_split' (b := fsp + 520#64) (n := 8) (k := 16) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 528#64) (n := 8) (k := 8) (b' := fsp + 536#64) rfl (by bv_omega) (by decide)]
    simp only [ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.of_eq (by sep_ac_rfl))))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      hcarve (by sep_ac_rfl) rfl)
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro v0
  apply r1c_sepWPp_exists_left; intro v1
  apply r1c_sepWPp_exists_left; intro v2
  let lowRest := ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hlow_eq :
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ lowRest =
      r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, lowRest]; sep_ac_rfl
  let tailHold := addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
    addrNameHeap A.repAlloc d.peerG ∗
    lowRest ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_okCore A.repAlloc g g' s0
  have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
      ((((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPcPlaced 0x2930 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.spkSigPtr ∧ s1.readReg64 .x1 = 64#64 ∧ s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = ((((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗
            ((fsp + 0x218#64) ↦₆₄ 0#64)) ∗
          (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))) := by
    have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
    have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := hs.spAligned_cur
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s.sp from hsp.symm]; clear hsp
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ tailHold)
    hs.inv (Entails.of_eq (by dsimp only [tailHold]; rw [← hlow_eq]; sep_ac_rfl)) hstep1
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm1]
  have hv8 : (((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗
      ((fsp + 0x218#64) ↦₆₄ 0#64)) ⊢ vecU8 A.repAlloc (fsp + 0x208#64) [] := by
    rw [show fsp + 0x210#64 = (fsp + 0x208#64) + 8#64 by bv_omega,
        show fsp + 0x218#64 = (fsp + 0x208#64) + 16#64 by bv_omega]
    exact r1c_empty_vecU8 A.repAlloc (fsp + 0x208#64)
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
      (vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ tailHold))
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗ tailHold)
      hv8 (by sep_ac_rfl) (by sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
      hx0_1 (by rw [hx1_1]; rfl) hx2_1 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  let st1 := M.stepEvents (rustDeallocEvents 64 1) st
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, _, _, _, _, _, _, hfp2, hv2⟩
  have hstep2 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s2
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s3 P3 => VmPreserved s2 s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          s3.readReg64 .lr = runPcPlaced 0x2948 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 .x0 = d.kpkPtr ∧ s3.readReg64 .x1 = 1568#64 ∧ s3.readReg64 .x2 = 1#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P3 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))) := by
    rw [runPcPlaced_eq] at hpc2
    have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
    have hx19' := hx19_2.trans hx19_1; have hx20' := hx20_2.trans hx20_1
    have hx21' := hx21_2.trans hx21_1
    have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s2.sp from hsp2.symm]; clear hsp2
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s2 ∗ tailHold)
    hinv2 (Entails.of_eq (by dsimp only [fsp, st1]; sep_ac_rfl)) hstep2
    fun s3 hvm3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx21_3⟩ => ?_
  rw [← A.pool_transport lim st1 s2 s3 hvm3]
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s3 ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        vecU8 A.repAlloc (fsp + 0x208#64) [] ∗ tailHold))
    (Entails.of_eq (by sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv3 hpc3 hrun3 hsp3 hlr3
      hx0_3 (by rw [hx1_3]; rfl) hx2_3 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s4 hinv4 hpc4 hrun4 hsp4 hcs4 hfs4 htr4 => ?_)
  let st2 := M.stepEvents (rustDeallocEvents 1568 1) st1
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, _, _, _, _, _, _, _, hfp4, hv4⟩
  have hstep3 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s4
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s5 P5 => VmPreserved s4 s5 ∧
        (s5.sp = fsp ∧ s5.readReg64 .fp = s0.sp - 0x60#64 ∧
          s5.readReg64 .lr = runPcPlaced 0x2960 ∧
          calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧ s5.trace = s4.trace ∧ s5.fs = s4.fs ∧
          s5.readReg64 .x0 = d.kpkSigPtr ∧ s5.readReg64 .x1 = 64#64 ∧ s5.readReg64 .x2 = 1#64 ∧
          s5.readReg64 (.gpr 19#5) = g.stores ∧ s5.readReg64 (.gpr 20#5) = g.res ∧
          s5.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P5 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))) := by
    rw [runPcPlaced_eq] at hpc4
    have hfp := hfp4.trans hfp3; have hv := hv4.trans hv3
    have hx19' := hx19_4.trans hx19_3; have hx20' := hx20_4.trans hx20_3
    have hx21' := hx21_4.trans hx21_3
    have hal : s4.spAligned = true := r1c_spAligned hs.spAligned hsp4
    dsimp only [runProgPlaced, lsProg_579]
    rw [show fsp = s4.sp from hsp4.symm]; clear hsp4
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
      r1c_close_post)
  refine r1c_frame_seq_vm
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
      vecU8 A.repAlloc (fsp + 0x208#64) [] ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st2 s4 ∗ tailHold)
    hinv4 (Entails.of_eq (by dsimp only [fsp, st2]; sep_ac_rfl)) hstep3
    fun s5 hvm5 hinv5 hpc5 hrun5 ⟨hsp5, hfp5, hlr5, hv5, htr5, hfs5, hx0_5, hx1_5, hx2_5, hx19_5, hx20_5, hx21_5⟩ => ?_
  rw [← A.pool_transport lim st2 s4 s5 hvm5]
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool lim st2 s5 ∗
      ((((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)) ∗
        (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)) ∗
        (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)) ∗
        vecU8 A.repAlloc (fsp + 0x208#64) [] ∗ tailHold))
    (Entails.of_eq (by sep_ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv5 hpc5 hrun5 hsp5 hlr5
      hx0_5 (by rw [hx1_5]; rfl) hx2_5 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      fun s6 hinv6 hpc6 hrun6 hsp6 hcs6 hfs6 htr6 => ?_)
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, _, _, _, _, _, _, _, hfp6, hv6⟩
  have hs6 : InRunPlaced R1cCodeOk s0 s6 0x2960 :=
    ⟨hpc6, hrun6, hsp6, hfp6.trans hfp5, hinv6, hv6.trans hv5, hs.spAligned⟩
  have htr_all : s6.trace = s.trace :=
    ((((htr6.trans htr5).trans htr4).trans htr3).trans htr2).trans htr1
  have hfs_all : s6.fs = s.fs :=
    ((((hfs6.trans hfs5).trans hfs4).trans hfs3).trans hfs2).trans hfs1
  have henv3 : EnvAt g' []
      (M.stepEvents (r1cFreeNamesEvs d) (M.stepEvents (rustDeallocEvents 64 1) st2)) := by
    dsimp only [st2, st1]
    rw [← M.stepEvents_append, ← M.stepEvents_append, ← M.stepEvents_append]
    simpa [r1cOkTailEvs, List.append_assoc] using henv
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_ok_free_me (d := d) hh hext_le hsub64 hs6
      (hx19_6.trans hx19_5) (hx20_6.trans hx20_5) (hx21_6.trans hx21_5)
      (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist)
      hans hwr henv3 hjoin)
  exact Entails.of_eq (by dsimp only [tailHold, dirG, fsp, st2]; rw [← hlow_eq]; sep_ac_rfl)

/-! ## 4. Error Tail (`R+0x2a20 → R+0x2c54 → R+0x2c68 → R+0x2c7c`) -/

theorem r1c_err_free_peer [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r1cFreePeerEvs peerG) st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp
  let mid := memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_errCore A.repAlloc g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢ runLocals fsp [] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, mid]
    rw [r1c_split_at fsp 0 0x2a0 runLocalBytes (by decide) (by decide),
        show (0 : Nat) + 0x2a0 = 0x2a0 from rfl,
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide),
        show (0x2a0 : Nat) + 32 = 0x2c0 from rfl,
        show fsp + BitVec.ofNat 64 0 = fsp by bv_omega]
    exact r1c_rewrite_front (memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by sep_ac_rfl) (by sep_ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch st := by
      simpa [r1cFreePeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced CryptoVerification.SignalSession.Cli.RunCompose.RejectKind.postDispatch.pcOff) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579, CryptoVerification.SignalSession.Cli.RunCompose.RejectKind.pcOff]
      rw [runPcPlaced_eq, hcap, show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hat : AtRejectPlaced R1cCodeOk g g' .postDispatch s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1
        preRegs := by rintro ⟨⟩
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_ (hrej s1 st g' .postDispatch hat henv0)
    rw [rejectMem_atState_postDispatch_eq]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗ core)
      hrejoin_peer (by sep_ac_rfl) (by dsimp only [core, fsp])
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r1cFreePeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced CryptoVerification.SignalSession.Cli.RunCompose.RejectKind.postDispatch.pcOff ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579, CryptoVerification.SignalSession.Cli.RunCompose.RejectKind.pcOff]
      rw [show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hat : AtRejectPlaced R1cCodeOk g g' .postDispatch s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1
        preRegs := by rintro ⟨⟩
        trace := (htr2.trans htr1) ▸ htr
        hist := r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_
      (hrej s2 (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' .postDispatch hat henv1)
    rw [rejectMem_atState_postDispatch_eq]
    exact r1c_rewrite_front
      (stackAt fsp (resStack - runFrame) ∗
        A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) s2 ∗ core)
      hrejoin_peer (by sep_ac_rfl) (by dsimp only [core, fsp])

theorem r1c_err_free_dir [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r1cFreeDirPeerEvs d) st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  let peerPayload := addrNameHeap A.repAlloc d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion fsp 0x2a0 ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  by_cases hcap : d.dirCap = 0#64
  · have henv0 : EnvAt g' .postDispatch (M.stepEvents (r1cFreePeerEvs d.peerG) st) := by
      simpa [r1cFreeDirPeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c68) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = emp) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq]; rw [hcap] at hx24
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := peerPayload ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗
        r1c_errCore A.repAlloc g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc dirG hcap))
        (Entails.of_eq (by dsimp only [peerPayload]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2c68 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 hs1 hx19_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans henv0 hrej)
    exact Entails.of_eq (by dsimp only [peerPayload, fsp]; rw [emp_sepConj]; sep_ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (r1cFreePeerEvs d.peerG)
          (M.stepEvents (rustDeallocEvents d.dirCap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r1cFreeDirPeerEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s emp
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced 0x2c68 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = emp) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        peerPayload ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗
        r1c_errCore A.repAlloc g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [dirG, peerPayload, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; rw [emp_sepConj]; sep_ac_rfl)) hstep
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        (peerPayload ∗ r1c_errCore A.repAlloc g g' s0))
      (Entails.of_eq (by rw [emp_sepConj]; sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hs2 : InRunPlaced R1cCodeOk s0 s2 0x2c68 :=
      ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 hs2 (hx19_2.trans hx19_1)
        ((htr2.trans htr1) ▸ htr)
        (r1c_hist_of_eq (htr2.trans htr1) (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        hans henv1 hrej)
    exact Entails.of_eq (by dsimp only [peerPayload, fsp]; sep_ac_rfl)

theorem r1c_err_free_me [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2a20)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : EnvAt g' .postDispatch (M.stepEvents (r1cFreeNamesEvs d) st))
    (hrej : RejectKPlacedEnv R1cCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0)
      Q Qp oom := by
  intro fsp dirG
  have hlow2a0 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
      memRegion fsp 0x2a0 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x2a0 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  let tailRest := addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
    memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
    stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0
  have hlow_dir : (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      r1c_lowNoDir fsp d = r1c_lowCells fsp d := by
    dsimp only [r1c_lowCells, r1c_lowNoDir]; sep_ac_rfl
  by_cases hcap : d.meG.name.cap = 0#64
  · have henv0 : EnvAt g' .postDispatch (M.stepEvents (r1cFreeDirPeerEvs d) st) := by
      simpa [r1cFreeNamesEvs, r1cFreeCapEvs, hcap] using henv
    have hstep : SepWP (runProgPlaced H) (runPcPlaced 0x2c54) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 (.gpr 19#5) = g.stores ∧
            s1.readReg64 (.gpr 22#5) = d.dirPtr ∧ s1.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, show fsp = s.sp from hsp.symm]; rw [hcap] at hx21; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := r1c_lowNoDir fsp d ∗ tailRest)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A.repAlloc d.meG hcap))
        (Entails.of_eq (by dsimp only [tailRest]; rw [emp_sepConj, ← hlow_dir]; sep_ac_rfl)))
      hstep fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx22_1, hx24_1⟩ => ?_
    dsimp only [tailRest]
    rw [← A.pool_transport lim st s s1 hvm1]
    have hs1 : InRunPlaced R1cCodeOk s0 s1 0x2c54 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 hs1 hx19_1 hx22_1 hx24_1
        (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist) hans henv0 hrej)
    exact r1c_rewrite_front
      (addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗ r1c_errCore A.repAlloc g g' s0)
      hlow2a0 (by rw [← hlow_dir]; sep_ac_rfl) (by dsimp only [dirG, fsp]; sep_ac_rfl)
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have henv1 : EnvAt g' .postDispatch
        (M.stepEvents (r1cFreeDirPeerEvs d)
          (M.stepEvents (rustDeallocEvents d.meG.name.cap.toNat 1) st)) := by
      rw [← M.stepEvents_append]
      simpa [r1cFreeNamesEvs, r1cFreeCapEvs, hcap] using henv
    have hlow_me : ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowNoMePtr fsp d =
        r1c_lowCells fsp d := by
      dsimp only [r1c_lowCells, r1c_lowNoMePtr]; sep_ac_rfl
    have hstep1 : SepWP (runProgPlaced H) (lsρ lsRustDeallocSymCli) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => VmPreserved s s1 ∧
          (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
            s1.readReg64 .lr = runPcPlaced 0x2a34 ∧
            calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
            s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
            s1.readReg64 .x2 = 1#64 ∧ s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)) := by
      have hpc := hs.pc; rw [runPcPlaced_eq] at hpc
      have hrun := hs.run; have hsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := hs.spAligned_cur
      dsimp only [runProgPlaced, lsProg_579]
      rw [show fsp = s.sp from hsp.symm]; clear hsp
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, rfl⟩
        r1c_close_post)
    apply r1c_sepWPp_weaken_pre
      (sepConj_mono_left (r1c_nameHeap_dealloc A.repAlloc d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq_vm
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        r1c_lowNoMePtr fsp d ∗ tailRest)
      hs.inv (Entails.of_eq (by dsimp only [tailRest, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; rw [← hlow_me]; sep_ac_rfl)) hstep1
      fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    dsimp only [tailRest]
    rw [← A.pool_transport lim st s s1 hvm1]
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s1 ∗
        ((((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          r1c_lowNoDir fsp d ∗
          addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗
          memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗ r1c_errCore A.repAlloc g g' s0))
      (Entails.of_eq (by dsimp only [r1c_lowNoMePtr, r1c_lowNoDir]; sep_ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    let st1 := M.stepEvents (rustDeallocEvents d.meG.name.cap.toNat 1) st
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hstep2 : SepWP (runProgPlaced H) (runPcPlaced 0x2c54) s2
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s3 P3 => VmPreserved s2 s3 ∧
          (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
            calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
            s3.readReg64 (.gpr 19#5) = g.stores ∧
            s3.readReg64 (.gpr 22#5) = d.dirPtr ∧ s3.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P3 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))) := by
      rw [runPcPlaced_eq] at hpc2
      have hfp := hfp2.trans hfp1; have hv := hv2.trans hv1
      have hx19' := hx19_2.trans hx19_1
      have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
      dsimp only [runProgPlaced, lsProg_579]
      rw [runPcPlaced_eq, show fsp = s2.sp from hsp2.symm]; clear hsp2
      by_vm_steps (
        wp_steps
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        refine ⟨by simp only [wp_norm, arm64_norm], ?_, by sep_ac_rfl⟩
        r1c_close_post)
    refine r1c_frame_seq_vm
      (F := r1c_lowNoDir fsp d ∗
        addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s2 ∗ r1c_errCore A.repAlloc g g' s0)
      hinv2 (Entails.of_eq (by dsimp only [fsp, st1]; sep_ac_rfl)) hstep2
      fun s3 hvm3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hv3, htr3, hfs3, hx19_3, hx22_3, hx24_3⟩ => ?_
    rw [← A.pool_transport lim st1 s2 s3 hvm3]
    have hs3 : InRunPlaced R1cCodeOk s0 s3 0x2c54 :=
      ⟨hpc3, hrun3, hsp3, hfp3, hinv3, hv3, hs.spAligned⟩
    have htr_all : s3.trace = s.trace := (htr3.trans htr2).trans htr1
    have hfs_all : s3.fs = s.fs := (hfs3.trans hfs2).trans hfs1
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 hs3 hx19_3 hx22_3 hx24_3
        (htr_all ▸ htr) (r1c_hist_of_eq htr_all (congrArg FsState.files hfs_all) hhist)
        hans henv1 hrej)
    exact r1c_rewrite_front
      (addrNameHeap A.repAlloc dirG ∗ addrNameHeap A.repAlloc d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st1 s3 ∗ r1c_errCore A.repAlloc g g' s0)
      hlow2a0 (by rw [← hlow_dir]; sep_ac_rfl) (by dsimp only [dirG, fsp, st1]; sep_ac_rfl)

/-! ## 5. Envelope-Erased Convenience Wrappers (`JoinKPlaced` / `RejectKPlaced`) -/

theorem r1c_ok_tail_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2908)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R1cCodeOk H A lim g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_okCore A.repAlloc g g' s0)
      Q Qp oom :=
  r1c_ok_tail (EnvAt := fun _ _ _ => True) hh hext_le hsub64 hs hx19 hx20 hx21
    htr hhist hans hwr trivial fun s' st' g'' out' hat _ => hjoin s' st' g'' out' hat

theorem r1c_err_free_me_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R1cCodeOk s0 s 0x2a20)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectKPlaced R1cCodeOk H A lim g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (addrNameHeap A.repAlloc d.meG ∗ addrNameHeap A.repAlloc dirG ∗
        addrNameHeap A.repAlloc d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ r1c_errCore A.repAlloc g g' s0)
      Q Qp oom :=
  r1c_err_free_me (EnvAt := fun _ _ _ => True) hh hext_le hsub64 hs hx19 hx21
    htr hhist hans trivial fun s' st' g'' rk' hat _ => hrej s' st' g'' rk' hat

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cStepsPlacedBudget
