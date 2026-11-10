/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded `signal_session::run` Arm `R3b`: `decrypt_prekey` Tail Step Lemmas

Proves the second half of the `PreKeySignalMessage::try_from` `Ok` stack shuffle
(`r3b_recvP_shuf2_placed`), the `decrypt_prekey` `Err` tail (`r3b_recvP_dec_err_placed`), and the
`decrypt_prekey` `Ok` continuation (`r3b_recvP_from_de0_placed`) — plus `_any` and `_codeOk`
variants — on Block `579` (`runProgPlaced H`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (LayoutOk vecU8)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliWrOk inputOf namedWrites runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtJoinPlaced Bytes InRunPlaced R3bCodeOk RejectKind RunHistOk addrNameHeap decResAt joinMem
   r3b_W30 r3b_W5 r3b_W6 r3b_addr_unpack r3b_calleeSavedVRegs_q0 r3b_calleeSavedVRegs_q1
   r3b_calleeSavedVRegs_q2 r3b_calleeSavedVRegs_setMem r3b_calleeSavedVRegs_setPC
   r3b_calleeSavedVRegs_setPState r3b_calleeSavedVRegs_writeReg64 r3b_collapse30_flat
   r3b_extractLsb_append_hi r3b_extractLsb_append_lo r3b_files_of_trace_eq r3b_fs_setMem
   r3b_fs_setPC r3b_fs_setPState r3b_fs_writeReg64 r3b_fs_writeVReg128 r3b_hist_of_eq
   r3b_inRun_step r3b_mem48_to_slot6 r3b_mem_setPState r3b_nameHeap_dealloc r3b_nameHeap_zero
   r3b_perm r3b_perm_post r3b_pt64_eq r3b_pure5 r3b_readReg64_setPState r3b_sepWPp_exists_left
   r3b_sepWPp_pure_left r3b_sepWPp_weaken_pre r3b_shufMid r3b_slot30 r3b_slot5 r3b_slot6
   r3b_slot6_to_mem48 r3b_sp_setPState r3b_split_at r3b_stOf r3b_stackAt_split_ge
   r3b_status_setPState r3b_symtab_setPState r3b_trace_setPState r3b_with_speOwned_words6
   r3b_words4_entails_mem32 runFsp runLocalBytes runLocals runLocalsFrom runPcPlaced
   runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runFrame)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget
  (r3bFreeCapEvs r3bFreeMePeerEvs r3b_reject_from_fec_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget
  (r3b_call_lscro r3b_dealloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux
  (r3b_sepWP_with_vm_oom r3b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlaced JoinKPlacedEnv RejectKPlaced RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget (dropSpeOwnedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudgetAux
  (r3b_sepWP_with_vm_oom r3b_seq_lscro_oom r3b_recvP_parse_err_placed
   r3b_recvP_parse_err_placed_any r3b_recvP_shuf1_placed)

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

private theorem sepWP_any_oom {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog tgt s Pre post) :
    SepWP prog tgt s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs, ⟨hpc, hrun, Pm, hm', hp⟩ | ⟨_, hfalse⟩⟩ := SepWP.to_reaches_pc h hm hL
  · exact ⟨sm, hs, Or.inl ⟨hpc, hrun, Pm, hm', hp⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private theorem r3b_cut_vm {P : Program} {b mid tgt : BitVec 64}
    {Hk : String → Option (State → State)} {s0 s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hvm0 : VmPreserved s0 s)
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (sm.pc = mid → sm.status = .Running → VmPreserved s0 sm →
          SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs1, ⟨hpc1, hrun1, Pm, hm1, hvm1, hk⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved (Hk := Hk) hseg) hm hL
  · obtain ⟨sf, hs2, hout2⟩ :=
      SepWP.to_reaches_pc (hk hpc1 hrun1 (hvm0.trans hvm1)) hm1 (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem vmPreserved_adrp_step {s0 sm : State} {r : Reg} {v pc' : BitVec 64}
    (h : VmPreserved s0 sm) :
    VmPreserved s0 ((sm.writeReg64 r v).setPC pc') :=
  h.trans (by simp [LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPC,
    LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_writeReg64])

scoped syntax "r3b_vm_cut " term:max " , " term:max " => " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| r3b_vm_cut $mid:term , $hvm:term => $rest:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| (apply r3b_cut_vm (mid := $mid) $hvm; try rw [runPcPlaced_eq])))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($rest)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "r3b_vm_cut: inner tactic left {rem.length} unsolved goal(s)"
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2
      Lean.Elab.Tactic.setGoals savedGoals.tail!

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

/-! ## 1. `PreKeySignalMessage::try_from` `Ok` Shuffle Part 2 (`r3b_recvP_shuf2_placed`) -/

set_option maxHeartbeats 800000 in
/-- Second half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0xaa0 → lsmpl.base 520`,
returning to `R+0xb78`), delivering `VmPreserved s sc` across all `ADRP` `pairStep`s and `STR`/`STP`
stores to the continuation. -/
theorem r3b_recvP_shuf2_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (stores pqCap : BitVec 64) (t0 : r3b_W5) (w z : r3b_W30) (F : SepProp)
    (hs : InRunPlaced R3bCodeOk s0 s 0xaa0)
    (hx8 : s.readReg64 (.gpr 8#5) = w.b0.w0)
    (hx9 : s.readReg64 (.gpr 9#5) = pqCap)
    (hx19 : s.readReg64 (.gpr 19#5) = stores)
    (hk : ∀ sc : State,
      VmPreserved s sc →
      R3bCodeOk sc.mem →
      sc.pc = lsmpl.base 520 →
      sc.status = .Running →
      sc.sp = runFsp s0 →
      sc.spAligned = true →
      sc.readReg64 Reg.lr = runPcPlaced 0xb78 →
      sc.readReg64 .x0 = runFsp s0 + 0x4d0#64 →
      sc.readReg64 .x1 = runFsp s0 + 0x220#64 →
      sc.readReg64 .x2 = runFsp s0 + 0x260#64 →
      sc.readReg64 .x3 = stores + 0xf0#64 →
      sc.readReg64 .x4 = lsρ cliSessionVtSym →
      sc.readReg64 .x5 = stores →
      sc.readReg64 .x6 = lsρ cliIdentityVtSym →
      sc.readReg64 .x7 = stores + 0xc8#64 →
      sc.readReg64 .x8 = runFsp s0 + 0x320#64 →
      sc.readReg64 (.gpr 19#5) = stores →
      sc.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sc.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sc.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sc.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sc.readReg64 .fp = s.readReg64 .fp →
      calleeSavedVRegs sc = calleeSavedVRegs s →
      sc.trace = s.trace →
      sc.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sc
        ((runFsp s0 ↦₆₄ lsρ cliPreKeyVtSym) ∗
          ((runFsp s0 + 8#64) ↦₆₄ (stores + 0x50#64)) ∗
          ((runFsp s0 + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((runFsp s0 + 24#64) ↦₆₄ (stores + 0x78#64)) ∗
          ((runFsp s0 + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          memRegion (runFsp s0 + 0x3e0#64) 240 ∗
          ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r3b_slot5 (runFsp s0) t0 ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
        ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0xaa0 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp ⊢
  apply r3b_seq_lscro_oom (mid := lsmpl.base 520) hs.inv
  dsimp only [r3b_slot30, r3b_slot5, r3b_shufMid]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_any_oom
  r3b_vm_cut (runPcPlaced 0xaa8) , (VmPreserved.refl s) =>
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun _hpc1 hrun1 hvm1 => ?_⟩
    wp_step
    r3b_vm_cut (runPcPlaced 0xac0) , (vmPreserved_adrp_step hvm1) =>
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun _hpc2 _hrun2 hvm2 => ?_⟩
      wp_step
      r3b_vm_cut (runPcPlaced 0xad8) , (vmPreserved_adrp_step hvm2) =>
        wp_steps
        refine SepWP.done
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], fun _hpc3 _hrun3 hvm3 => ?_⟩
        wp_step
        r3b_vm_cut (runPcPlaced 0xaf4) , (vmPreserved_adrp_step hvm3) =>
          wp_steps
          refine SepWP.done
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hrun])
            ⟨by simp only [wp_norm, arm64_norm], fun _hpc4 _hrun4 hvm4 => ?_⟩
          wp_step
          r3b_vm_cut (runPcPlaced 0xb48) , (vmPreserved_adrp_step hvm4) =>
            wp_steps
            refine SepWP.done
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm, hrun])
              ⟨by simp only [wp_norm, arm64_norm], fun _hpc5 _hrun5 hvm5 => ?_⟩
            wp_step
            r3b_vm_cut (lsmpl.base 520) , (vmPreserved_adrp_step hvm5) =>
              wp_steps
              refine SepWP.done
                (by simp only [wp_norm, arm64_norm])
                (by simp only [wp_norm, arm64_norm, hrun])
                ⟨by simp only [wp_norm, arm64_norm], fun hpc6 hrun6 hvm =>
                  SepWP.done hpc6 hrun6 (fun hinv_c => ?_)⟩
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              subst hfsp
              let fsp := runFsp s0
              refine r3b_sepWPp_weaken_pre ?_
                (hk (r3b_stOf hinv_c) hvm hinv_c
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
                  (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]))
              try rw [hsp]
              dsimp only [fsp, r3b_slot30, r3b_slot5]
              simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
              refine sepConj_mono (r3b_pt64_eq rfl rfl)
                (sepConj_mono (r3b_pt64_eq rfl rfl)
                  (sepConj_mono (r3b_pt64_eq rfl rfl)
                    (sepConj_mono (r3b_pt64_eq rfl rfl)
                      (sepConj_mono (r3b_pt64_eq rfl rfl)
                        (r3b_collapse30_flat
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (Entails.refl _))))))

/-! ## 2. `decrypt_prekey` `Err` Tail (`r3b_recvP_dec_err_placed`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded `decrypt_prekey` `Err` tail from `R+0xd94`
(`R+0xd94 → R+0xfc4 → (blkPl_553).base → R+0xfec → R+0x2c7c`). -/
theorem r3b_recvP_dec_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (err : ApiError AddrVal Unit) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_drop, FreeOnlyEvs evs_drop →
      EnvAt g' .postDispatch
        (M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h350 : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) := by
    rw [r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A.repAlloc (fsp + 0x320#64) (.error err) ∗ memRegion (fsp + 0x4d0#64) 48 ⊢
        ∃∗ k : SpeOwned, ∃∗ d0 : r3b_W6,
          speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗
          r3b_slot6 (fsp + 0x4d0#64) d0 := by
    dsimp only [decResAt]
    refine Entails.trans (sepConj_mono_right (r3b_mem48_to_slot6 (fsp + 0x4d0#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro k
    exact Entails.sepExists_right k (Entails.sepExists_right d0 (Entails.refl _))
  rw [h350]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
          protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro d0
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (A := A.repAlloc) (src := fsp + 0x320#64)
    (dst := fsp + 0x4d0#64) (k := k) (fun sw hu3 hu2 => ?_)
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true := bne_iff_ne.mpr hu2
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x320#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        (r3b_slot6 (fsp + 0x4d0#64) d0 ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
            runSaved s0 ∗
            memRegion fsp 0x220 ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))) ⊢
      (r3b_slot6 (fsp + 0x320#64) sw ∗
        r3b_slot6 (fsp + 0x4d0#64) d0 ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k)) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        memRegion (fsp + 0x280#64) 0xa0 ∗
        memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) from Entails.of_eq (by ac_rfl))
  apply r3b_seq_lscro_oom (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6]
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
      (F := memRegion (fsp + 0x320#64) 48 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        memRegion (fsp + 0x280#64) 0xa0 ∗
        memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
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
            (sepConj_mono (r3b_slot6_to_mem48 (fsp + 0x320#64) sw)
              (Entails.refl (A.pool lim st (r3b_stOf hinv_c) ∗ stackAt fsp (resStack - runFrame) ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                runSaved s0 ∗
                memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                memRegion (fsp + 0x280#64) 0xa0 ∗
                memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
                memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap))))
          (by dsimp only [r3b_stOf]; sep_ac_rfl))
        (by
          dsimp only [r3b_slot6, r3b_stOf]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
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
      have hunp :
          protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ⊢
            ∃∗ hiP : BitVec 64,
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
              memRegion (fsp + 0x260#64) 32 ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG := by
        refine Entails.trans
          (sepConj_mono
            (r3b_addr_unpack A.repAlloc peerG (fsp + 0x220#64) (fsp + 0x228#64)
              (fsp + 0x230#64) (fsp + 0x238#64) (by bv_omega) (by bv_omega) (by bv_omega))
            (r3b_addr_unpack A.repAlloc meG (fsp + 0x260#64) (fsp + 0x268#64)
              (fsp + 0x270#64) (fsp + 0x278#64) (by bv_omega) (by bv_omega) (by bv_omega))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro hiM
        apply Entails.sepExists_elim; intro hiP
        simp only [sepConj_assoc]
        apply Entails.pure_left; intro _
        apply r3b_pure5; intro _
        have hm4 := r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) hiM
        have o1 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
        have o2 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
        have o3 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
        rw [o1, o2, o3] at hm4
        refine Entails.sepExists_right hiP ?_
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hm4
              (Entails.refl ((((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
                addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG)))
            (by ac_rfl))
          (by ac_rfl)
      simp only [r3b_stOf, wp_norm, arm64_norm, hsp]
      apply r3b_sepWPp_weaken_pre
        (r3b_perm
          (sepConj_mono_left
            (Q := memRegion (fsp + 0x4d0#64) 48 ∗ A.pool lim (M.stepEvents evs_drop st) sm ∗
              stackAt fsp (resStack - runFrame) ∗
              memRegion (fsp + 0x320#64) 48 ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              memRegion (fsp + 0x280#64) 0xa0 ∗
              memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
              memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
            hunp)
          (by sep_ac_rfl))
      simp only [sepExists_sepConj_left]
      apply r3b_sepWPp_exists_left; intro hiP
      have hloc_back :
          memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x260#64) 32 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x320#64) 48 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x4d0#64) 48 ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) =
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
        rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
      have henv_drop : EnvAt g' .postDispatch
          (M.stepEvents (r3bFreeMePeerEvs meG peerG) (M.stepEvents evs_drop st)) := by
        rw [← M.stepEvents_append]
        exact henv evs_drop hfree_drop
      refine r3b_sepWPp_weaken_pre ?_
        (r3b_reject_from_fec_placed g' meG peerG
          (BitVec.ofNat 64 peerG.name.bytes.length) hiP hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]))
          (hcsm.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]))
          (hcsm.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]))
          (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot hfs_tot hhist)
          hans
          henv_drop
          hrej)
      subst hfsp
      rw [← hloc_back]
      exact Entails.of_eq (by sep_ac_rfl))

theorem r3b_recvP_dec_err_placed_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (err : ApiError AddrVal Unit) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced R3bCodeOk s0 s 0xd94)
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
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom :=
  r3b_recvP_dec_err_placed (EnvAt := fun _ _ _ => True) g' err peerG meG hh hdrop hstk32
    hext_le hsub64 hs hx19 hx20 hx21 hx26 hx28 htr hhist hans (fun _ _ => trivial)
    (fun s' st' g'' rk hat _ => hrej s' st' g'' rk hat)

/-! ## 3. `decrypt_prekey` `Ok` Tail (`r3b_recvP_from_de0_placed`) -/

private theorem joinMem_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : RunCall) (g' : StoresGhost) (out : Bytes) (s0 : State) (resStack : Nat) :
    joinMem (A.atState lim st s) g g' out s0 resStack =
      memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗
        runLocals (runFsp s0) [(0x208, 24, vecU8 A.repAlloc (runFsp s0 + 0x208#64) out)] ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap := by
  have hlive :
      joinMem (A.atState lim st s) g g' out s0 resStack =
        joinMem { pool := A.pool lim st s, live := A.repAlloc.live } g g' out s0 resStack := rfl
  rw [hlive]
  dsimp only [joinMem]
  change _ =
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
      storesAt { pool := A.pool lim st s, live := A.repAlloc.live } g.stores g' ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      runLocals (runFsp s0)
        [(0x208, 24, vecU8 { pool := A.pool lim st s, live := A.repAlloc.live }
          (runFsp s0 + 0x208#64) out)] ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap
  sep_ac_rfl

set_option maxHeartbeats 800000 in
/-- Budget-threaded continuation from `R+0xde0`
(`R+0xde0 → R+0xf8c` `AtJoinPlaced`, freeing `peerG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_de0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG : AddrGhost)
    {s0 sd : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsd : InRunPlaced R3bCodeOk s0 sd 0xde0)
    (hx19d : sd.readReg64 (.gpr 19#5) = g.stores)
    (hx20d : sd.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: sd.trace)
    (hhist : RunHistOk g.i s0 sd)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st))
    (hjoin : JoinKPlacedEnv R3bCodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sd
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have hjoin_loc :
      memRegion fsp 0x208 ∗
        vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [(0x208, 24, vecU8 A.repAlloc (fsp + 0x208#64) pt)] := by
    have hp32 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16 ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    have h220 :
        memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
          memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) :=
      r3b_split_at fsp 0x220 32 runLocalBytes (by decide) (by decide)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl, h220]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hp32)))
  by_cases hcapP : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' pt st := by
      simpa [r3bFreeCapEvs, hcapP] using henv
    have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    rw [runPcPlaced_eq] at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply r3b_seq_lscro_oom (mid := runPcPlaced 0xf8c) hsd.inv
    rw [runPcPlaced_eq, hcapP, ← hsd.sp]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrund])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st sd (r3b_stOf hinv') hvm]
      have hsj : InRunPlaced R3bCodeOk s0 (r3b_stOf hinv') 0xf8c :=
        r3b_inRun_step hsd (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrund])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have htrj : (r3b_stOf hinv').trace = sd.trace := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hfsj : (r3b_stOf hinv').fs = sd.fs := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hat : AtJoinPlaced R3bCodeOk g g' pt s0 (r3b_stOf hinv') :=
        { base := hsj
          x19 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx19d]
          x20 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx20d]
          trace := htrj ▸ htr
          hist := r3b_hist_of_eq htrj (congrArg FsState.files hfsj) hhist
          ans := hans
          wrOk := hwr }
      refine r3b_sepWPp_weaken_pre ?_ (hjoin (r3b_stOf hinv') st g' pt hat henv0)
      rw [joinMem_atState_eq, hsd.sp, ← hcapP]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc peerG hcapP)
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim st (r3b_stOf hinv') ∗ anyHeap))))
          (by rw [emp_sepConj]; dsimp only [fsp]; sep_ac_rfl))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeqP : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapP
    have henv1 : EnvAt g' pt
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r3bFreeCapEvs, hcapP] using henv
    have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    rw [runPcPlaced_eq] at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hspd : sd.sp = fsp := hsd.sp
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc peerG hcapP))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayP
    apply r3b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hsd.inv
    rw [← hspd]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrund])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st sd (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = sd.sp := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge sd.sp hext_le hsub64
      refine r3b_call_lscro
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ memRegion sd.sp 0x208 ∗ vecU8 A.repAlloc (sd.sp + 0x208#64) pt ∗
          (((sd.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((sd.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (sd.sp + 0x230#64) 16) ∗
          memRegion (sd.sp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (sd.sp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (peerG.name.ptr, peerG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrund])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_ald)
        (retAddr := runPcPlaced 0xf8c)
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
           ⟨hlayP, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0xf8c#64 (by decide) (by decide)⟩
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
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ memRegion sd.sp 0x208 ∗ vecU8 A.repAlloc (sd.sp + 0x208#64) pt ∗
              (((sd.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((sd.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (sd.sp + 0x230#64) 16) ∗
              memRegion (sd.sp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt sd.sp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced R3bCodeOk s0 sm 0xf8c :=
          r3b_inRun_step hsd hpcm hrunm (hspm.trans hsp_c)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = sd.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = sd.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hat : AtJoinPlaced R3bCodeOk g g' pt s0 sm :=
          { base := hs_m
            x19 := hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19d])
            x20 := hcsm.2.1.trans (by simp only [wp_norm, arm64_norm, hx20d])
            trace := htr_tot ▸ htr
            hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
            ans := hans
            wrOk := hwr }
        refine r3b_sepWPp_weaken_pre ?_
          (hjoin sm (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' pt hat henv1)
        rw [joinMem_atState_eq, hspd]
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
                anyHeap)))
            (by dsimp only [fsp]; sep_ac_rfl))
          (by dsimp only [fsp]; sep_ac_rfl))

theorem r3b_recvP_from_de0_placed_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG : AddrGhost)
    {s0 sd : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsd : InRunPlaced R3bCodeOk s0 sd 0xde0)
    (hx19d : sd.readReg64 (.gpr 19#5) = g.stores)
    (hx20d : sd.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: sd.trace)
    (hhist : RunHistOk g.i s0 sd)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinKPlaced R3bCodeOk H A lim g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sd
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap)
      Q Qp oom :=
  r3b_recvP_from_de0_placed (EnvAt := fun _ _ _ => True) g' pt peerG hh hext_le hsub64 hsd hx19d
    hx20d htr hhist hans hwr trivial (fun s' st' g'' out hat _ => hjoin s' st' g'' out hat)


set_option maxHeartbeats 800000 in
/-- Second half of `PreKeySignalMessage::try_from` `Ok` shuffle (`R+0xaa0 → lsmpl.base 520`,
returning to `R+0xb78`), delivering `VmPreserved s sc` across all `ADRP` `pairStep`s and `STR`/`STP`
stores to the continuation. -/
theorem r3b_recvP_shuf2_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {H : LibsignalHooks}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (stores pqCap : BitVec 64) (t0 : r3b_W5) (w z : r3b_W30) (F : SepProp)
    (hs : InRunPlaced CodeOk s0 s 0xaa0)
    (hx8 : s.readReg64 (.gpr 8#5) = w.b0.w0)
    (hx9 : s.readReg64 (.gpr 9#5) = pqCap)
    (hx19 : s.readReg64 (.gpr 19#5) = stores)
    (hk : ∀ sc : State,
      VmPreserved s sc →
      CodeOk sc.mem →
      sc.pc = lsmpl.base 520 →
      sc.status = .Running →
      sc.sp = runFsp s0 →
      sc.spAligned = true →
      sc.readReg64 Reg.lr = runPcPlaced 0xb78 →
      sc.readReg64 .x0 = runFsp s0 + 0x4d0#64 →
      sc.readReg64 .x1 = runFsp s0 + 0x220#64 →
      sc.readReg64 .x2 = runFsp s0 + 0x260#64 →
      sc.readReg64 .x3 = stores + 0xf0#64 →
      sc.readReg64 .x4 = lsρ cliSessionVtSym →
      sc.readReg64 .x5 = stores →
      sc.readReg64 .x6 = lsρ cliIdentityVtSym →
      sc.readReg64 .x7 = stores + 0xc8#64 →
      sc.readReg64 .x8 = runFsp s0 + 0x320#64 →
      sc.readReg64 (.gpr 19#5) = stores →
      sc.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sc.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sc.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) →
      sc.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sc.readReg64 .fp = s.readReg64 .fp →
      calleeSavedVRegs sc = calleeSavedVRegs s →
      sc.trace = s.trace →
      sc.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sc
        ((runFsp s0 ↦₆₄ lsρ cliPreKeyVtSym) ∗
          ((runFsp s0 + 8#64) ↦₆₄ (stores + 0x50#64)) ∗
          ((runFsp s0 + 16#64) ↦₆₄ lsρ cliSignedPreKeyVtSym) ∗
          ((runFsp s0 + 24#64) ↦₆₄ (stores + 0x78#64)) ∗
          ((runFsp s0 + 32#64) ↦₆₄ lsρ cliKyberPreKeyVtSym) ∗
          memRegion (runFsp s0 + 0x3e0#64) 240 ∗
          ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
          r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
        Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r3b_slot5 (runFsp s0) t0 ∗
        r3b_slot30 (runFsp s0 + 0x3e0#64) (r3b_shufMid w z) ∗
        ((runFsp s0 + 0x4d0#64) ↦₆₄ pqCap) ∗
        r3b_slot30 (runFsp s0 + 0x4d8#64) w ∗ F)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0xaa0 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp ⊢
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := lsmpl.base 520) hs.inv
  dsimp only [r3b_slot30, r3b_slot5, r3b_shufMid]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_any_oom
  r3b_vm_cut (runPcPlaced 0xaa8) , (VmPreserved.refl s) =>
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], fun _hpc1 hrun1 hvm1 => ?_⟩
    wp_step
    r3b_vm_cut (runPcPlaced 0xac0) , (vmPreserved_adrp_step hvm1) =>
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], fun _hpc2 _hrun2 hvm2 => ?_⟩
      wp_step
      r3b_vm_cut (runPcPlaced 0xad8) , (vmPreserved_adrp_step hvm2) =>
        wp_steps
        refine SepWP.done
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], fun _hpc3 _hrun3 hvm3 => ?_⟩
        wp_step
        r3b_vm_cut (runPcPlaced 0xaf4) , (vmPreserved_adrp_step hvm3) =>
          wp_steps
          refine SepWP.done
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hrun])
            ⟨by simp only [wp_norm, arm64_norm], fun _hpc4 _hrun4 hvm4 => ?_⟩
          wp_step
          r3b_vm_cut (runPcPlaced 0xb48) , (vmPreserved_adrp_step hvm4) =>
            wp_steps
            refine SepWP.done
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm, hrun])
              ⟨by simp only [wp_norm, arm64_norm], fun _hpc5 _hrun5 hvm5 => ?_⟩
            wp_step
            r3b_vm_cut (lsmpl.base 520) , (vmPreserved_adrp_step hvm5) =>
              wp_steps
              refine SepWP.done
                (by simp only [wp_norm, arm64_norm])
                (by simp only [wp_norm, arm64_norm, hrun])
                ⟨by simp only [wp_norm, arm64_norm], fun hpc6 hrun6 hvm =>
                  SepWP.done hpc6 hrun6 (fun hinv_c => ?_)⟩
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              subst hfsp
              let fsp := runFsp s0
              refine r3b_sepWPp_weaken_pre ?_
                (hk (r3b_stOf hinv_c) hvm hinv_c
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm, hrun])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_al)
                  (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hsp])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]; try rw [hx19])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm])
                  (by simp only [r3b_stOf, wp_norm, arm64_norm]))
              try rw [hsp]
              dsimp only [fsp, r3b_slot30, r3b_slot5]
              simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
              refine sepConj_mono (r3b_pt64_eq rfl rfl)
                (sepConj_mono (r3b_pt64_eq rfl rfl)
                  (sepConj_mono (r3b_pt64_eq rfl rfl)
                    (sepConj_mono (r3b_pt64_eq rfl rfl)
                      (sepConj_mono (r3b_pt64_eq rfl rfl)
                        (r3b_collapse30_flat
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
                          (Entails.refl _))))))

/-! ## 4. `CodeOk`-Parametric `decrypt_prekey` `Err` and `Ok` Tails -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded `decrypt_prekey` `Err` tail from `R+0xd94`
(`R+0xd94 → R+0xfc4 → (blkPl_553).base → R+0xfec → R+0x2c7c`). -/
theorem r3b_recvP_dec_err_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (err : ApiError AddrVal Unit) (peerG meG : AddrGhost)
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 0xd94)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_drop, FreeOnlyEvs evs_drop →
      EnvAt g' .postDispatch
        (M.stepEvents (evs_drop ++ r3bFreeMePeerEvs meG peerG) st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x220 ∗
        memRegion (runFsp s0 + 0x240#64) 0x20 ∗
        memRegion (runFsp s0 + 0x280#64) 0xa0 ∗
        decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
        memRegion (runFsp s0 + 0x350#64) (runLocalBytes - 0x350) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
      Q Qp oom := by
  have hpc : s.pc = runPcPlaced 0xd94 := hs.pc
  rw [runPcPlaced_eq] at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = runFsp s0 := hs.sp
  have hsp_al : s.spAligned = true := hs.spAligned_cur
  generalize hfsp : runFsp s0 = fsp at hsp hx26 ⊢
  have h350 : memRegion (fsp + 0x350#64) (runLocalBytes - 0x350) =
      memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) := by
    rw [r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
        r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
  have hprep :
      decResAt A.repAlloc (fsp + 0x320#64) (.error err) ∗ memRegion (fsp + 0x4d0#64) 48 ⊢
        ∃∗ k : SpeOwned, ∃∗ d0 : r3b_W6,
          speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗
          r3b_slot6 (fsp + 0x4d0#64) d0 := by
    dsimp only [decResAt]
    refine Entails.trans (sepConj_mono_right (r3b_mem48_to_slot6 (fsp + 0x4d0#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro k
    exact Entails.sepExists_right k (Entails.sepExists_right d0 (Entails.refl _))
  rw [h350]
  apply r3b_sepWPp_weaken_pre
    (r3b_perm
      (sepConj_mono_left
        (Q := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
          protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
          runSaved s0 ∗
          memRegion fsp 0x220 ∗
          memRegion (fsp + 0x240#64) 0x20 ∗
          memRegion (fsp + 0x280#64) 0xa0 ∗
          memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
          memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap)
        hprep)
      (by ac_rfl))
  simp only [sepExists_sepConj_left]
  apply r3b_sepWPp_exists_left; intro k
  apply r3b_sepWPp_exists_left; intro d0
  rw [sepConj_assoc]
  refine r3b_with_speOwned_words6 (A := A.repAlloc) (src := fsp + 0x320#64)
    (dst := fsp + 0x4d0#64) (k := k) (fun sw hu3 hu2 => ?_)
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true := bne_iff_ne.mpr hu2
  apply r3b_sepWPp_weaken_pre
    (show (r3b_slot6 (fsp + 0x320#64) sw ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k) ∗
        (r3b_slot6 (fsp + 0x4d0#64) d0 ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
            runSaved s0 ∗
            memRegion fsp 0x220 ∗
            memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap))) ⊢
      (r3b_slot6 (fsp + 0x320#64) sw ∗
        r3b_slot6 (fsp + 0x4d0#64) d0 ∗
        (r3b_slot6 (fsp + 0x4d0#64) sw -∗ speOwnedAt A.repAlloc (fsp + 0x4d0#64) k)) ∗
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        memRegion (fsp + 0x280#64) 0xa0 ∗
        memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ anyHeap) from Entails.of_eq (by ac_rfl))
  apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := (blkPl_553).base) hs.inv
  dsimp only [r3b_slot6]
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
      (F := memRegion (fsp + 0x320#64) 48 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        runSaved s0 ∗
        memRegion fsp 0x220 ∗
        memRegion (fsp + 0x240#64) 0x20 ∗
        memRegion (fsp + 0x280#64) 0xa0 ∗
        memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
        memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
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
            (sepConj_mono (r3b_slot6_to_mem48 (fsp + 0x320#64) sw)
              (Entails.refl (A.pool lim st (r3b_stOf hinv_c) ∗ stackAt fsp (resStack - runFrame) ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
                protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
                runSaved s0 ∗
                memRegion fsp 0x220 ∗
                memRegion (fsp + 0x240#64) 0x20 ∗
                memRegion (fsp + 0x280#64) 0xa0 ∗
                memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
                memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap))))
          (by dsimp only [r3b_stOf]; sep_ac_rfl))
        (by
          dsimp only [r3b_slot6, r3b_stOf]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
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
      have hunp :
          protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ⊢
            ∃∗ hiP : BitVec 64,
              (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
              memRegion (fsp + 0x260#64) 32 ∗
              addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG := by
        refine Entails.trans
          (sepConj_mono
            (r3b_addr_unpack A.repAlloc peerG (fsp + 0x220#64) (fsp + 0x228#64)
              (fsp + 0x230#64) (fsp + 0x238#64) (by bv_omega) (by bv_omega) (by bv_omega))
            (r3b_addr_unpack A.repAlloc meG (fsp + 0x260#64) (fsp + 0x268#64)
              (fsp + 0x270#64) (fsp + 0x278#64) (by bv_omega) (by bv_omega) (by bv_omega))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro hiM
        apply Entails.sepExists_elim; intro hiP
        simp only [sepConj_assoc]
        apply Entails.pure_left; intro _
        apply r3b_pure5; intro _
        have hm4 := r3b_words4_entails_mem32 (fsp + 0x260#64) meG.name.cap meG.name.ptr
          (BitVec.ofNat 64 meG.name.bytes.length) hiM
        have o1 : fsp + 0x260#64 + 8#64 = fsp + 0x268#64 := by bv_omega
        have o2 : fsp + 0x260#64 + 16#64 = fsp + 0x270#64 := by bv_omega
        have o3 : fsp + 0x260#64 + 24#64 = fsp + 0x278#64 := by bv_omega
        rw [o1, o2, o3] at hm4
        refine Entails.sepExists_right hiP ?_
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hm4
              (Entails.refl ((((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                ((fsp + 0x230#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x238#64) ↦₆₄ hiP)) ∗
                addrNameHeap A.repAlloc meG ∗ addrNameHeap A.repAlloc peerG)))
            (by ac_rfl))
          (by ac_rfl)
      simp only [r3b_stOf, wp_norm, arm64_norm, hsp]
      apply r3b_sepWPp_weaken_pre
        (r3b_perm
          (sepConj_mono_left
            (Q := memRegion (fsp + 0x4d0#64) 48 ∗ A.pool lim (M.stepEvents evs_drop st) sm ∗
              stackAt fsp (resStack - runFrame) ∗
              memRegion (fsp + 0x320#64) 48 ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗
              memRegion fsp 0x220 ∗
              memRegion (fsp + 0x240#64) 0x20 ∗
              memRegion (fsp + 0x280#64) 0xa0 ∗
              memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
              memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) ∗ anyHeap)
            hunp)
          (by sep_ac_rfl))
      simp only [sepExists_sepConj_left]
      apply r3b_sepWPp_exists_left; intro hiP
      have hloc_back :
          memRegion (fsp + 0x240#64) 0x20 ∗
            memRegion (fsp + 0x260#64) 32 ∗
            memRegion (fsp + 0x280#64) 0xa0 ∗
            memRegion (fsp + 0x320#64) 48 ∗
            memRegion (fsp + 0x350#64) (0x4d0 - 0x350) ∗
            memRegion (fsp + 0x4d0#64) 48 ∗
            memRegion (fsp + 0x500#64) (runLocalBytes - 0x500) =
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) := by
        rw [r3b_split_at fsp 0x240 0x20 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x260 32 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x280 0xa0 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x320 48 runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x350 (0x4d0 - 0x350) runLocalBytes (by decide) (by decide),
            r3b_split_at fsp 0x4d0 48 runLocalBytes (by decide) (by decide)]
      have henv_drop : EnvAt g' .postDispatch
          (M.stepEvents (r3bFreeMePeerEvs meG peerG) (M.stepEvents evs_drop st)) := by
        rw [← M.stepEvents_append]
        exact henv evs_drop hfree_drop
      refine r3b_sepWPp_weaken_pre ?_
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bBadPlacedBudget.r3b_reject_from_fec_placed_codeOk g' meG peerG
          (BitVec.ofNat 64 peerG.name.bytes.length) hiP hh hext_le hsub64 hs_m
          (hcsm.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx19]))
          (hcsm.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx20]))
          (hcsm.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx21]))
          (hcsm.2.2.2.2.2.2.2.2.2.1.trans (by simp only [r3b_stOf, wp_norm, arm64_norm, hx28]))
          (htr_tot ▸ htr)
          (r3b_hist_of_eq htr_tot hfs_tot hhist)
          hans
          henv_drop
          hrej)
      subst hfsp
      rw [← hloc_back]
      exact Entails.of_eq (by sep_ac_rfl))


set_option maxHeartbeats 800000 in
/-- Budget-threaded continuation from `R+0xde0`
(`R+0xde0 → R+0xf8c` `AtJoinPlaced`, freeing `peerG.name` if `cap ≠ 0`). -/
theorem r3b_recvP_from_de0_placed_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [CryptoVerification.SignalSession.Cli.MainHops.LsCodeInv CodeOk] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall}
    (g' : StoresGhost) (pt : Bytes) (peerG : AddrGhost)
    {s0 sd : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsd : InRunPlaced CodeOk s0 sd 0xde0)
    (hx19d : sd.readReg64 (.gpr 19#5) = g.stores)
    (hx20d : sd.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: sd.trace)
    (hhist : RunHistOk g.i s0 sd)
    (hans : g.a = some (some (namedWrites g'.writes, pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (henv : EnvAt g' pt (M.stepEvents (r3bFreeCapEvs peerG.name.cap) st))
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sd
      (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        addrNameHeap A.repAlloc peerG ∗
        runSaved s0 ∗
        memRegion (runFsp s0) 0x208 ∗
        vecU8 A.repAlloc (runFsp s0 + 0x208#64) pt ∗
        (((runFsp s0 + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((runFsp s0 + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (runFsp s0 + 0x230#64) 16) ∗
        memRegion (runFsp s0 + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap)
      Q Qp oom := by
  let fsp := runFsp s0
  have hjoin_loc :
      memRegion fsp 0x208 ∗
        vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ⊢
      runLocals fsp [(0x208, 24, vecU8 A.repAlloc (fsp + 0x208#64) pt)] := by
    have hp32 :
        ((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16 ⊢
        memRegion (fsp + 0x220#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x220#64) (n := 8) (k := 24)
            (b' := fsp + 0x228#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x228#64) (n := 8) (k := 16)
            (b' := fsp + 0x230#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    have h220 :
        memRegion (fsp + 0x220#64) (runLocalBytes - 0x220) =
          memRegion (fsp + 0x220#64) 32 ∗ memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) :=
      r3b_split_at fsp 0x220 32 runLocalBytes (by decide) (by decide)
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero]
    have hz : fsp + BitVec.ofNat 64 0 = fsp := by bv_omega
    rw [hz, show BitVec.ofNat 64 (0x208 + 24) = 0x220#64 from rfl, h220]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hp32)))
  by_cases hcapP : peerG.name.cap = 0#64
  · have henv0 : EnvAt g' pt st := by
      simpa [r3bFreeCapEvs, hcapP] using henv
    have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    rw [runPcPlaced_eq] at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := runPcPlaced 0xf8c) hsd.inv
    rw [runPcPlaced_eq, hcapP, ← hsd.sp]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hrund])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv' => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st sd (r3b_stOf hinv') hvm]
      have hsj : InRunPlaced CodeOk s0 (r3b_stOf hinv') 0xf8c :=
        r3b_inRun_step hsd (by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm, hrund])
          (by simp only [r3b_stOf, wp_norm, arm64_norm])
          (by simp only [r3b_stOf, wp_norm, arm64_norm]) hinv'
          (by simp only [r3b_stOf, calleeSavedVRegs, wp_norm, arm64_norm])
      have htrj : (r3b_stOf hinv').trace = sd.trace := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hfsj : (r3b_stOf hinv').fs = sd.fs := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hat : AtJoinPlaced CodeOk g g' pt s0 (r3b_stOf hinv') :=
        { base := hsj
          x19 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx19d]
          x20 := by simp only [r3b_stOf, wp_norm, arm64_norm, hx20d]
          trace := htrj ▸ htr
          hist := r3b_hist_of_eq htrj (congrArg FsState.files hfsj) hhist
          ans := hans
          wrOk := hwr }
      refine r3b_sepWPp_weaken_pre ?_ (hjoin (r3b_stOf hinv') st g' pt hat henv0)
      rw [joinMem_atState_eq, hsd.sp, ← hcapP]
      exact r3b_perm
        (r3b_perm_post
          (sepConj_mono (r3b_nameHeap_zero A.repAlloc peerG hcapP)
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim st (r3b_stOf hinv') ∗ anyHeap))))
          (by rw [emp_sepConj]; dsimp only [fsp]; sep_ac_rfl))
        (by dsimp only [fsp]; sep_ac_rfl))
  · have hbeqP : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcapP
    have henv1 : EnvAt g' pt
        (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) := by
      simpa [r3bFreeCapEvs, hcapP] using henv
    have hpcd : sd.pc = runPcPlaced 0xde0 := hsd.pc
    rw [runPcPlaced_eq] at hpcd
    have hrund : sd.status = .Running := hsd.run
    have hspd : sd.sp = fsp := hsd.sp
    have hsp_ald : sd.spAligned = true := hsd.spAligned_cur
    apply r3b_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (r3b_nameHeap_dealloc A.repAlloc peerG hcapP))))))
    rw [show (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        (⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
          A.repAlloc.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
        (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
          ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x230#64) 16) ∗
        memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap) =
      ⌜LayoutOk peerG.name.cap.toNat 1⌝ ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat ∗
          runSaved s0 ∗ memRegion fsp 0x208 ∗ vecU8 A.repAlloc (fsp + 0x208#64) pt ∗
          (((fsp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((fsp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (fsp + 0x230#64) 16) ∗
          memRegion (fsp + 0x240#64) (runLocalBytes - 0x240) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st sd ∗ anyHeap) by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl]
    apply r3b_sepWPp_pure_left; intro hlayP
    apply CryptoVerification.SignalSession.Cli.RunCompose.r3b_seq (mid := lsρ lsRustDeallocSymCli) hsd.inv
    rw [← hspd]
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm, hrund])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm hinv_c => ?_⟩
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← A.pool_transport lim st sd (r3b_stOf hinv_c) hvm]
      have hsp_c : (r3b_stOf hinv_c).sp = sd.sp := by simp only [r3b_stOf, wp_norm, arm64_norm]
      have hstk_split := r3b_stackAt_split_ge sd.sp hext_le hsub64
      refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bHelpersPlacedBudget.r3b_call_lscro_codeOk
        (F := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ memRegion sd.sp 0x208 ∗ vecU8 A.repAlloc (sd.sp + 0x208#64) pt ∗
          (((sd.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
            ((sd.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
            memRegion (sd.sp + 0x230#64) 16) ∗
          memRegion (sd.sp + 0x240#64) (runLocalBytes - 0x240) ∗
          memRegion (sd.sp - BitVec.ofNat 64 (resStack - runFrame))
            (resStack - runFrame - extHookStack) ∗
          anyHeap)
        (peerG.name.ptr, peerG.name.cap.toNat, 1, st)
        (r3b_dealloc_ok hh) hinv_c
        (by simp only [r3b_stOf, wp_norm, arm64_norm])
        (by simp only [r3b_stOf, wp_norm, arm64_norm, hrund])
        (by simpa only [r3b_stOf, State.spAligned, wp_norm, arm64_norm] using hsp_ald)
        (retAddr := runPcPlaced 0xf8c)
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
           ⟨hlayP, by decide⟩,
           by simp only [r3b_stOf, runPcPlaced_eq, wp_norm, arm64_norm]
              exact lsRetAddr624_blockPlacement_base_add 579 0xf8c#64 (by decide) (by decide)⟩
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
            (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              runSaved s0 ∗ memRegion sd.sp 0x208 ∗ vecU8 A.repAlloc (sd.sp + 0x208#64) pt ∗
              (((sd.sp + 0x220#64) ↦₆₄ peerG.name.cap) ∗
                ((sd.sp + 0x228#64) ↦₆₄ peerG.name.ptr) ∗
                memRegion (sd.sp + 0x230#64) 16) ∗
              memRegion (sd.sp + 0x240#64) (runLocalBytes - 0x240) ∗
              stackAt sd.sp (resStack - runFrame) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
              anyHeap))
          (by rw [hstk_split]; dsimp only [r3b_stOf]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        apply r3b_sepWPp_pure_left; rintro ⟨hfs_m, htr_m⟩
        have hs_m : InRunPlaced CodeOk s0 sm 0xf8c :=
          r3b_inRun_step hsd hpcm hrunm (hspm.trans hsp_c)
            (hcsm.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])) hinv_m
            (hcsm.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        have htr_tot : sm.trace = sd.trace :=
          htr_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hfs_tot : sm.fs = sd.fs :=
          hfs_m.trans (by simp only [r3b_stOf, wp_norm, arm64_norm])
        have hat : AtJoinPlaced CodeOk g g' pt s0 sm :=
          { base := hs_m
            x19 := hcsm.1.trans (by simp only [wp_norm, arm64_norm, hx19d])
            x20 := hcsm.2.1.trans (by simp only [wp_norm, arm64_norm, hx20d])
            trace := htr_tot ▸ htr
            hist := r3b_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist
            ans := hans
            wrOk := hwr }
        refine r3b_sepWPp_weaken_pre ?_
          (hjoin sm (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) g' pt hat henv1)
        rw [joinMem_atState_eq, hspd]
        exact r3b_perm
          (r3b_perm_post
            (sepConj_mono hjoin_loc
              (Entails.refl (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents peerG.name.cap.toNat 1) st) sm ∗
                anyHeap)))
            (by dsimp only [fsp]; sep_ac_rfl))
          (by dsimp only [fsp]; sep_ac_rfl))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bStepsPlacedBudget
