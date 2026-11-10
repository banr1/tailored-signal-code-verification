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
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# `FdsGe3Closed`-Threaded `signal_session::run` Arm `R3a` Auxiliary Helpers

`CodeOk`-parametric `withPreFdsGe3Closed` call commutation, frame-rejoin before
`SignalMessage::try_from`, and error/drop/`me = .none` continuations for `R3aProofPlacedBudgetFd`
on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SignalMessageGhost errTag protocolAddressAt
   signalMessageAt signalMessageResultAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW LsCodeInv RunCall callAt cliWrOk coinsInstalledPlaced coinsOf inputOf
   namedWrites ownedBytes runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553 blkPl_554)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtRunEntryPlaced Bytes InRunPlaced PanicK RejectKind
   RunHistOk RunNeeds RunSem SlotAns addrNameHeap addrUpperAt decResAt decResAt_ok
   dispatchCells dispatchMeHeap finish idVtPlaced protocolAddressAt_eq_parts runFiles runFsp
   runPcPlaced runPcPlaced_eq runProgPlaced runSaved sessVtPlaced slotOut withCodeOk)
open CryptoVerification.SignalSession.Cli.RunCompose.R1cPlacedHelpers
  (r1c_W6 r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
   r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setPState
   r1c_calleeSavedVRegs_writeReg64 r1c_extractLsb_append_hi r1c_extractLsb_append_lo
   r1c_fs_setMem r1c_fs_setPC r1c_fs_setPState r1c_fs_writeReg64 r1c_fs_writeVReg128
   r1c_mem48_to_slot6 r1c_mem_setPState r1c_readReg64_setPState r1c_sepWPp_exists_left
   r1c_sepWPp_pure_left r1c_sepWPp_weaken_pre r1c_slot6 r1c_slot6_to_mem48 r1c_spAligned
   r1c_sp_setPState r1c_stackAt_split_ge r1c_status_setPState r1c_symtab_setPState
   r1c_trace_setPState r1c_with_speOwned_words6)
open CryptoVerification.SignalSession.Cli.RunDrop (SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs
  (decResAt_err_owned msgResultAt_err_owned sret120_rejoin)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.Bridge (lsρ)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAux
  (r3a_accept_tail_codeOk r3a_bounds r3a_callRecv_open r3a_call_lscro_codeOk r3a_cs_regs
   r3a_drop_spe_call_codeOk r3a_frameGaps r3a_frame_seq_vm_codeOk r3a_freeOnly_append
   r3a_hiGaps r3a_hist_eq r3a_hist_step r3a_locals_empty_rest r3a_memRegion_words
   r3a_pack_peer r3a_res_split r3a_restFrame r3a_sepWPp_bind r3a_sepWPp_exists_left
   r3a_slotOut_err r3a_slotOut_ok r3a_storesAt_atState r3a_tail_me_reject_codeOk
   r3a_tail_peer_reject_codeOk r3a_words64At r3a_words_to_memRegion)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessageBudget
  (dropSignalMessageSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced dropSignalMessage_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (withPreFdsGe3Closed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

theorem r3a_readVReg128_writeReg64_fd (s : State) (r : Reg) (v : BitVec 64) (i : BitVec 5) :
    (s.writeReg64 r v).readVReg128 i = s.readVReg128 i := by cases s; cases r <;> rfl
theorem r3a_readVReg128_setPC_fd (s : State) (pc : BitVec 64) (i : BitVec 5) :
    (s.setPC pc).readVReg128 i = s.readVReg128 i := by cases s; rfl
theorem r3a_readVReg128_setMem_fd (s : State) (m : Memory) (i : BitVec 5) :
    (s.setMem m).readVReg128 i = s.readVReg128 i := by cases s; rfl
theorem r3a_readVReg128_setPState_fd (s : State) (ps : PState) (i : BitVec 5) :
    (s.setPState ps).readVReg128 i = s.readVReg128 i := by cases s; rfl
theorem r3a_vreg_same_fd (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).readVReg128 i = v := by
  simp [State.readVReg128, State.writeVReg128, VRegFile.read, VRegFile.write]
theorem r3a_vreg_01_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 1#5 v).readVReg128 0#5 = s.readVReg128 0#5 := rfl
theorem r3a_vreg_02_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 2#5 v).readVReg128 0#5 = s.readVReg128 0#5 := rfl
theorem r3a_vreg_10_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 0#5 v).readVReg128 1#5 = s.readVReg128 1#5 := rfl
theorem r3a_vreg_12_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 2#5 v).readVReg128 1#5 = s.readVReg128 1#5 := rfl
theorem r3a_vreg_20_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 0#5 v).readVReg128 2#5 = s.readVReg128 2#5 := rfl
theorem r3a_vreg_21_fd (s : State) (v : BitVec 128) :
    (s.writeVReg128 1#5 v).readVReg128 2#5 = s.readVReg128 2#5 := rfl

theorem r3a_sepWP_seq_vm_fd {prog : Program} {mid tgt : BitVec 64}
    {s : State} {P P' P'' : SepProp} {post1 post2 : State → Prop}
    (h1 : SepWP prog mid s P (fun s1 P1 => VmPreserved s s1 ∧ post1 s1 ∧ (P1 ⊢ P')))
    (h2 : ∀ s1 : State, VmPreserved s s1 → s1.pc = mid → s1.status = .Running → post1 s1 →
      SepWP prog tgt s1 P' (fun s2 P2 => VmPreserved s1 s2 ∧ post2 s2 ∧ (P2 ⊢ P''))) :
    SepWP prog tgt s P (fun s2 P2 => VmPreserved s s2 ∧ post2 s2 ∧ (P2 ⊢ P'')) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hvm1, hp1, hent1⟩ | ⟨_, hf⟩⟩ :=
    SepWP.to_reaches_pc h1 hm hL
  · have hm1' : s1.mem ⊨ P' ∗ R := Satisfies.mono (sepConj_mono_left hent1) hm1
    obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, hvm2, hp2, hent2⟩ | ⟨_, hf⟩⟩ :=
      SepWP.to_reaches_pc (h2 s1 hvm1 hpc1 hrun1 hp1) hm1' (hst1.codeLoaded hL)
    · exact ⟨s2, hst1.trans hst2, Or.inl ⟨hpc2, hrun2, P2, hm2, hvm1.trans hvm2, hp2, hent2⟩⟩
    · exact (not_satisfies_false_sepConj hf).elim
  · exact (not_satisfies_false_sepConj hf).elim

attribute [local simp, local arm64_norm, local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem
  r3a_readVReg128_writeReg64_fd r3a_readVReg128_setPC_fd r3a_readVReg128_setMem_fd
  r3a_readVReg128_setPState_fd
  r3a_vreg_same_fd r3a_vreg_01_fd r3a_vreg_02_fd r3a_vreg_10_fd r3a_vreg_12_fd
  r3a_vreg_20_fd r3a_vreg_21_fd

local macro "r3a_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals ((try simp (config := { zetaDelta := true }) only [runPcPlaced_eq, RejectKind.pcOff, sessVtPlaced, idVtPlaced, cliSessionVtSym, cliIdentityVtSym, lsρ, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, runFsp, wp_norm, arm64_norm, *]); try rfl; try bv_omega)))

/-! ## 1. `withCodeOk` / `withPreFdsGe3Closed` Commutation and Callee Stepper -/

theorem subroutine_ok_withCodeOk_preFds_of_outer {α : Type} {CodeOk : Memory → Prop}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withPreFdsGe3Closed (withCodeOk CodeOk spec))) :
    subroutine_ok prog entry (withCodeOk CodeOk (withPreFdsGe3Closed spec)) :=
  subroutine_ok_mono h
    (fun _ _ _ hpre => by
      simpa only [withPreFdsGe3Closed, withCodeOk, sepConj_assoc] using hpre)
    (fun _ _ _ _ hpost => hpost)

theorem r3a_call_codeOk_fd [LibsignalPlacement]
    {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog callee (withCodeOk CodeOk spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      CodeOk sm.mem →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  have hpre :
      s.mem ⊨ (withCodeOk CodeOk spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withCodeOk]
    refine Satisfies.mono ?_ hm_pre
    exact Entails.trans
      (Entails.pure_right hinv (Entails.refl _))
      (Entails.of_eq (by sep_ac_rfl))
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withCodeOk] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm R hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withCodeOk] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

/-! ## 2. Frame Rejoin Before `SignalMessage::try_from` and Error / Drop / None Continuations -/

set_option maxHeartbeats 1600000 in
theorem r3a_some_pre_try_fd [LibsignalPlacement]
    (A : RustAlloc) (pool : SepProp) (g : RunCall) (peerV : AddrV) (rest : Bytes)
    (s0 : State) (resStack : Nat) (meV : AddrV) (meG : AddrGhost) (w : CallW) (u1 : BitVec 64)
    (hme_bytes : meG.name.bytes = meV.name)
    (hsm : smallRootStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hcall56 : r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ⊢ memRegion g.call 56)
    (hpeer : r3a_words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
      ownedBytes A w.w1 w.w2 w.w3 peerV.name ⊢
      protocolAddressAt A (r3aPeerGhost w peerV) (runFsp s0 + 0x220#64))
    (hme_close : ∀ dst : BitVec 64,
      r3a_words64At dst [BitVec.ofNat 64 meG.name.bytes.length, u1] ⊢ addrUpperAt dst meG)
    (h1d0 : r3a_words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ⊢
      memRegion (runFsp s0) 0x208) :
    (r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
      r3a_words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
      r3a_words64At (runFsp s0 + 0x260#64)
        [meG.name.cap, meG.name.ptr, BitVec.ofNat 64 meV.name.length, u1] ∗
      (g.inp ↦₈ 2#8)) ∗
      (ownedBytes A w.w1 w.w2 w.w3 peerV.name ∗ addrNameHeap A meG ∗
        ((g.inp + 1#64) ↦ₛ rest) ∗
        (memRegion g.res runResSize ∗
          storesAt A g.stores StoresGhost.opened ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff ∗
          runSaved s0 ∗ memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
          memRegion (runFsp s0 + 0x4d0#64) 120 ∗ memRegion (runFsp s0 + 0x23b0#64) 48 ∗
          r3a_hiGaps (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ pool)) ⊢
    ((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ lsLogOff ∗
      stackAt (runFsp s0) smallRootStack ∗ pool ∗
      (memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
        (resStack - runFrame - smallRootStack) ∗
        ((g.inp ↦₈ 2#8) ∗
          protocolAddressAt A meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A (r3aPeerGhost w peerV) (runFsp s0 + 0x220#64) ∗
          storesAt A g.stores StoresGhost.opened ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          r3a_restFrame (runFsp s0))) := by
  have hme_pack :
      r3a_words64At (runFsp s0 + 0x260#64)
        [meG.name.cap, meG.name.ptr, BitVec.ofNat 64 meV.name.length, u1] ∗
        addrNameHeap A meG ⊢
      protocolAddressAt A meG (runFsp s0 + 0x260#64) := by
    rw [← hme_bytes, protocolAddressAt_eq_parts]
    dsimp only [r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    have hup := hme_close (runFsp s0 + 0x270#64)
    dsimp only [r3a_words64At] at hup
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hup
    exact Entails.trans
      (Entails.of_eq (show _ =
        (((runFsp s0 + 0x270#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
          ((runFsp s0 + 0x278#64) ↦₆₄ u1)) ∗
        (((runFsp s0 + 0x260#64) ↦₆₄ meG.name.cap) ∗
          ((runFsp s0 + 0x268#64) ↦₆₄ meG.name.ptr) ∗
          addrNameHeap A meG) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hup) (Entails.of_eq (by sep_ac_rfl)))
  have hsp_sm := r1c_stackAt_split_ge (runFsp s0) hsm hsub64
  rw [hsp_sm]
  dsimp only [r3a_restFrame, r3a_frameGaps]
  exact Entails.trans
    (Entails.of_eq (show _ =
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      (r3a_words64At (runFsp s0 + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗
        ownedBytes A w.w1 w.w2 w.w3 peerV.name) ∗
      (r3a_words64At (runFsp s0 + 0x260#64)
        [meG.name.cap, meG.name.ptr, BitVec.ofNat 64 meV.name.length, u1] ∗
        addrNameHeap A meG) ∗
      (r3a_words64At (runFsp s0 + 0x1d0#64) [BitVec.ofNat 64 meG.name.bytes.length, u1] ∗
        memRegion (runFsp s0) 0x1d0 ∗ memRegion (runFsp s0 + 0x1e0#64) 40) ∗
      (((g.inp + 1#64) ↦ₛ rest) ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗ lsLogOff ∗
        stackAt (runFsp s0) smallRootStack ∗ pool ∗
        memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
          (resStack - runFrame - smallRootStack) ∗
        (g.inp ↦₈ 2#8) ∗
        storesAt A g.stores StoresGhost.opened ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        memRegion g.res runResSize ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
        memRegion (runFsp s0 + 0x23b0#64) 48 ∗ r3a_hiGaps (runFsp s0)) by sep_ac_rfl))
    (Entails.trans
      (sepConj_mono hcall56
        (sepConj_mono hpeer
          (sepConj_mono hme_pack
            (sepConj_mono_left h1d0))))
      (Entails.of_eq (by sep_ac_rfl)))

set_option maxHeartbeats 1600000 in
theorem r3a_after_decrypt_err_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost} {peerG meG : AddrGhost}
    {err : ApiError AddrVal Unit} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3476)
    (herr : err ≠ .store ())
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail → EnvAt g' .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (runFsp s0 + 0x4d0#64) 120 ∗ A.pool lim st s ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗
        (decResAt A.repAlloc (runFsp s0 + 0x320#64) (.error err) ∗
          protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hm120 : memRegion (fsp + 0x4d0#64) 120 =
      memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 72 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (fsp + 0x4d0#64) 48 72 (by decide)
  let errBase : SepProp := memRegion (fsp + 0x500#64) 72 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores g' ∗ memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ r3a_restFrame fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x320#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (by
      dsimp +zetaDelta only at hm120 ⊢; rw [hm120]
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (sepConj_mono (decResAt_err_owned A.repAlloc (runFsp s0 + 0x320#64) err herr)
          (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x4d0#64)))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x4d0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x320#64) k ∗
      (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x4d0#64)
    fun sw H_spe hu3 hu2 hspe_close => ?_
  have hpc : s.pc = runPcPlaced 3476 := hs.pc
  change s.pc = (blkPl_579).base + 3476#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  have hb3 : (sw.w0 + 3#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu3
  have hb2 : (sw.w0 + 2#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hu2
  let P_step : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) dv
  let P_after : SepProp := r1c_slot6 (s.sp + 0x320#64) sw ∗ r1c_slot6 (s.sp + 0x4d0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x320#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x4d0#64) dv ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ errBase) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x320#64) 48 ∗ errBase))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm320 := r1c_slot6_to_mem48 (fsp + 0x320#64) sw
      dsimp +zetaDelta only at hspe_close hm320 ⊢
      exact Entails.trans (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm320
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ errBase))))
          (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)))) ?_
  refine r3a_drop_spe_call_codeOk (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt g' .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  refine r1c_sepWPp_weaken_pre ?_
    (r3a_tail_me_reject_codeOk (g' := g') (peerG := peerG) (meG := meG) hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)
  dsimp +zetaDelta only at hm120 ⊢
  have hrej120 :
      memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame) =
      memRegion (runFsp s0 + 0x4d0#64) 120 ∗ stackAt (runFsp s0) (resStack - runFrame) := by
    rw [← sepConj_assoc, ← hm120]
  exact Entails.trans
    (Entails.of_eq (show _ =
      (memRegion (runFsp s0 + 0x4d0#64) 48 ∗ memRegion (runFsp s0 + 0x500#64) 72 ∗
        stackAt (runFsp s0) (resStack - runFrame)) ∗
      (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
        r3a_restFrame (runFsp s0) ∗ A.pool lim st2 s2 ∗ anyHeap) by sep_ac_rfl))
    (by rw [hrej120]; exact Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 1600000 in
theorem r3a_recvW_try_err_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {peerG meG : AddrGhost} {e : SignalProtocolError}
    {s0 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hext : extHookStack ≤ resStack - runFrame)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 2032)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (henv : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvAt g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (signalMessageResultAt A.repAlloc [] (runFsp s0 + 0x4d0#64) (.error e) ∗
        A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        (protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
          protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
          r3a_restFrame (runFsp s0) ∗ anyHeap))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let tryErrRest : SepProp := memRegion (fsp + 0x508#64) 64 ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
    memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗ r3a_frameGaps fsp ∗ anyHeap
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ k : SpeOwned, speOwnedAt A.repAlloc (fsp + 0x4d8#64) k) ∗
      ((∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (by
      dsimp +zetaDelta only [r3a_restFrame]
      (try simp only [BitVec.add_assoc, BitVec.reduceAdd])
      exact Entails.trans
        (sepConj_mono_left (msgResultAt_err_owned A.repAlloc [] (runFsp s0 + 0x4d0#64) e))
        (Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_left (r1c_mem48_to_slot6 (runFsp s0 + 0x23b0#64))))))
    (r3a_sepWPp_exists_left fun k => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ dv : r1c_W6, r1c_slot6 (fsp + 0x23b0#64) dv) ∗
      (speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
    (r3a_sepWPp_exists_left fun dv => ?_)
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x4d8#64) k ∗
      (r1c_slot6 (fsp + 0x23b0#64) dv ∗
        ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest))
    (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl)) ?_
  refine r1c_with_speOwned_words6 (dst := fsp + 0x23b0#64)
    fun sw H_spe _ _ hspe_close => ?_
  have hpc : s.pc = runPcPlaced 2032 := hs.pc
  change s.pc = (blkPl_579).base + 2032#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  rw [← hs.sp] at hx26
  let P_step : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) dv
  let P_after : SepProp :=
    ((s.sp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (s.sp + 0x4d8#64) sw ∗
      r1c_slot6 (s.sp + 0x23b0#64) sw
  have hstep : SepWP (runProgPlaced H) (blkPl_553).base s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .lr = runPcPlaced 4076 ∧
          s1.readReg64 .x0 = fsp + 0x23b0#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
          s1.readReg64 (.gpr 21#5) = meG.name.cap ∧ s1.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P1 ⊢ P_after)) := by
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r1c_slot6, errTag]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r1c_slot6 (fsp + 0x4d8#64) sw ∗ H_spe ∗
        (r1c_slot6 (fsp + 0x23b0#64) dv ∗
          ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) ⊢
      P_step ∗ (H_spe ∗ A.pool lim st s ∗ stackAt fsp sub ∗ tryErrRest) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1
      ⟨hsp1, hfp1, hv1, htr1, hfs1, hlr1, hx0_1, hx19_1, hx20_1, hx21_1, hx28_1⟩ => ?_
  have hal1 : s1.spAligned = true := r1c_spAligned hs.spAligned hsp1
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre
    (P' := speOwnedAt A.repAlloc (fsp + 0x23b0#64) k ∗ A.pool lim st s1 ∗ stackAt fsp sub ∗
      (memRegion (fsp + 0x4d0#64) 120 ∗
        protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
        protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x320#64) 48 ∗
        memRegion (fsp + 0x380#64) 16 ∗ memRegion (fsp + 0x460#64) 112 ∗
        r3a_frameGaps fsp ∗ anyHeap))
    (by
      dsimp only [P_after]; rw [hs.sp]
      have hm4d0 : ((fsp + 0x4d0#64) ↦₆₄ errTag) ∗ r1c_slot6 (fsp + 0x4d8#64) sw ∗
          memRegion (fsp + 0x508#64) 64 ⊢ memRegion (fsp + 0x4d0#64) 120 := by
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_left (r1c_slot6_to_mem48 (fsp + 0x4d8#64) sw))) ?_
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using sret120_rejoin (fsp + 0x4d0#64) errTag
      dsimp +zetaDelta only at hspe_close hm4d0 ⊢
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans
          (sepConj_mono hspe_close
            (sepConj_mono hm4d0
              (Entails.refl (A.pool lim st s1 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
                protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
                protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
                memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x320#64) 48 ∗
                memRegion (runFsp s0 + 0x380#64) 16 ∗ memRegion (runFsp s0 + 0x460#64) 112 ∗
                r3a_frameGaps (runFsp s0) ∗ anyHeap))))
          (Entails.of_eq (by sep_ac_rfl)))) ?_
  refine r3a_drop_spe_call_codeOk (k := k) hdrop h32 hsub64 hinv1 hpc1 hrun1 hal1 hlr1 hsp1 hfp1 hv1
    hs.spAligned hx0_1 fun s2 evs_drop hfree_drop hsteps2 hin2 hcsm2 htr2 => ?_
  have hcs2 := r3a_cs_regs hcsm2
  have htr2_tot : s0.trace <+: s2.trace := (htr2.trans htr1) ▸ htr
  have hhist2 : RunHistOk g.i s0 s2 :=
    r3a_hist_step hh hsteps2 htr2 (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist)
  let st2 := M.stepEvents evs_drop st
  have henv2 : ∀ evs_rem, FreeOnlyEvs evs_rem →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs_rem st2) := by
    intro evs_rem hf_rem
    rw [← M.stepEvents_append]
    exact henv (evs_drop ++ evs_rem) (r3a_freeOnly_append hfree_drop hf_rem)
  exact r1c_sepWPp_weaken_pre
    (by dsimp +zetaDelta only [r3a_restFrame]; exact Entails.of_eq (by sep_ac_rfl))
    (r3a_tail_me_reject_codeOk (g' := StoresGhost.opened) (peerG := peerG) (meG := meG)
      hh hext hsub64 hin2
      (hcs2.1.trans hx19_1) (hcs2.2.1.trans hx20_1) (hcs2.2.2.1.trans hx21_1)
      (hcs2.2.2.2.2.1.trans hx28_1) htr2_tot hhist2 hans henv2 hrej)

set_option maxHeartbeats 1600000 in
theorem r3a_after_decrypt_drop_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {EnvJoin : StoresGhost → Bytes → M.σ → Prop}
    {H : LibsignalHooks} {g : RunCall} {g' : StoresGhost}
    {peerG meG : AddrGhost} {msgG : SignalMessageGhost} {m : SignalMessage}
    {ans : SlotAns Bytes} {res : Except (ApiError AddrVal Unit) Bytes}
    {s0 s1 s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (h32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRunPlaced CodeOk s0 s 3468)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = runFsp s0 + 0x4d0#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (_htr_s1 : s0.trace <+: s1.trace)
    (hga : g.a = finish ans id)
    (hslot2 : slotOut ans g' res s1 s)
    (htr2_tot : s0.trace <+: s.trace)
    (hhist2 : RunHistOk g.i s0 s)
    (henv_rej : ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvRej g' .postDispatch (M.stepEvents evs_tail st))
    (henv_join : ∀ out, res = .ok out → ∀ evs_tail, FreeOnlyEvs evs_tail →
      EnvJoin g' out (M.stepEvents evs_tail st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvRej g s0 resStack Q Qp)
    (hjoin : JoinKPlacedEnv CodeOk H A lim EnvJoin g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (storesAt A.repAlloc g.stores g' ∗ decResAt A.repAlloc (runFsp s0 + 0x320#64) res ∗
        signalMessageAt A.repAlloc msgG (runFsp s0 + 0x4d0#64) m ∗
        protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x220#64) ∗
        protocolAddressAt A.repAlloc meG (runFsp s0 + 0x260#64) ∗
        (lsLogOff ∗ anyHeap ∗ A.pool lim st s ∗ stackAt (runFsp s0) (resStack - runFrame)) ∗
        (r3a_restFrame (runFsp s0) ∗
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (runFsp s0 + 0x208#64) 24)))
      Q Qp (fun _ => ⌜False⌝) := by
  let fsp := runFsp s0; let sub := resStack - runFrame
  let callKeep : SepProp := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ memRegion (fsp + 0x208#64) 24
  have hpc : s.pc = runPcPlaced 3468 := hs.pc
  change s.pc = (blkPl_579).base + 3468#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hstep : SepWP (runProgPlaced H) (blkPl_554).base s emp
      (fun s3 P3 => VmPreserved s s3 ∧
        (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s.trace ∧ s3.fs = s.fs ∧
          s3.readReg64 .lr = runPcPlaced 3476 ∧
          s3.readReg64 .x0 = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
          s3.readReg64 (.gpr 21#5) = meG.name.cap ∧
          s3.readReg64 (.gpr 26#5) = fsp + 0x4d0#64 ∧
          s3.readReg64 (.gpr 28#5) = meG.name.ptr) ∧
        (P3 ⊢ emp)) := by
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.refl _⟩
      r3a_close_post)
  refine r3a_frame_seq_vm_codeOk hs.inv (Entails.of_eq (by rw [emp_sepConj])) hstep
    fun s3 hvm3 hinv3 hpc3 hrun3
      ⟨hsp3, hfp3, hv3, htr3, hfs3, hlr3, hx0_3, hx19_3, hx20_3, hx21_3, hx26_3, hx28_3⟩ => ?_
  have hal3 : s3.spAligned = true := r1c_spAligned hs.spAligned hsp3
  rw [emp_sepConj, ← A.pool_transport lim st s s3 hvm3]
  have hdsm_ok := dropSignalMessage_placed_ok (callerProg := runProgPlaced H) (i := 579) hh sub h32 hsub64
  let dropKeep : SepProp := storesAt A.repAlloc g.stores g' ∗
    decResAt A.repAlloc (fsp + 0x320#64) res ∗
    protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
    protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
    r3a_restFrame fsp ∗ callKeep ∗ anyHeap
  refine r3a_call_lscro_codeOk (⟨fsp + 0x4d0#64, msgG, m⟩, st) hdsm_ok hinv3 hpc3 hrun3 hal3 hlr3
    (F := dropKeep) ?_
    (hnext := fun s4 hsteps4 hinv4 hpcm4 hrun4 hsp4 hcsm4 => ?_)
  · dsimp only [dropSignalMessageSpec]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (lsLogOff ∗ anyHeap) ∗
          (signalMessageAt A.repAlloc msgG (fsp + 0x4d0#64) m ∗
            A.pool lim st s3 ∗ stackAt fsp sub ∗ storesAt A.repAlloc g.stores g' ∗
            decResAt A.repAlloc (fsp + 0x320#64) res ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x220#64) ∗
            protocolAddressAt A.repAlloc meG (fsp + 0x260#64) ∗
            r3a_restFrame fsp ∗ callKeep) by dsimp +zetaDelta only; sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (entails_anyHeap _)) ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0_3, by rw [hlr3]; simp (config := { decide := true }) only [wp_norm, arm64_norm, runPcPlaced_eq]⟩
      (Entails.of_eq (by rw [hsp3]; dsimp +zetaDelta only; sep_ac_rfl))
  · dsimp only [dropSignalMessageSpec]
    rw [sepExists_sepConj_left]
    refine r1c_sepWPp_exists_left fun evs_dsm => ?_
    simp only [sepConj_assoc]
    refine r1c_sepWPp_pure_left fun ⟨htr4, hfree_dsm⟩ => ?_
    have hcs4 := r3a_cs_regs hcsm4; rw [hsp3]
    have hin4 : InRunPlaced CodeOk s0 s4 3476 :=
      ⟨hpcm4, hrun4, hsp4.trans hsp3, hcs4.2.2.2.2.2.1.trans hfp3, hinv4,
        hcs4.2.2.2.2.2.2.trans hv3, hs.spAligned⟩
    have hx19_4 := hcs4.1.trans hx19_3; have hx20_4 := hcs4.2.1.trans hx20_3
    have hx21_4 := hcs4.2.2.1.trans hx21_3; have hx26_4 := hcs4.2.2.2.1.trans hx26_3
    have hx28_4 := hcs4.2.2.2.2.1.trans hx28_3
    have htr4_tot : s0.trace <+: s4.trace := (htr4.trans htr3) ▸ htr2_tot
    have hhist4 : RunHistOk g.i s0 s4 :=
      r3a_hist_step hh hsteps4 htr4 (r3a_hist_eq htr3 (congrArg FsState.files hfs3) hhist2)
    let st4 := M.stepEvents evs_dsm st
    cases res with
    | ok out =>
      obtain ⟨hans_ok, hwr⟩ := r3a_slotOut_ok hslot2
      have hans4 : g.a = some (some (namedWrites g'.writes, out)) := by
        rw [hga, hans_ok]; rfl
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvJoin g' out (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_join out rfl (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; rw [decResAt_ok]; sep_ac_rfl))
        (r3a_accept_tail_codeOk (g' := g') (peerG := peerG) (meG := meG) (out := out)
          hh hext hsub64 hin4 hx19_4 hx20_4 hx21_4 hx28_4 htr4_tot hhist4 hans4 hwr henv4 hjoin)
    | error err =>
      obtain ⟨herr, hans_err⟩ := r3a_slotOut_err hga hslot2
      have henv4 : ∀ evs_rem, FreeOnlyEvs evs_rem →
          EnvRej g' .postDispatch (M.stepEvents evs_rem st4) := by
        intro evs_rem hf_rem
        rw [← M.stepEvents_append]
        exact henv_rej (evs_dsm ++ evs_rem) (r3a_freeOnly_append hfree_dsm hf_rem)
      exact r1c_sepWPp_weaken_pre
        (Entails.of_eq (by dsimp +zetaDelta only; sep_ac_rfl))
        (r3a_after_decrypt_err_codeOk_fd (g' := g') (peerG := peerG) (meG := meG)
          hh hdrop hext h32 hsub64 hin4 herr hx19_4 hx20_4 hx21_4 hx26_4 hx28_4
          htr4_tot hhist4 hans_err henv4 hrej)

set_option maxHeartbeats 1600000 in
theorem r3a_recvW_none_codeOk_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {sEnvs : RunSlotEnvs}
    {EnvRej : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {rest : Bytes} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (he : AtRunEntryPlaced CodeOk S g s0)
    (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hcall : g.c = .recv peerV)
    (hstdin : g.i.stdin = 2#8 :: rest)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvRej StoresGhost.opened .postDispatch (M.stepEvents evs st))
    (hrej : RejectKPlacedEnv CodeOk H A lim EnvRej g s0 resStack Q Qp) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g .none s0 s resStack)
      Q Qp (fun _ => ⌜False⌝) := by
  obtain ⟨_, _, hsub64, _, _, hext, _⟩ := r3a_bounds hres hres64
  let fsp := runFsp s0; let sub := resStack - runFrame
  have hs : InRunPlaced CodeOk s0 s 532 := hd.base
  have hpc : s.pc = runPcPlaced 532 := hs.pc
  change s.pc = (blkPl_579).base + 532#64 at hpc
  have hrun : s.status = .Running := hs.run
  have hsp : s.sp = fsp := hs.sp; have hfp := hs.fp; have hv := hs.vregs
  have hal : s.spAligned = true := hs.spAligned_cur
  have hx8 : s.readReg64 (.gpr 8#5) = 3#64 := by simpa only [hcall, CallV.tag] using hd.x8
  have hx19 := hd.x19; have hx20 := hd.x20; have hx23 := hd.x23; have hx25 := hd.x25
  have hinp_eq : inputOf g.i g.c = 2#8 :: rest := by rw [hcall]; exact hstdin
  have hinp_merge : (g.inp ↦₈ 2#8) ∗ ((g.inp + 1#64) ↦ₛ rest) = (g.inp ↦ₛ inputOf g.i g.c) := by
    rw [hinp_eq, pointsToBytes_cons]
  have hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 (rest.length + 1) := by
    rw [hd.x24, hinp_eq]; rfl
  have hrest32 : rest.length < 2 ^ 32 := by
    simpa [hstdin] using he.rel.2.1.2.2.1 peerV (hcall ▸ he.parse)
  have hnz24 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  have hans0 : g.a = some none := hd.reject_of_me_none he
  have hx21 : s.readReg64 (.gpr 21#5) = -1#64 := hd.meRegs
  have hhist0 : RunHistOk g.i s0 s := ⟨hd.fs, hd.stdout⟩
  have hres_split := r3a_res_split g.res
  let noneTail : SepProp := memRegion (g.res + 8#64) (runResSize - 8) ∗
    storesAt A.repAlloc g.stores StoresGhost.opened ∗
    ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
    memRegion (fsp + 0x208#64) 24 ∗ memRegion (fsp + 0x260#64) 32 ∗
    memRegion (fsp + 0x320#64) 48 ∗ memRegion (fsp + 0x4d0#64) 120 ∗
    r3a_restFrame fsp ∗ stackAt fsp sub ∗ A.pool lim st s
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w : CallW, ⌜w.w4.setWidth 8 = peerV.device⌝ ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name) ∗
      ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
        memRegion (fsp + 0x220#64) 32 ∗ (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap)) ?_ ?_
  · dsimp +zetaDelta only [dispatchMemPlaced,
      CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced,
      dispatchMeHeap, dispatchCells]
    simp only [RustCliAllocBudget.atState_pool, callAt_atState, r3a_storesAt_atState]
    rw [hinp_eq, pointsToBytes_cons, hcall, hres_split, emp_sepConj,
      r3a_locals_empty_rest (runFsp s0)]
    refine Entails.trans
      (Entails.of_eq (show _ =
        callAt A.repAlloc g.call (.recv peerV) ∗
        (coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗ lsLogOff) ∗
        ((∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (runFsp s0 + 0x220#64) 32 ∗
          (g.inp ↦₈ 2#8) ∗
          (memRegion (g.res + 8#64) (runResSize - 8) ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗
            ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
            memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
            memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
            r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim st s)) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono (r3a_callRecv_open A.repAlloc g.call peerV)
        (sepConj_mono_left (entails_anyHeap _)))
      (Entails.of_eq (by sep_ac_rfl))
  refine r3a_sepWPp_exists_left fun w => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine r1c_sepWPp_pure_left fun hw4 => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗
      (memRegion (fsp + 0x220#64) 32 ∗
        r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
        ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
        (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap))
    (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (r3a_sepWPp_exists_left fun w_res => ?_)
  refine r3a_sepWPp_bind (A0 := memRegion (fsp + 0x220#64) 32)
    (F := (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
      (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ?_ |>
    r1c_sepWPp_weaken_pre (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
  intro R hm
  obtain ⟨ws220, hlen220, hm⟩ := r3a_memRegion_words 4 (fsp + 0x220#64) (by decide) hm
  rcases ws220 with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen220; done)
  refine ⟨r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3], hm, ?_⟩
  let P_step : SepProp :=
    (g.res ↦₆₄ w_res) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [p0, p1, p2, p3] ∗ (g.inp ↦₈ 2#8)
  let P_after : SepProp :=
    (g.res ↦₆₄ 0xffffffffffffffff#64) ∗
      r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
      r3a_words64At (s.sp + 0x220#64) [w.w1, w.w2, w.w3, w.w4] ∗ (g.inp ↦₈ 2#8)
  have hstep : SepWP (runProgPlaced H) (runPcPlaced 4104) s P_step
      (fun s1 P1 => VmPreserved s s1 ∧
        (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
        (P1 ⊢ P_after)) := by
    rw [runPcPlaced_eq]
    dsimp only [runProgPlaced, lsProg_579, P_step, P_after, r3a_words64At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]
    by_vm_steps (
      wp_steps
      apply SepWP.done (by simp only [runPcPlaced_eq, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
      refine ⟨by simp only [wp_norm, arm64_norm], ?_, Entails.of_eq (by sep_ac_rfl)⟩
      r3a_close_post)
  have hP_in :
      r3a_words64At (fsp + 0x220#64) [p0, p1, p2, p3] ∗
        ((g.res ↦₆₄ w_res) ∗
          r3a_words64At g.call [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] ∗
          ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗
          (g.inp ↦₈ 2#8) ∗ noneTail ∗ anyHeap) ⊢
      P_step ∗ (ownedBytes A.repAlloc w.w1 w.w2 w.w3 peerV.name ∗ noneTail ∗ anyHeap) := by
    dsimp +zetaDelta only [P_step]; rw [hs.sp]; exact Entails.of_eq (by sep_ac_rfl)
  refine r3a_frame_seq_vm_codeOk hs.inv hP_in hstep
    fun s1 hvm1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
  dsimp only [noneTail]
  rw [← A.pool_transport lim st s s1 hvm1]
  refine r1c_sepWPp_weaken_pre ?_
    (r3a_tail_peer_reject_codeOk (g' := StoresGhost.opened)
      (peerG := ⟨⟨w.w1, w.w2, peerV.name⟩, peerV.device⟩)
      hh hext hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
      hx19_1 (htr1 ▸ hd.trace) (r3a_hist_eq htr1 (congrArg FsState.files hfs1) hhist0)
      hans0 henv hrej)
  dsimp +zetaDelta only [P_after]; rw [hs.sp]
  have hpeer := r3a_pack_peer A.repAlloc (fsp + 0x220#64) peerV w.w1 w.w2 w.w3 w.w4 hw4
  have hcall56 := r3a_words_to_memRegion [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6] g.call 56
  dsimp +zetaDelta only [runResAt] at hpeer hcall56 ⊢; rw [← hinp_merge]
  exact Entails.trans (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl))
    (Entails.trans
      (sepConj_mono hpeer (sepConj_mono hcall56
        (Entails.refl ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦₈ 2#8) ∗
          ((g.inp + 1#64) ↦ₛ rest) ∗ runSaved s0 ∗
          memRegion (runFsp s0 + 0x208#64) 24 ∗ memRegion (runFsp s0 + 0x260#64) 32 ∗
          memRegion (runFsp s0 + 0x320#64) 48 ∗ memRegion (runFsp s0 + 0x4d0#64) 120 ∗
          r3a_restFrame (runFsp s0) ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim st s1 ∗ anyHeap))))
      (Entails.of_eq (by (try dsimp +zetaDelta only); try sep_ac_rfl)))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudgetAuxFd
