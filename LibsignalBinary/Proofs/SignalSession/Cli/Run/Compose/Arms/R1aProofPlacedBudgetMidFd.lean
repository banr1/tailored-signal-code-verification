/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Post-Read and Post-Decode Sub-Hops for Arm `R1a`

Verifies `r1a_after_decode_fd` (`0x710 → 0x74c`) and `r1a_after_read_fd` (`0x6bc → 0x74c`) on Block
`579`, threading `FdsGe3Closed` across path-buffer deallocation, `IdentityKey::decode`, and buffer
cleanup.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (sepWPp_seq_lscro)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt speWord)
open CryptoVerification.RecordCodecs (decodeIdentityKey)
open CryptoVerification.RecordCodecs.Placed (blkPl_18)
open CryptoVerification.RecordCodecsBinary (identityKeyResultAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallW RunCall cliIo coinsInstalledPlaced coinsOf inputOf ownedBytes runResSize storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (beq_add_one_zero_false_of_lt entails_pure_intro_left ownedBytes_pure vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtRunEntryPlaced Bytes InRunPlaced Init1Data PanicK
   RunHistOk RunSem addrNameHeap addrUpperAt addrUpperAt_entails_memRegion addrValOf
   init1Cells protocolAddressAt_eq_parts r1b_StackBounds runFiles runFsp runLocalBytes runLocals
   runLocalsFrom runOom runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
  (FreeRejK r1a_CodeOk r1a_addrNameHeap_eq_owned r1a_bind_sepWPp_state r1a_call_run
   r1a_decode_err_unified r1a_exists_words32 r1a_false_entails r1a_group2c r1a_group6c
   r1a_group_6bc r1a_group_ok710 r1a_hist_ans_step r1a_ikOk_sem r1a_localsBound r1a_localsCtx
   r1a_localsEnd r1a_locals_drop_head
   r1a_locals_drop_mid r1a_locals_focus r1a_memRegion_zero r1a_ownedBytes_expose
   r1a_ownedBytes_zero r1a_ownedSlack r1a_peerGhostOf r1a_pointsTo32_entails_memRegion
   r1a_pool_setMem_write16 r1a_pool_setMem_write32 r1a_pool_setMem_write32_2
   r1a_pool_setMem_write64 r1a_pool_setMem_write64_2 r1a_pool_setMem_write64_4
   r1a_pool_setMem_write8 r1a_reject_of_decode_err r1a_sepWPp_exists_pre r1a_sepWPp_pure_pre
   r1a_sepWPp_weaken_pre r1a_stackAt_split r1a_words6_to_memRegion48)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
  (identityKeyDecode_keepsFs_vm_placed_ok r1a_free_path_6e0_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
  (r1a_pool_congr_vm r1a_read_err)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
  (r1a_decode_err)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (init1MemPlaced ownedBytes_congr_live storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  r1a_pool_setMem_write8 r1a_pool_setMem_write16 r1a_pool_setMem_write32
  r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
  r1a_pool_setMem_write64_4

/-! ## `IdentityKey::decode` Post-Call Path (`0x710 → 0x74c`) -/

set_option maxHeartbeats 800000 in
theorem r1a_after_decode_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir ikB : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW}
    {ikCap ikPtr : BitVec 64} {s0 s_disp s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp)
    (hcall : g.c = .init peerV dir)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hnext : ∀ (s1 : State) (evs_fi : List AllocEvent) (d1 : Init1Data),
      FreeOnlyEvs evs_fi →
      AtInit1Placed r1a_CodeOk g d1 s0 s1 →
      FdsGe3Closed s1.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs_fi st) g d1 s0 s1 resStack) Q Qp (runOom s0))
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x710)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx25 : s.readReg64 (.gpr 25#5) = ikCap)
    (hx27 : s.readReg64 (.gpr 27#5) = ikPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hik : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB)
    (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hfds : FdsGe3Closed s.fs)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
           (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
           (0x2a0, 32, protocolAddressAt A.repAlloc (r1a_peerGhostOf peerV w) (runFsp s0 + 0x2a0#64)),
           (0x4d0, 48, identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB))] ∗
        ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) Q Qp (runOom s0) := by
  let peerG := r1a_peerGhostOf peerV w
  let cs6 :=
    [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
     (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
     (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64))]
  rcases hdec : decodeIdentityKey ikB with err | idKey
  · have hnotOk : ∀ ik, decodeIdentityKey ikB ≠ .ok ik := by rw [hdec]; intro _ h; nomatch h
    obtain ⟨i, hi, hcmn_ne, hent_spe⟩ := r1a_decode_err_unified A.repAlloc (runFsp s0 + 0x4d0#64) ikB hnotOk
    have hhans : RunHistOk g.i s0 s ∧ g.a = some none :=
      ⟨⟨hfs, hout⟩, r1a_reject_of_decode_err he hd hcall hik (by rw [hdec]; rfl)⟩
    rw [← hdec]
    have hf4d0 := r1a_locals_focus (runFsp s0) cs6 0x4d0 48 (identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB)) []
    (try rw [r1a_memRegion_zero (runFsp s0)])
    change SepWPp _ _ _ (runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB))]) ∗ _) _ _ _
    rw [hf4d0]
    have h40_words : memRegion (runFsp s0 + 0x4d0#64 + 8#64) 40 ⊢
        ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64,
          ((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗
          ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5) := by
      rw [ProofLib.memRegion_split _ 8 32 (by decide), ProofLib.memRegion_split _ 8 24 (by decide),
          ProofLib.memRegion_split _ 8 16 (by decide), ProofLib.memRegion_split _ 8 8 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun d5 => Entails.sepExists_elim fun d4 =>
        Entails.sepExists_elim fun d3 => Entails.sepExists_elim fun d2 => Entails.sepExists_elim fun d1 => ?_
      exact Entails.sepExists_right d1 (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 (Entails.sepExists_right d5 (Entails.refl _)))))
    refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (Entails.trans hent_spe (sepConj_mono_right h40_words)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro d1; apply r1a_sepWPp_exists_pre; intro d2
    apply r1a_sepWPp_exists_pre; intro d3; apply r1a_sepWPp_exists_pre; intro d4; apply r1a_sepWPp_exists_pre; intro d5
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
    change s.pc = (blkPl_579).base + 1808#64 at hpc0
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x8f0) hbase.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      rw [← hsp0]; symm at hsp0
      wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0
      refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hcmn_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]) ⟨by simp only [wp_norm, arm64_norm], fun hvm01 hinv1 => ?_⟩
      apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group6c]
      have hpool_01 : A.pool lim st s = A.pool lim st s1 := (A.pool_of_vmPreserved hvm01).symm
      refine r1a_sepWPp_weaken_pre ?_
        (r1a_decode_err (peerV := peerV) (dir := dir) (ikB := ikB) (meG := meG) (w := w)
          (ikCap := ikCap) (ikPtr := ikPtr)
          (F_heap := coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff)
          hh hdrop hbnd hpanic hrej hi
          ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hcmn_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0],
           by simp only [arm64_norm, s1, hbase.fp], hinv1,
           by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs],
           hbase.spAligned⟩
          (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1, hx19])
          (by simp only [arm64_norm, s1, hx20]) (by simp only [arm64_norm, s1, hx21])
          (by simp only [arm64_norm, s1, hx25]) (by simp only [arm64_norm, s1, hx27])
          (by simpa only [arm64_norm, s1] using htr)
          (r1a_hist_ans_step hhans (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])))
      have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord i) ∗
          (((runFsp s0 + 0x4d8#64) ↦₆₄ d1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ d2) ∗
            ((runFsp s0 + 0x4e8#64) ↦₆₄ d3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ d4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ d5)) ⊢
          memRegion (runFsp s0 + 0x4d0#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1a_words6_to_memRegion48 (runFsp s0 + 0x4d0#64) (speWord i) d1 d2 d3 d4 d5
      have hcs_ent : runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ⊢
          runLocals (runFsp s0)
            [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
             (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4),
             (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
             (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
             (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
             (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)] ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name := by
        let csPre3 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
          (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5)]
        let csSuf2 := [(0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)),
          (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
        dsimp only [cs6, csPre3, csSuf2] at *
        refine Entails.trans (r1a_locals_drop_head (runFsp s0) 0x1b0 4 _
          (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf2)
          (r1a_pointsTo32_entails_memRegion _ _)) ?_
        refine Entails.trans (r1a_locals_drop_mid (runFsp s0) csPre3 0x260 16 _ csSuf2
          (addrUpperAt_entails_memRegion _ _)) ?_
        rw [r1a_locals_focus (runFsp s0) csPre3 0x2a0 32 (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64))
            [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)],
            protocolAddressAt_eq_parts A.repAlloc peerG (runFsp s0 + 0x2a0#64),
            r1a_addrNameHeap_eq_owned peerG]
        dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
        have hup16 : addrUpperAt (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w) ⊢
            memRegion (runFsp s0 + 0x2b0#64) 16 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            addrUpperAt_entails_memRegion (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w)
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup16)))) ?_
        dsimp only [csPre3, r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]
        have hm2b0 : memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 528 =
            memRegion (runFsp s0 + 0x2b0#64) 544 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 16 528 (by decide)).symm
        simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
          BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]
        refine Entails.of_eq ?_
        trans ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ ((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗
            ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗
            (memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 528) ∗
            memRegion (runFsp s0) 440 ∗ ((runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
            ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ ((runFsp s0 + 0x1c8#64) ↦₆₄ w.w5) ∗
            memRegion (runFsp s0 + 0x1d0#64) 208 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
            memRegion (runFsp s0 + 0x500#64) 9456
        · sep_ac_rfl
        · rw [hm2b0]; sep_ac_rfl
      rw [hpool_01]
      refine Entails.trans (sepConj_mono_left (Entails.trans (sepConj_mono_left hw48)
        (Entails.trans (Entails.of_eq (r1a_locals_focus (runFsp s0) cs6 0x4d0 48 _ []).symm) hcs_ent))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    )
  · obtain ⟨ikW0, ikW1, ikW2, ikW3, hikWords⟩ := r1a_exists_words32 idKey.publicKey.bytes.toList (by simp)
    have hf4d0 := r1a_locals_focus (runFsp s0) cs6 0x4d0 48 (identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (.ok idKey)) []
    (try rw [r1a_memRegion_zero (runFsp s0)])
    change SepWPp _ _ _ (runLocals (runFsp s0) (cs6 ++ [(0x4d0, 48, identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (.ok idKey))]) ∗ _) _ _ _
    rw [hf4d0]; dsimp only [identityKeyResultAt]; rw [← hikWords (runFsp s0 + 0x4d0#64 + 8#64)]
    have hhead_split : r1a_localsCtx (runFsp s0) 0 cs6 0x4d0 48 [] =
        memRegion (runFsp s0 + 0x180#64) 8 ∗ memRegion (runFsp s0 + 0x190#64) 8 ∗
          memRegion (runFsp s0 + 0x1a8#64) 8 ∗
          (memRegion (runFsp s0) 0x180 ∗ memRegion (runFsp s0 + 0x188#64) 8 ∗
            memRegion (runFsp s0 + 0x198#64) 16 ∗ r1a_localsCtx (runFsp s0) 0x1b0 cs6 0x4d0 48 []) := by
      dsimp only [cs6, r1a_localsCtx, BitVec.ofNat_eq_ofNat]
      have s1 := ProofLib.memRegion_split (runFsp s0 + 0#64) 0x180 48 (by decide)
      have s2 := ProofLib.memRegion_split (runFsp s0 + 0x180#64) 8 40 (by decide)
      have s3 := ProofLib.memRegion_split (runFsp s0 + 0x188#64) 8 32 (by decide)
      have s4 := ProofLib.memRegion_split (runFsp s0 + 0x190#64) 8 24 (by decide)
      have s5 := ProofLib.memRegion_split (runFsp s0 + 0x198#64) 16 8 (by decide)
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at s1 s2 s3 s4 s5 ⊢
      rw [s1, s2, s3, s4, s5]; sep_ac_rfl
    rw [hhead_split, ProofLib.memRegion_eight (runFsp s0 + 0x180#64),
        ProofLib.memRegion_eight (runFsp s0 + 0x190#64), ProofLib.memRegion_eight (runFsp s0 + 0x1a8#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply r1a_sepWPp_exists_pre; intro z0; apply r1a_sepWPp_exists_pre; intro z1; apply r1a_sepWPp_exists_pre; intro z2
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
    change s.pc = (blkPl_579).base + 1808#64 at hpc0
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x738) hbase.inv
    dsimp only [runProgPlaced, lsProg_579, CryptoVerification.LibsignalTripleRatchetRepr.okTagVec]
    by_vm_open (
      rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
      (iterate 10 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0
      refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]) ⟨by simp only [wp_norm, arm64_norm], fun hvm01 hinv1 => ?_⟩
      apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_ok710]
      have hpool_01 : A.pool lim st s = A.pool lim st s1 := (A.pool_of_vmPreserved hvm01).symm
      rw [hpool_01]
      have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x738 :=
        ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0],
         by simp only [arm64_norm, s1, hbase.fp], hinv1,
         by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs],
         hbase.spAligned⟩
      have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, s1, hx19]
      have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, s1, hx20]
      have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, s1, hx21]
      have hx22_1 : s1.readReg64 (.gpr 22#5) = ikW2 := by simp only [arm64_norm, s1]
      have hx25_1 : s1.readReg64 (.gpr 25#5) = ikCap := by simp only [arm64_norm, s1, hx25]
      have hx27_1 : s1.readReg64 (.gpr 27#5) = ikPtr := by simp only [arm64_norm, s1, hx27]
      have hx28_1 : s1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length := by simp only [arm64_norm, s1, hx28]
      have htr_01 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using htr
      have hfs_1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hfs
      have hfds_1 : FdsGe3Closed s1.fs := by simpa only [arm64_norm, s1] using hfds
      have hout_1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [] := by simpa only [arm64_norm, s1] using hout
      let d1 : Init1Data :=
        { peerV := peerV, peerG := peerG, meV := meV, meG := meG, dir := dir, dirCap := w.w4,
          dirPtr := w.w5, idKey := idKey, ikW0 := ikW0, ikW1 := ikW1, ikW2 := ikW2, ikW3 := ikW3 }
      have hpack_init1 :
          ((((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ (((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗
            ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗
            ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3)) ∗ memRegion (runFsp s0 + 0x4f8#64) 8) ∗
          (((runFsp s0 + 0x180#64) ↦₆₄ ikW0) ∗ ((runFsp s0 + 0x190#64) ↦₆₄ ikW3) ∗
            ((runFsp s0 + 0x1a8#64) ↦₆₄ ikW1) ∗
            (memRegion (runFsp s0) 0x180 ∗ memRegion (runFsp s0 + 0x188#64) 8 ∗
              memRegion (runFsp s0 + 0x198#64) 16 ∗ r1a_localsCtx (runFsp s0) 0x1b0 cs6 0x4d0 48 []))) ⊢
          runLocals (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) := by
        have hw48 : ((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ (((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗
            ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗
            ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3)) ∗ memRegion (runFsp s0 + 0x4f8#64) 8 ⊢
            memRegion (runFsp s0 + 0x4d0#64) 48 := by
          have s1 := (ProofLib.memRegion_split (runFsp s0 + 0x4d0#64) 8 40 (by decide)).symm
          have s2 := (ProofLib.memRegion_split (runFsp s0 + 0x4d8#64) 8 32 (by decide)).symm
          have s3 := (ProofLib.memRegion_split (runFsp s0 + 0x4e0#64) 8 24 (by decide)).symm
          have s4 := (ProofLib.memRegion_split (runFsp s0 + 0x4e8#64) 8 16 (by decide)).symm
          have s5 := (ProofLib.memRegion_split (runFsp s0 + 0x4f0#64) 8 8 (by decide)).symm
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5; rw [← s1, ← s2, ← s3, ← s4, ← s5]
          refine Entails.trans (Entails.of_eq (show _ =
            ((runFsp s0 + 0x4d0#64) ↦₆₄ -2#64) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ ikW0) ∗
              ((runFsp s0 + 0x4e0#64) ↦₆₄ ikW1) ∗ ((runFsp s0 + 0x4e8#64) ↦₆₄ ikW2) ∗
              ((runFsp s0 + 0x4f0#64) ↦₆₄ ikW3) ∗ memRegion (runFsp s0 + 0x4f8#64) 8 by sep_ac_rfl)) ?_
          exact sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))
        refine Entails.trans (sepConj_mono_left hw48) ?_
        have hdrop4d0 : runLocals (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1 ++ [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]) ⊢
            runLocals (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) :=
          r1a_locals_drop_mid (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) 0x4d0 48 _ [] (Entails.refl _)
        refine Entails.trans (Entails.of_eq ?_) hdrop4d0
        rw [r1a_locals_focus (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) 0x4d0 48 _ []]
        dsimp only [init1Cells, d1, cs6, r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]
        simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
          BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]
        sep_ac_rfl
      refine r1a_sepWPp_weaken_pre (sepConj_mono_left hpack_init1) ?_
      have hmeVal : d1.meG.val = addrValOf d1.meV := by
        rcases hd.meRegs with ⟨_, _, hnb, _, hdev⟩; dsimp only [d1, AddrGhost.val, addrValOf]; rw [hnb, hdev]
      have hfinish : ∀ (s2 : State) (evs_fi : List AllocEvent), FreeOnlyEvs evs_fi →
          InRunPlaced r1a_CodeOk s0 s2 0x74c → s2.readReg64 (.gpr 19#5) = g.stores →
          s2.readReg64 (.gpr 20#5) = g.res → s2.readReg64 (.gpr 21#5) = meG.name.cap →
          s2.readReg64 (.gpr 22#5) = ikW2 → s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length →
          s0.trace <+: s2.trace → s2.fs.files = runFiles g.i → FdsGe3Closed s2.fs →
          ProcessOutcome.traceStreamBytes .stdout s2.trace = [] →
          SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
            (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_fi st) s2 ∗
              (runLocals (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) ∗
                addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
                memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
                CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0))
            Q Qp (runOom s0) := by
        intro s2 evs_fi hfi hb2 r19 r20 r21 r22 r28 tr2 fs2 fds2 out2
        have hpa : protocolAddressAt (A.atState lim (M.stepEvents evs_fi st) s2) d1.peerG (runFsp s0 + 0x2a0#64) =
            protocolAddressAt A.repAlloc d1.peerG (runFsp s0 + 0x2a0#64) := by
          rw [protocolAddressAt_eq_parts, protocolAddressAt_eq_parts]; rfl
        have hic : init1Cells (A.atState lim (M.stepEvents evs_fi st) s2) (runFsp s0) d1 =
            init1Cells A.repAlloc (runFsp s0) d1 := by
          dsimp only [init1Cells]; rw [hpa]
        have hanh : addrNameHeap (A.atState lim (M.stepEvents evs_fi st) s2) d1.meG =
            addrNameHeap A.repAlloc meG := rfl
        refine r1a_sepWPp_weaken_pre
          (by dsimp only [init1MemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.init1MemPlaced]
              rw [storesAt_opened_atState, hanh, ownedBytes_congr_live (A₂ := A.repAlloc) rfl, hic,
                  RustCliAllocBudget.atState_pool]
              dsimp only [d1]; rw [hw6]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext s2 evs_fi d1 hfi ⟨hb2, hcall, r19, r20, r21, r22, r28, rfl, hmeVal, hd.ownSem,
            ⟨ikB, r1a_ikOk_sem hik hdec⟩, hikWords, tr2, fs2, out2⟩ fds2)
      have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp
      change s1.pc = (blkPl_579).base + 1848#64 at hpc1
      by_cases hik0 : ikCap = 0#64
      · apply sepWPp_seq_lscro (mid := runPcPlaced 0x74c) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
        (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx25_1, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1])
        intro hinv2; apply r1a_bind_sepWPp_state; intro s2z
        have hpool_12z : A.pool lim st s1 = A.pool lim (M.stepEvents [] st) s2z :=
          r1a_pool_congr_vm A lim st (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm])
            (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm]) (fun _ => by simp only [s2z, arm64_norm])
        refine r1a_sepWPp_weaken_pre ?_
          (hfinish s2z [] FreeOnlyEvs.nil
            ⟨by simp only [s2z, runPcPlaced_eq, arm64_norm, hx25_1, hik0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
             by simp only [s2z, arm64_norm, hrun1], by simp only [s2z, arm64_norm, hsp1],
             by simp only [s2z, arm64_norm, hb1.fp], hinv2,
             by simp only [s2z, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
             hbase.spAligned⟩
            (by simp only [s2z, arm64_norm, hx19_1]) (by simp only [s2z, arm64_norm, hx20_1])
            (by simp only [s2z, arm64_norm, hx21_1]) (by simp only [s2z, arm64_norm, hx22_1])
            (by simp only [s2z, arm64_norm, hx28_1]) (by simpa only [s2z, arm64_norm] using htr_01)
            (by simpa only [s2z, arm64_norm] using hfs_1)
            (by simpa only [s2z, arm64_norm] using hfds_1)
            (by simpa only [s2z, arm64_norm] using hout_1))
        rw [hpool_12z]
        refine Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hik0))) ?_
        rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)
      · have hne_ik : (ikCap == 0#64) = false := beq_false_of_ne hik0
        apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hb1.inv; try dsimp only [runProgPlaced, lsProg_579]
        (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm, hx25_1, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte]) (by simp only [arm64_norm, hrun1])
        intro hinv_c; apply r1a_bind_sepWPp_state; intro sc
        have hpool_1c : A.pool lim st s1 = A.pool lim st sc :=
          r1a_pool_congr_vm A lim st (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm])
            (by simp only [sc, arm64_norm]) (by simp only [sc, arm64_norm]) (fun _ => by simp only [sc, arm64_norm])
        refine r1a_sepWPp_weaken_pre
          (by rw [hpool_1c]
              exact Entails.of_eq (show _ =
                ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
                  stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sc ∗
                  (runLocals (runFsp s0) (init1Cells A.repAlloc (runFsp s0) d1) ∗
                    addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
                    memRegion g.res runResSize ∗ memRegion g.call 56 ∗
                    storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                    coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
                    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0)
                by sep_ac_rfl)) ?_
        refine r1b_call_dealloc_ownedBytes_placed (retOff := 0x74c) hh hbnd hinv_c
          (by simp only [sc, lsRustDeallocSymCli, arm64_norm, hx25_1, hne_ik, bne, Bool.not_false, Bool.not_true, ↓reduceIte])
          (by simp only [sc, arm64_norm, hrun1]) (by simp only [sc, arm64_norm, hsp1])
          (by simp only [sc, arm64_norm, hb1.fp])
          (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs])
          hbase.spAligned
          (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          (by simp only [sc, arm64_norm, hx27_1]) (by simp only [sc, arm64_norm, hx25_1])
          (by simp only [sc, arm64_norm]) hik0 hpanic fun sm hbm hcsm hfsm htrm => ?_
        exact hfinish sm (rustDeallocEvents ikCap.toNat 1) (FreeOnlyEvs.singleton 1 ikCap.toNat) hbm
          (by simpa only [sc, arm64_norm, hx19_1] using hcsm.1)
          (by simpa only [sc, arm64_norm, hx20_1] using hcsm.2.1)
          (by simpa only [sc, arm64_norm, hx21_1] using hcsm.2.2.1)
          (by simpa only [sc, arm64_norm, hx22_1] using hcsm.2.2.2.1)
          (by simpa only [sc, arm64_norm, hx28_1] using hcsm.2.2.2.2.2.2.2.2.2.1)
          (by simpa only [htrm, sc, arm64_norm] using htr_01)
          (by simpa only [hfsm, sc, arm64_norm] using hfs_1)
          (by simpa only [hfsm, sc, arm64_norm] using hfds_1)
          (by simpa only [htrm, sc, arm64_norm] using hout_1)
    )

/-! ## `read_file` Post-Call Dispatch (`0x6bc → 0x74c`) -/

set_option maxHeartbeats 800000 in
theorem r1a_after_read_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW}
    {pathCap pathPtr : BitVec 64} {r : Except Unit Bytes} {s0 s_disp s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp)
    (hcall : g.c = .init peerV dir)
    (hfits22 : r = .error () → FitsEvents M lim st (rustAllocEvents 22 1))
    (hpanic : PanicK g s0 Qp)
    (hrej_err : r = .error () → FreeRejK A lim (M.stepEvents (rustAllocEvents 22 1) st) H g s0 resStack Q Qp)
    (hrej_ok : ∀ ikB (evs_fp : List AllocEvent), r = .ok ikB → FreeOnlyEvs evs_fp →
      FreeRejK A lim (M.stepEvents evs_fp st) H g s0 resStack Q Qp)
    (hnext_ok : ∀ ikB (evs_fp evs_fi : List AllocEvent) (s1 : State) (d1 : Init1Data),
      r = .ok ikB → FreeOnlyEvs evs_fp → FreeOnlyEvs evs_fi →
      AtInit1Placed r1a_CodeOk g d1 s0 s1 →
      FdsGe3Closed s1.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs_fi (M.stepEvents evs_fp st)) g d1 s0 s1 resStack)
        Q Qp (runOom s0))
    (hikStk : 0x60 ≤ resStack - runFrame)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x6bc)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (_hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length)
    (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length)
    (htr : s0.trace <+: s.trace)
    (hfds : FdsGe3Closed s.fs)
    (herr_f : r = .error () → RunHistOk g.i s0 s ∧ g.a = some none)
    (hok_f : ∀ ikB, r = .ok ikB →
      cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB ∧
        s.fs.files = runFiles g.i ∧ ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
           (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
           (0x2a0, 32, protocolAddressAt A.repAlloc (r1a_peerGhostOf peerV w) (runFsp s0 + 0x2a0#64)),
           (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48),
           (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap),
           (0x23b0, 24, ioVecAt A.repAlloc (runFsp s0 + 0x23b0#64) r)] ∗
        ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s) Q Qp (runOom s0) := by
  intro pathBs
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnd.sub64
  let peerG := r1a_peerGhostOf peerV w
  let cs8 :=
    [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
     (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
     (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)),
     (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48),
     (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
  have hf23b0 := r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (ioVecAt A.repAlloc (runFsp s0 + 0x23b0#64) r) []
  (try rw [r1a_memRegion_zero (runFsp s0)])
  change SepWPp _ _ _ (runLocals (runFsp s0) (cs8 ++ [(0x23b0, 24, ioVecAt A.repAlloc (runFsp s0 + 0x23b0#64) r)]) ∗ _) _ _ _
  rw [hf23b0]
  rcases r with ⟨⟨⟩⟩ | ikB
  · dsimp only [ioVecAt]
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
    change s.pc = (blkPl_579).base + 1724#64 at hpc0
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x878) hbase.inv
    try dsimp only [runProgPlaced, lsProg_579]; rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
    (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
    intro hinv1; apply r1a_bind_sepWPp_state; intro s1e
    (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group2c]
    have hpool_e : A.pool lim st s = A.pool lim st s1e :=
      r1a_pool_congr_vm A lim st (by simp only [s1e, arm64_norm]) (by simp only [s1e, arm64_norm])
        (by simp only [s1e, arm64_norm]) (by simp only [s1e, arm64_norm]) (fun _ => by simp only [s1e, arm64_norm])
    refine r1a_sepWPp_weaken_pre ?_
      (r1a_read_err (peerV := peerV) (dir := dir) (pathBs := pathBs) (meG := meG) (w := w)
        (pathCap := pathCap) (pathPtr := pathPtr)
        (F_heap := coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff)
        hh hdrop hbnd (hfits22 rfl) hpanic (hrej_err rfl)
        ⟨by simp only [s1e, runPcPlaced_eq, arm64_norm, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s1e, arm64_norm, hrun0], by simp only [s1e, arm64_norm, hsp0],
         by simp only [s1e, arm64_norm, hbase.fp], hinv1,
         by simp only [s1e, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [s1e, arm64_norm, hx19]) (by simp only [s1e, arm64_norm, hx20])
        (by simp only [s1e, arm64_norm, hx21]) (by simp only [s1e, arm64_norm]; decide)
        (by simp only [s1e, arm64_norm, hx24]) (by simp only [s1e, arm64_norm, hx26])
        (by simpa only [s1e, arm64_norm] using htr)
        (r1a_hist_ans_step (herr_f rfl) (by simp only [s1e, arm64_norm]) (by simp only [s1e, arm64_norm])))
    have hm24 : ∀ v, ((runFsp s0 + 0x23b0#64) ↦₆₄ v) ∗ memRegion (runFsp s0 + 0x23b8#64) 16 ⊢
        memRegion (runFsp s0 + 0x23b0#64) 24 := fun v => by
      have hs24 := ProofLib.memRegion_split (runFsp s0 + 0x23b0#64) 8 16 (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hs24; rw [hs24]
      exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    rw [hpool_e]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left (hm24 _))) ?_
    rw [← r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (memRegion (runFsp s0 + 0x23b0#64) 24) []]
    have hdrop23b0 : runLocals (runFsp s0) (cs8 ++ [(0x23b0, 24, memRegion (runFsp s0 + 0x23b0#64) 24)]) ⊢
        runLocals (runFsp s0) cs8 := r1a_locals_drop_mid (runFsp s0) cs8 0x23b0 24 _ [] (Entails.refl _)
    let csPre3 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
      (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5)]
    let csSuf2 := [(0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48), (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
    let csSuf3 := (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)) :: csSuf2
    have hdrop1b0 : runLocals (runFsp s0) cs8 ⊢
        runLocals (runFsp s0) (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3) :=
      r1a_locals_drop_head (runFsp s0) 0x1b0 4 _
        (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3)
        (r1a_pointsTo32_entails_memRegion _ _)
    have hdrop260 : runLocals (runFsp s0) (csPre3 ++ (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG) :: csSuf3) ⊢
        runLocals (runFsp s0) (csPre3 ++ csSuf3) :=
      r1a_locals_drop_mid (runFsp s0) csPre3 0x260 16 _ csSuf3 (addrUpperAt_entails_memRegion _ _)
    refine Entails.trans (sepConj_mono_left (Entails.trans hdrop23b0 (Entails.trans hdrop1b0 hdrop260))) ?_
    change (runLocals (runFsp s0) (csPre3 ++ (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)) :: csSuf2) ∗ _) ⊢ _
    rw [r1a_locals_focus (runFsp s0) csPre3 0x2a0 32 (protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)) csSuf2,
        protocolAddressAt_eq_parts A.repAlloc peerG (runFsp s0 + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]
    dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
    have hsplit_peer :
        (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a0#64 + 8#64) ↦₆₄ w.w1) ∗
          addrUpperAt (runFsp s0 + 0x2a0#64 + 16#64) (r1a_peerGhostOf peerV w) ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name) ∗
          r1a_localsCtx (runFsp s0) 0 csPre3 0x2a0 32 csSuf2 ⊢
        runLocals (runFsp s0) (csPre3 ++ (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ::
          (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) :: csSuf2) ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (addrUpperAt_entails_memRegion _ _))))) ?_
      have hc1 := r1a_locals_drop_mid (runFsp s0)
        (csPre3 ++ [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)])
        0x2b0 16 (memRegion (runFsp s0 + 0x2b0#64) 16) csSuf2 (Entails.refl _)
      refine Entails.trans ?_ (sepConj_mono_left hc1)
      simp only [csPre3, csSuf2, List.append_assoc, List.cons_append, List.nil_append, BitVec.add_assoc, BitVec.reduceAdd]
      dsimp only [r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by sep_ac_rfl)
    refine Entails.trans (sepConj_mono_left hsplit_peer) ?_
    dsimp only [csPre3, csSuf2]; simp only [List.cons_append, List.nil_append]; exact Entails.of_eq (by sep_ac_rfl)
  · obtain ⟨hik, hfs_ok, hout_ok⟩ := hok_f ikB rfl
    dsimp only [ioVecAt]
    refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc _ ikB))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply r1a_sepWPp_exists_pre; intro ikCap; apply r1a_sepWPp_exists_pre; intro ikPtr
    rw [ownedBytes_pure A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB]
    have hp_ik {P0 : Prop} (W0 W1 W2 Y0 C0 P1 R0 : SepProp) :
        ((W0 ∗ W1 ∗ W2 ∗ ⌜P0⌝ ∗ Y0) ∗ C0) ∗ P1 ∗ R0 = ⌜P0⌝ ∗ ((((W0 ∗ W1 ∗ W2) ∗ C0) ∗ P1 ∗ Y0) ∗ R0) := by sep_ac_rfl
    rw [hp_ik]; apply r1a_sepWPp_pure_pre; rintro ⟨_, _hik_le, hik_lt, _⟩
    have hik_ne : (ikCap + 1#64 == 0#64) = false := beq_add_one_zero_false_of_lt hik_lt
    let cs7 :=
      [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
       (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
       (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
       (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
       (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
       (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)),
       (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
    have hafter_path : ∀ (evs_fp : List AllocEvent), FreeOnlyEvs evs_fp → ∀ s2 : State,
        InRunPlaced r1a_CodeOk s0 s2 0x6f4 → s2.readReg64 (.gpr 19#5) = g.stores →
        s2.readReg64 (.gpr 20#5) = g.res → s2.readReg64 (.gpr 21#5) = meG.name.cap →
        s2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 ikB.length → s2.readReg64 (.gpr 23#5) = ikCap →
        s2.readReg64 (.gpr 24#5) = w.w4 → s2.readReg64 (.gpr 25#5) = ikCap →
        s2.readReg64 (.gpr 27#5) = ikPtr → s2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 dir.length →
        s0.trace <+: s2.trace → s2.fs.files = runFiles g.i → FdsGe3Closed s2.fs →
        ProcessOutcome.traceStreamBytes .stdout s2.trace = [] →
        SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
          (runLocals (runFsp s0) cs7 ∗
            ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
            addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs_fp st) s2)
          Q Qp (runOom s0) := by
      intro evs_fp hfp s2 hb2 r19 r20 r21 r22 r23 r24 r25 r27 r28 tr2 fs2 fds2 out2
      let st_p := M.stepEvents evs_fp st
      let csPre2 := [(0x1b0, 4, (runFsp s0 + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
        (0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr)]
      let csSuf4 := [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
        (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
        (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64)),
        (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      (try rw [r1a_memRegion_zero (runFsp s0)])
      change SepWPp _ _ _ (runLocals (runFsp s0) (csPre2 ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csSuf4) ∗ _) _ _ _
      rw [r1a_locals_focus (runFsp s0) csPre2 0x1c0 8 (memRegion (runFsp s0 + 0x1c0#64) 8) csSuf4,
          ProofLib.memRegion_eight (runFsp s0 + 0x1c0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro c1c0
      have hpc2 := hb2.pc; have := hb2.spAligned_cur; have hrun2 := hb2.run; have hsp2 := hb2.sp
      change s2.pc = (blkPl_579).base + 1780#64 at hpc2
      apply sepWPp_seq_lscro (mid := (blkPl_18).base) hb2.inv
      (try dsimp only [runProgPlaced, lsProg_579])
      by_vm_open (
        rw [← hsp2]; symm at hsp2; wp_simp_pre only [sepConj_assoc]
        (iterate 7 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hsp2
        refine SepWP.done (by simp only [arm64_norm, r23, hik_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte]; try rfl) (by simp only [arm64_norm, hrun2]) ⟨by simp only [wp_norm, arm64_norm], fun hvm2d hinv_d => ?_⟩
        apply r1a_bind_sepWPp_state; intro sd; (try simp only [arm64_norm, r24]); (try rw [hsp2])
        have hpool_2d : A.pool lim st_p s2 = A.pool lim st_p sd := (A.pool_of_vmPreserved hvm2d).symm
        have hfds_d : FdsGe3Closed sd.fs := by simpa only [arm64_norm, sd] using fds2
        let csPre6 := csPre2 ++ (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ::
          [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x260, 16, addrUpperAt (runFsp s0 + 0x260#64) meG),
           (0x2a0, 32, protocolAddressAt A.repAlloc peerG (runFsp s0 + 0x2a0#64))]
        have hfold4d0 : ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ r1a_localsCtx (runFsp s0) 0 csPre2 0x1c0 8 csSuf4 =
            memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 [] := by
          rw [← r1a_locals_focus (runFsp s0) csPre2 0x1c0 8 ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) csSuf4]
          exact r1a_locals_focus (runFsp s0) csPre6 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
        let sub := resStack - runFrame
        let rem60 := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - 0x60)
        have hstk60 : stackAt (runFsp s0) sub = rem60 ∗ stackAt (runFsp s0) 0x60 :=
          r1a_stackAt_split (runFsp s0) hikStk hsub64
        refine r1a_call_run (x := ⟨ikPtr, ikB, runFsp s0 + 0x4d0#64⟩)
          (F := r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 [] ∗
            r1a_ownedSlack A.repAlloc ikCap ikPtr ikB ∗ rem60 ∗ addrNameHeap A.repAlloc meG ∗
            ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗ memRegion g.res runResSize ∗
            memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗ runSaved s0 ∗ A.pool lim st_p sd)
          (retOff := 0x710) (hh.fs (runProgPlaced H) 579)
          (identityKeyDecode_keepsFs_vm_placed_ok (callerProg := runProgPlaced H) (i := 579) A)
          (by simp only [arm64_norm, sd, r23, hik_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte]; rfl)
          (by simp only [arm64_norm, sd, hrun2]) hinv_d (by simp only [arm64_norm, sd, hsp2])
          (by simp only [arm64_norm, sd, hb2.fp])
          (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, sd, hb2.vregs])
          hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, sd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          hpanic
          (by dsimp only [Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]
              rw [← sepConj_assoc, hfold4d0, r1a_ownedBytes_expose A.repAlloc ikCap ikPtr ikB, hstk60, hpool_2d]
              have hlen_ik : (BitVec.ofNat 64 ikB.length).toNat = ikB.length := Nat.mod_eq_of_lt (by omega)
              refine Entails.trans (Entails.of_eq (by
                (try simp only [arm64_norm, sd]); (try rw [hsp2])
                dsimp only [lsLogOff, lsLogFilterAddr, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff, lsρ]
                sep_ac_rfl))
                (sepConj_mono_left (Entails.pure_right
                  ⟨by simp only [arm64_norm, sd, r27], by simp only [arm64_norm, sd, r22, hlen_ik],
                   by simp only [arm64_norm, sd, hsp2]⟩ (Entails.refl _))))
          (fun _ => by dsimp only [Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails)
          (fun _ _ => by dsimp only [Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact Entails.refl _)
          (fun _ => by dsimp only [Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails) ?_
        intro s3 hb3 hcs3 _ hfiles3
        dsimp only [Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]
        rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
        apply r1a_sepWPp_pure_pre; intro hfs3
        apply r1a_sepWPp_pure_pre; intro hvm3; apply r1a_sepWPp_pure_pre; intro htr3
        rw [← A.pool_transport lim st_p sd s3 hvm3]
        refine r1a_sepWPp_weaken_pre ?_
          (r1a_after_decode_fd hh hdrop hbnd he hd hcall hpanic
            (hrej_ok ikB evs_fp rfl hfp)
            (fun s1' evs_fi d1 hfi hat1 hfds1 => hnext_ok ikB evs_fp evs_fi s1' d1 rfl hfp hfi hat1 hfds1)
            hb3
            (by simpa only [arm64_norm, sd, r19] using hcs3.1)
            (by simpa only [arm64_norm, sd, r20] using hcs3.2.1)
            (by simpa only [arm64_norm, sd, r21] using hcs3.2.2.1)
            (by simpa only [arm64_norm, sd, r25] using hcs3.2.2.2.2.2.2.1)
            (by simpa only [arm64_norm, sd, r27] using hcs3.2.2.2.2.2.2.2.2.1)
            (by simpa only [arm64_norm, sd, r28] using hcs3.2.2.2.2.2.2.2.2.2.1)
            hik hw6 hw2 (by simpa only [htr3, arm64_norm, sd] using tr2)
            ((hfiles3 htr3).trans (by simpa only [arm64_norm, sd] using fs2))
            (hfs3 ▸ hfds_d)
            (by simpa only [htr3, arm64_norm, sd] using out2))
        have hsd_sp : sd.sp = runFsp s0 := by simp only [sd, arm64_norm, hsp2]
        rw [hsd_sp]
        have hback4d0 := (r1a_locals_focus (runFsp s0) csPre6 0x4d0 48 (identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB)) []).symm
        dsimp only [csPre6, csPre2, peerG] at hback4d0
        simp only [List.cons_append, List.append_assoc, List.nil_append] at hback4d0
        refine Entails.of_eq ?_
        trans (identityKeyResultAt A.repAlloc (runFsp s0 + 0x4d0#64) (decodeIdentityKey ikB) ∗
            r1a_localsCtx (runFsp s0) 0 csPre6 0x4d0 48 []) ∗
          ((ikPtr ↦ₛ ikB) ∗ r1a_ownedSlack A.repAlloc ikCap ikPtr ikB) ∗
          addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          stackAt (runFsp s0) sub ∗ A.pool lim st_p s3
        · rw [hstk60]
          dsimp only [lsLogOff, lsLogFilterAddr, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff, lsρ]
          sep_ac_rfl
        · rw [← r1a_ownedBytes_expose A.repAlloc ikCap ikPtr ikB]
          dsimp only [csPre6, csPre2, peerG]
          simp only [List.cons_append, List.append_assoc, List.nil_append]
          rw [← hback4d0]
      )
    have hcollapse_slots :
        (((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗
          ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗
          r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 [] ⊢
        runLocals (runFsp s0) cs7 := by
      have hw24 : ((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗
          ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length) ⊢
          memRegion (runFsp s0 + 0x23b0#64) 24 := by
        have s1 := (ProofLib.memRegion_split (runFsp s0 + 0x23b0#64) 8 16 (by decide)).symm
        have s2 := (ProofLib.memRegion_split (runFsp s0 + 0x23b8#64) 8 8 (by decide)).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2; rw [← s1, ← s2]
        exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))
      refine Entails.trans (sepConj_mono_left hw24) ?_
      rw [← r1a_locals_focus (runFsp s0) cs8 0x23b0 24 (memRegion (runFsp s0 + 0x23b0#64) 24) []]
      refine Entails.trans (r1a_locals_drop_mid (runFsp s0) cs8 0x23b0 24 _ [] (Entails.refl _)) ?_
      exact r1a_locals_drop_mid (runFsp s0) cs7 0x1750 8 _ [] (pointsTo64_entails_memRegion _ _)
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
    change s.pc = (blkPl_579).base + 1724#64 at hpc0
    by_cases hp0 : pathCap = 0#64
    · apply sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hbase.inv
      dsimp only [cs8, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
      (iterate 9 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
      intro hinv1; apply r1a_bind_sepWPp_state; intro s2z
      (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_6bc]
      have hpool_z : A.pool lim st s = A.pool lim (M.stepEvents [] st) s2z :=
        r1a_pool_congr_vm A lim st (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm])
          (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm]) (fun _ => by simp only [s2z, arm64_norm])
      rw [hpool_z]
      refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
        (((((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗
          ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗
          r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 []) ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
          ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim (M.stepEvents [] st) s2z
        by simp only [cs8, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat,
             BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]
           sep_ac_rfl)) ?_
      refine r1a_sepWPp_weaken_pre ?_
        (hafter_path [] FreeOnlyEvs.nil s2z
          ⟨by simp only [s2z, runPcPlaced_eq, arm64_norm, hik_ne, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [s2z, arm64_norm, hrun0], by simp only [s2z, arm64_norm, hsp0],
           by simp only [s2z, arm64_norm, hbase.fp], hinv1,
           by simp only [s2z, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
           hbase.spAligned⟩
          (by simp only [s2z, arm64_norm, hx19]) (by simp only [s2z, arm64_norm, hx20])
          (by simp only [s2z, arm64_norm, hx21]) (by simp only [s2z, arm64_norm])
          (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm, hx24])
          (by simp only [s2z, arm64_norm]) (by simp only [s2z, arm64_norm])
          (by simp only [s2z, arm64_norm, hx28]) (by simpa only [s2z, arm64_norm] using htr)
          (by simpa only [s2z, arm64_norm] using hfs_ok)
          (by simpa only [s2z, arm64_norm] using hfds)
          (by simpa only [s2z, arm64_norm] using hout_ok))
      refine Entails.trans (sepConj_mono_left (sepConj_mono hcollapse_slots (sepConj_mono_left (r1a_ownedBytes_zero hp0)))) ?_
      rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)
    · have hp_be : (pathCap == 0#64) = false := beq_false_of_ne hp0
      apply sepWPp_seq_lscro (mid := runPcPlaced 0x6e0) hbase.inv
      dsimp only [cs8, r1a_localsCtx, BitVec.ofNat_eq_ofNat]; try dsimp only [runProgPlaced, lsProg_579]
      rw [← hsp0]; symm at hsp0; wp_simp_pre only [sepConj_assoc]
      (iterate 9 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hik_ne, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
      intro hinv1; apply r1a_bind_sepWPp_state; intro s2p
      (try simp only [arm64_norm]); (try rw [hsp0]); rw [r1a_group_6bc]
      have hpool_p : A.pool lim st s = A.pool lim st s2p :=
        r1a_pool_congr_vm A lim st (by simp only [s2p, arm64_norm]) (by simp only [s2p, arm64_norm])
          (by simp only [s2p, arm64_norm]) (by simp only [s2p, arm64_norm]) (fun _ => by simp only [s2p, arm64_norm])
      rw [hpool_p]
      refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
        (((((runFsp s0 + 0x23b0#64) ↦₆₄ ikCap) ∗ ((runFsp s0 + 0x23b8#64) ↦₆₄ ikPtr) ∗
          ((runFsp s0 + 0x23c0#64) ↦₆₄ BitVec.ofNat 64 ikB.length)) ∗
          r1a_localsCtx (runFsp s0) 0 cs8 0x23b0 24 []) ∗
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
          ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s2p
        by simp only [cs8, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat,
             BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp]
           sep_ac_rfl)) ?_
      refine r1a_sepWPp_weaken_pre (Entails.trans (sepConj_mono_left (sepConj_mono_left hcollapse_slots))
        (Entails.of_eq (show
          (runLocals (runFsp s0) cs7 ∗
            ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
            ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB) ∗
            addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s2p =
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
            stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s2p ∗
            (runLocals (runFsp s0) cs7 ∗
              ownedBytes A.repAlloc ikCap ikPtr (BitVec.ofNat 64 ikB.length) ikB ∗
              addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0)
          by sep_ac_rfl))) ?_
      apply r1a_free_path_6e0_fd hh hbnd hpanic hp0
        ⟨by simp only [s2p, runPcPlaced_eq, arm64_norm, hik_ne, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s2p, arm64_norm, hrun0], by simp only [s2p, arm64_norm, hsp0],
         by simp only [s2p, arm64_norm, hbase.fp], hinv1,
         by simp only [s2p, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [s2p, arm64_norm]) (by simp only [s2p, arm64_norm, hx26])
      intro sm4 hb4 _ r19 r20 r21 r22 r23 r24 r25 r27 r28 htrm4 hfsm4
      exact r1a_sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hafter_path (rustDeallocEvents pathCap.toNat 1) (FreeOnlyEvs.singleton 1 pathCap.toNat) sm4 hb4
          (by simpa only [s2p, arm64_norm, hx19] using r19)
          (by simpa only [s2p, arm64_norm, hx20] using r20)
          (by simpa only [s2p, arm64_norm, hx21] using r21)
          (by simpa only [s2p, arm64_norm] using r22)
          (by simpa only [s2p, arm64_norm] using r23)
          (by simpa only [s2p, arm64_norm, hx24] using r24)
          (by simpa only [s2p, arm64_norm] using r25)
          (by simpa only [s2p, arm64_norm] using r27)
          (by simpa only [s2p, arm64_norm, hx28] using r28)
          (by simpa only [htrm4, s2p, arm64_norm] using htr)
          (by simpa only [hfsm4, s2p, arm64_norm] using hfs_ok)
          (by simpa only [hfsm4, s2p, arm64_norm] using hfds)
          (by simpa only [htrm4, s2p, arm64_norm] using hout_ok))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd
