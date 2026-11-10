/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Post-Read and Post-Decode Sub-Hops for Budget-Threaded Arm `R1a`

Verifies the `read_file` error branch and `IdentityKey::decode` post-call dispatch on Block `579`
supporting `R1aProofPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWPp_seq_lscro subroutine_ok_withLsCodeRoLoaded_of_plain)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsLogOff withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt speWord)
open CryptoVerification.RecordCodecs (decodeIdentityKey)
open CryptoVerification.RecordCodecs.Placed (blkPl_18)
open CryptoVerification.RecordCodecsBinary (identityKeyResultAt)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.SignalSession
  (lsReadFileSym lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (PathGhost ReadFileGhost StoresGhost ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW RunCall addrWords callAt callHeap cliIo cliWrOk coinsInstalledPlaced coinsOf
   inputOf ownedBytes runResSize storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (beq_add_one_zero_false_of_lt entails_pure_intro_left ownedBytes_pure vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_596)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtRunEntryPlaced Bytes InRunPlaced Init1Data MeAtDispatch PanicK
   RunHistOk RunNeeds RunSem addrNameHeap addrUpperAt addrUpperAt_entails_memRegion addrValOf
   dispatchCells dispatchMeHeap init1Cells protocolAddressAt_eq_parts r1b_StackBounds runAns
   runFiles runFsp runLocalBytes runLocals runLocalsFrom runOom runPcPlaced runPcPlaced_eq
   runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed runFrame)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsLen lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget (RunHopInit1Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
  (FreeRejK identityKeyDecode_vm_placed_ok r1a_CodeOk r1a_addrNameHeap_eq_owned r1a_addrUpperAt_close
   r1a_addrUpperAt_open r1a_bind_sepWPp_state r1a_buf22_merge r1a_buf22_reassoc
   r1a_call7_to_memRegion56 r1a_call_run r1a_decode_err_unified r1a_exists_words32 r1a_false_entails
   r1a_freeOnly_append r1a_group2c r1a_group4_7 r1a_group6c r1a_group_6bc r1a_group_8b0
   r1a_group_mid2 r1a_group_mid6 r1a_group_ok710 r1a_high64 r1a_hist_ans_step r1a_idKeySym
   r1a_idKey_path_bounds r1a_ikOk_sem r1a_localsBound r1a_localsCtx r1a_localsEnd
   r1a_locals_carve_region r1a_locals_drop_head
   r1a_locals_drop_mid r1a_locals_focus r1a_low64 r1a_memRegion32_eq_words r1a_memRegion48_words
   r1a_memRegion_zero r1a_ownedBytes_expose r1a_ownedBytes_zero r1a_ownedSlack r1a_peerGhostOf
   r1a_pointsTo32_entails_memRegion r1a_pool_setMem_write16 r1a_pool_setMem_write32
   r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
   r1a_pool_setMem_write64_4 r1a_pool_setMem_write8 r1a_readFile_post_facts
   r1a_reject_of_decode_err r1a_rodata_idkey_intro r1a_rodata_unreadable_intro
   r1a_sepWPp_exists_pre r1a_sepWPp_pure_left r1a_sepWPp_pure_pre r1a_sepWPp_weaken_pre
   r1a_stackAt_split r1a_unreadSym r1a_utf8_idkey_len r1a_utf8_unreadable_len
   r1a_vec22_withString_intro r1a_words6_to_memRegion48)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
  (r1a_decode_err r1a_free_path_6e0 r1a_me_none r1a_tail_after_spe)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed r1b_stackBounds_of_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced init1MemPlaced ownedBytes_congr_live runNeed_bounds_placed
   storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced path_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (pathSpecPlaced readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOomExtern_lscro_of_cli shim_lscro_of_cli)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomExternSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  r1a_pool_setMem_write8 r1a_pool_setMem_write16 r1a_pool_setMem_write32
  r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
  r1a_pool_setMem_write64_4

/-! ## Allocation-Event Envelopes -/
theorem r1a_pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk) (htp : s'.tpidrEl0 = s.tpidrEl0)
    (hph : s'.physMemAvail = s.physMemAvail) (hperm : ∀ a, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s = A.pool lim st s' :=
  (A.pool_transport lim st s s' ⟨⟨hbs, hbrk, htp⟩, hph, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩).symm

/-! ## `read_file` Error and `IdentityKey::decode` Post-Call Paths -/

set_option maxHeartbeats 800000 in
theorem r1a_read_err [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {peerV : AddrV}
    {dir pathBs : Bytes} {meG : AddrGhost} {w : CallW} {pathCap pathPtr : BitVec 64}
    {s0 s : State} {resStack : Nat} {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hfits22 : FitsEvents M lim st (rustAllocEvents 22 1))
    (hpanic : PanicK g s0 Qp)
    (hrej_a : FreeRejK A lim (M.stepEvents (rustAllocEvents 22 1) st) H g s0 resStack Q Qp)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x878)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx23 : s.readReg64 (.gpr 23#5) = -1#64)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr)
    (htr : s0.trace <+: s.trace) (hhans : RunHistOk g.i s0 s ∧ g.a = some none) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0)
          [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
           (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
           (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
           (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
           (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
           (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48),
           (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)] ∗
        ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
        memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
        A.pool lim st s ∗ F_heap) Q Qp (runOom s0) := by
  let sub := resStack - runFrame
  have hext : extHookStack ≤ sub := hbnd.hook
  have hsub64 : sub ≤ 2 ^ 64 := hbnd.sub64
  let rem := memRegion (runFsp s0 - BitVec.ofNat 64 sub) (sub - extHookStack)
  let csErr :=
    [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
     (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
     (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
     (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
     (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
     (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48),
     (0x1750, 8, (runFsp s0 + 0x1750#64) ↦₆₄ pathCap)]
  let restMem :=
    runLocals (runFsp s0) csErr ∗
      ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
      addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
      ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
      memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
      (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  change s.pc = (blkPl_579).base + 2168#64 at hpc0
  apply sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustNoAllocShimSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0])
  intro hinv_s; apply r1a_bind_sepWPp_state; intro sc0
  have hpool_0 : A.pool lim st s = A.pool lim st sc0 :=
    r1a_pool_congr_vm A lim st (by simp only [sc0, arm64_norm]) (by simp only [sc0, arm64_norm])
      (by simp only [sc0, arm64_norm]) (by simp only [sc0, arm64_norm]) (fun _ => by simp only [sc0, arm64_norm])
  refine r1a_call_run (x := ()) (F := rem ∗ A.pool lim st sc0 ∗ restMem) (retOff := 0x87c)
    (hh.fs (runProgPlaced H) 579) (shim_lscro_of_cli hh.alloc (stk := extHookStack))
    (by simp only [sc0, lsRustNoAllocShimSymCli, arm64_norm]) (by simp only [sc0, arm64_norm, hrun0])
    hinv_s (by simp only [sc0, arm64_norm, hsp0]) (by simp only [sc0, arm64_norm, hbase.fp])
    (by simp only [sc0, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
    hbase.spAligned (by simp only [sc0, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    hpanic
    (by have hs : stackAt (runFsp s0) sub = rem ∗ stackAt (runFsp s0) extHookStack :=
          r1a_stackAt_split (runFsp s0) hext hsub64
        dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, sub, restMem, csErr] at hs ⊢
        rw [hs, hpool_0]; (try simp only [sc0, arm64_norm]); (try rw [hsp0]); exact Entails.of_eq (by sep_ac_rfl))
    (fun _ => by dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]; exact r1a_false_entails)
    (fun _ _ => Entails.refl _)
    (fun _ => by dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]; exact r1a_false_entails) ?_
  intro s1 hb1 hcs1 _ hfiles1
  dsimp only [withStack, sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
  rw [sepConj_assoc, sepConj_assoc]
  apply r1a_sepWPp_pure_pre; intro hvm1; apply r1a_sepWPp_pure_pre; intro htr1
  rw [← A.pool_transport lim st sc0 s1 hvm1]
  have hsc0_sp : sc0.sp = runFsp s0 := by simp only [sc0, arm64_norm, hsp0]
  rw [hsc0_sp]
  have hx19_1 : s1.readReg64 (.gpr 19#5) = g.stores := by simpa only [sc0, arm64_norm, hx19] using hcs1.1
  have hx20_1 : s1.readReg64 (.gpr 20#5) = g.res := by simpa only [sc0, arm64_norm, hx20] using hcs1.2.1
  have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [sc0, arm64_norm, hx21] using hcs1.2.2.1
  have hx23_1 : s1.readReg64 (.gpr 23#5) = -1#64 := by simpa only [sc0, arm64_norm, hx23] using hcs1.2.2.2.2.1
  have hx24_1 : s1.readReg64 (.gpr 24#5) = w.w4 := by simpa only [sc0, arm64_norm, hx24] using hcs1.2.2.2.2.2.1
  have hx26_1 : s1.readReg64 (.gpr 26#5) = pathPtr := by simpa only [sc0, arm64_norm, hx26] using hcs1.2.2.2.2.2.2.2.1
  have htr_01 : s0.trace <+: s1.trace := by simpa only [htr1, sc0, arm64_norm] using htr
  have hhans1 := r1a_hist_ans_step hhans (by simpa only [sc0, arm64_norm] using htr1) (by simpa only [sc0, arm64_norm] using hfiles1 htr1)
  clear hpc0 hrun0 hsp0 hinv_s hcs1 htr1 hfiles1 hvm1 hpool_0 hsc0_sp
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run; have hsp1 := hb1.sp
  change s1.pc = (blkPl_579).base + 2172#64 at hpc1
  apply sepWPp_seq_lscro (mid := lsρ lsRustAllocSymCli) hb1.inv
  try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustAllocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun1])
  intro hinv_a; apply r1a_bind_sepWPp_state; intro sa
  have hpool_1a : A.pool lim st s1 = A.pool lim st sa :=
    r1a_pool_congr_vm A lim st (by simp only [sa, arm64_norm]) (by simp only [sa, arm64_norm])
      (by simp only [sa, arm64_norm]) (by simp only [sa, arm64_norm]) (fun _ => by simp only [sa, arm64_norm])
  refine r1a_call_run (x := (22, 1, st)) (F := rem ∗ restMem) (retOff := 0x888)
    (hh.fs (runProgPlaced H) 579) (allocNoOomExtern_lscro_of_cli hh.alloc)
    (by simp only [sa, lsRustAllocSymCli, arm64_norm]) (by simp only [sa, arm64_norm, hrun1])
    hinv_a (by simp only [sa, arm64_norm, hsp1]) (by simp only [sa, arm64_norm, hb1.fp])
    (by simp only [sa, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs])
    hbase.spAligned (by simp only [sa, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    hpanic
    (by dsimp only [rustAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
          LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack, rustCliAllocNoOomSpecWithStack,
          LibsignalBinary.Heap.rustCliAllocNoOomSpec]
        have hsa_sp0 : sa.sp = runFsp s0 := by simp only [sa, arm64_norm, hsp1]
        have hsa_lr : sa.readReg64 .lr = (blkPl_579).base + 0x888#64 := by
          simp only [sa, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        have hpure : (sa.readReg64 .x0).toNat = 22 ∧ (sa.readReg64 .x1).toNat = 1 ∧
            RustLayoutOk 22 1 ∧ FitsEvents M lim st (rustAllocEvents 22 1) ∧
            LsRetAddr624 (sa.readReg64 .lr) :=
          ⟨by simp only [sa, arm64_norm], by simp only [sa, arm64_norm],
            ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩, hfits22,
            hsa_lr ▸ lsRetAddr624_blockPlacement_base_add 579 0x888#64 (by decide) (by decide)⟩
        rw [hpool_1a, hsa_sp0]
        refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
          (sepConj_mono_left (entails_pure_intro_left hpure (Entails.refl _))))
    (fun _ => by dsimp only [rustAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]; exact r1a_false_entails)
    (fun _ _ => Entails.refl _)
    (fun _ => by dsimp only [rustAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]; exact r1a_false_entails) ?_
  intro s2 hb2 hcs2 _ hfiles2
  dsimp only [rustAllocNoOomExternSpecWithStack, LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  apply r1a_sepWPp_pure_pre; rintro ⟨htr2, hbuf0, _⟩
  have hsa_sp : sa.sp = runFsp s0 := by simp only [sa, arm64_norm, hsp1]
  rw [hsa_sp]
  have hx19_2 : s2.readReg64 (.gpr 19#5) = g.stores := by simpa only [sa, arm64_norm, hx19_1] using hcs2.1
  have hx20_2 : s2.readReg64 (.gpr 20#5) = g.res := by simpa only [sa, arm64_norm, hx20_1] using hcs2.2.1
  have hx21_2 : s2.readReg64 (.gpr 21#5) = meG.name.cap := by simpa only [sa, arm64_norm, hx21_1] using hcs2.2.2.1
  have hx23_2 : s2.readReg64 (.gpr 23#5) = -1#64 := by simpa only [sa, arm64_norm, hx23_1] using hcs2.2.2.2.2.1
  have hx24_2 : s2.readReg64 (.gpr 24#5) = w.w4 := by simpa only [sa, arm64_norm, hx24_1] using hcs2.2.2.2.2.2.1
  have hx26_2 : s2.readReg64 (.gpr 26#5) = pathPtr := by simpa only [sa, arm64_norm, hx26_1] using hcs2.2.2.2.2.2.2.2.1
  have htr_02 : s0.trace <+: s2.trace := by simpa only [htr2, sa, arm64_norm] using htr_01
  have hhans2 := r1a_hist_ans_step hhans1 (by simpa only [sa, arm64_norm] using htr2) (by simpa only [sa, arm64_norm] using hfiles2 htr2)
  clear hpc1 hrun1 hsp1 hinv_a hcs2 htr2 hfiles2 hpool_1a hsa_sp
  set buf := s2.readReg64 .x0
  let st_a := M.stepEvents (rustAllocEvents 22 1) st
  have hbuf_be : (buf == 0#64) = false := beq_false_of_ne hbuf0
  have hbuf22 : memRegion buf 22 = (∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64,
      (buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) := by
    have h1 : memRegion buf 22 = memRegion buf 8 ∗ (memRegion (buf + 8#64) 8 ∗ memRegion (buf + 16#64) 6) := by
      rw [show (22 : Nat) = 8 + 14 from rfl, ProofLib.memRegion_split buf 8 14 (by decide),
          show (14 : Nat) = 8 + 6 from rfl, ProofLib.memRegion_split (buf + 8#64) 8 6 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [h1, ProofLib.memRegion_eight buf, sepExists_sepConj_left]; congr 1; funext b0
    rw [ProofLib.memRegion_eight (buf + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  rw [hbuf22]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro b0; apply r1a_sepWPp_exists_pre; intro b1 R hm2 hL2
  have hm2_ro := r1a_rodata_unreadable_intro hb2.inv hm2
  let ptrUnr := lsρ r1a_unreadSym
  refine (?_ : SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
    ((ptrUnr ↦ᵣ utf8 "file could not be read") ∗
      ((A.live buf 22 1 ∗ (((buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) ∗
        A.pool lim st_a s2 ∗ stackAt (runFsp s0) extHookStack)) ∗ (rem ∗ restMem)))
    Q Qp (runOom s0)) R (Satisfies.of_eq hm2_ro (by sep_ac_rfl)) hL2
  clear R hm2 hm2_ro hL2
  have hpc2 := hb2.pc; have := hb2.spAligned_cur; have hrun2 := hb2.run; have hsp2 := hb2.sp
  change s2.pc = (blkPl_579).base + 2184#64 at hpc2
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x8a0) hb2.inv; try dsimp only [runProgPlaced, lsProg_579]
  (wp_step; conv => arg 3; simp (config := { zeta := false }) only [show s2.readReg64 (Reg.gpr 0#5) = buf from rfl, hbuf_be, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
  (iterate 2 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  have hunr_len : (utf8 "file could not be read").length = 22 := r1a_utf8_unreadable_len
  apply SepWP.step_ldrSimd128 (by simp only [arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]; rfl) (by simp only [arm64_norm, hrun2]) (by wp_norm_lhs) rfl (by show _ = (ptrUnr, none); simp only [ptrUnr, lsρ, lsmpl, r1a_unreadSym, evalAddrMode, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) rfl (SepLoad64.of_pointsToBytesRO rfl (off := 0) (by rw [hunr_len]; decide) (by simp)) (SepLoad64.of_pointsToBytesRO rfl (off := 8) (by rw [hunr_len]; decide) rfl) rfl
  simp (config := { zeta := false }) only [applyWriteback, State.pc_setPC, State.setPC_setPC, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  apply SepWP.step_ldur64 (by simp only [arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]; rfl) (by simp only [arm64_norm, hrun2]) (by wp_norm_lhs) rfl (by show _ = (ptrUnr + 14#64, none); simp only [ptrUnr, lsρ, lsmpl, r1a_unreadSym, evalAddrMode, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (SepLoad64.of_pointsToBytesRO rfl (off := 14) (by rw [hunr_len]) rfl) rfl
  simp (config := { zeta := false }) only [applyWriteback, State.pc_setPC, State.setPC_setPC, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun2])
  intro hinv2b; apply r1a_bind_sepWPp_state; intro s2b
  have hvm2b : VmPreserved s2 s2b := by simp only [s2b, wp_norm, arm64_norm]
  have hpc2b : s2b.pc = (blkPl_579).base + 2208#64 := by simp only [s2b, hpc2, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hrun2b : s2b.status = .Running := by simp only [s2b, arm64_norm, hrun2]
  have hal2b : (s2b.sp &&& 15#64 == 0#64) = true := by simp only [s2b, arm64_norm]; exact hb2.spAligned_cur
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x8b0) hinv2b; try dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    have hbuf_rw : s2.readReg64 (Reg.gpr 0#5) = buf := rfl
    rw [← hbuf_rw]; symm at hbuf_rw; wp_simp_pre only [sepConj_assoc]
    (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hbuf_rw; rw [hbuf_rw]
    refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, s2b, buf, hbuf_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun2, hrun2b]) ⟨by simp only [wp_norm, arm64_norm], fun hvm23 hinv3 => ?_⟩
    apply r1a_bind_sepWPp_state; intro s3
    have hpool_23 : A.pool lim st_a s2 = A.pool lim st_a s3 := (A.pool_of_vmPreserved (hvm2b.trans hvm23)).symm
    have hb3 : InRunPlaced r1a_CodeOk s0 s3 0x8b0 :=
      ⟨by simp only [runPcPlaced_eq, arm64_norm, s3, s2b, buf, hbuf_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
       by simp only [arm64_norm, s3, s2b, hrun2], by simp only [arm64_norm, s3, s2b, hsp2],
       by simp only [arm64_norm, s3, s2b, hb2.fp], hinv3,
       by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s3, s2b, hb2.vregs],
       hbase.spAligned⟩
    have hx0_3 : s3.readReg64 .x0 = buf := by simp only [arm64_norm, s3, s2b, buf]
    have hx12_3 : s3.readReg64 (.gpr 12#5) = speWord 1 := by simp only [arm64_norm, s3, s2b]; decide
    have hx19_3 : s3.readReg64 (.gpr 19#5) = g.stores := by simp only [arm64_norm, s3, s2b, hx19_2]
    have hx20_3 : s3.readReg64 (.gpr 20#5) = g.res := by simp only [arm64_norm, s3, s2b, hx20_2]
    have hx21_3 : s3.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [arm64_norm, s3, s2b, hx21_2]
    have hx22_3 : s3.readReg64 (.gpr 22#5) = 22#64 := by simp only [arm64_norm, s3, s2b]
    have hx23_3 : s3.readReg64 (.gpr 23#5) = -1#64 := by simp only [arm64_norm, s3, s2b, hx23_2]
    have hx24_3 : s3.readReg64 (.gpr 24#5) = w.w4 := by simp only [arm64_norm, s3, s2b, hx24_2]
    have hx25_3 : s3.readReg64 (.gpr 25#5) = 22#64 := by simp only [arm64_norm, s3, s2b]
    have hx26_3 : s3.readReg64 (.gpr 26#5) = pathPtr := by simp only [arm64_norm, s3, s2b, hx26_2]
    have hx27_3 : s3.readReg64 (.gpr 27#5) = buf := by simp only [arm64_norm, s3, s2b, buf]
    have htr_03 : s0.trace <+: s3.trace := by simpa only [arm64_norm, s3, s2b] using htr_02
    have hhans3 := r1a_hist_ans_step (s2 := s3) hhans2 (by simp only [arm64_norm, s3, s2b]) (by simp only [arm64_norm, s3, s2b])
    have hstk_back : rem ∗ stackAt (runFsp s0) extHookStack = stackAt (runFsp s0) sub :=
      (r1a_stackAt_split (runFsp s0) hext hsub64).symm
    refine r1a_sepWPp_weaken_pre (?_ : _ ⊢ (∃∗ b2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ b2)) ∗
        A.live buf 22 1 ∗ stackAt (runFsp s0) sub ∗ A.pool lim st_a s3 ∗ restMem ∗ anyHeap) ?_
    · rw [hpool_23]
      refine Entails.trans (Entails.of_eq (show _ =
        ((buf ↦₆₄ _) ∗ ((buf + 8#64) ↦₆₄ _) ∗ memRegion (buf + 16#64) 6) ∗ A.live buf 22 1 ∗
          (rem ∗ stackAt (runFsp s0) extHookStack) ∗ A.pool lim st_a s3 ∗ restMem ∗
          (_ ↦ᵣ utf8 "file could not be read") by sep_ac_rfl)) ?_
      rw [hstk_back]
      exact sepConj_mono (r1a_buf22_reassoc buf _ _)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))))
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro b2
    have hafter_free : ∀ (st4 : M.σ) (s4 : State), FreeRejK A lim st4 H g s0 resStack Q Qp →
        InRunPlaced r1a_CodeOk s0 s4 0x6f4 → s4.readReg64 (.gpr 12#5) = speWord 1 →
        s4.readReg64 (.gpr 19#5) = g.stores → s4.readReg64 (.gpr 20#5) = g.res →
        s4.readReg64 (.gpr 21#5) = meG.name.cap → s4.readReg64 (.gpr 22#5) = 22#64 →
        s4.readReg64 (.gpr 23#5) = -1#64 → s4.readReg64 (.gpr 24#5) = w.w4 →
        s4.readReg64 (.gpr 25#5) = 22#64 → s4.readReg64 (.gpr 27#5) = buf →
        s0.trace <+: s4.trace → (RunHistOk g.i s0 s4 ∧ g.a = some none) →
        SepWPp (runProgPlaced H) (s0.readReg64 .lr) s4
          (memRegion buf 22 ∗ A.live buf 22 1 ∗ runLocals (runFsp s0) csErr ∗
            addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
            memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ stackAt (runFsp s0) sub ∗
            A.pool lim st4 s4 ∗ (F_heap ∗ anyHeap)) Q Qp (runOom s0) := by
      intro st4 s4 hrej4 hb4 hx12_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx27_4 htr_04 hhans4
      let csPre := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr)]
      let csMid := [(0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
        (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1),
        (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      have hdrop1750 : runLocals (runFsp s0) csErr ⊢
          runLocals (runFsp s0) (csPre ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csMid) :=
        r1a_locals_drop_mid (runFsp s0) (csPre ++ (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8) :: csMid)
          0x1750 8 _ [] (pointsTo64_entails_memRegion _ _)
      refine r1a_sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hdrop1750))) ?_
      rw [r1a_locals_focus (runFsp s0) csPre 0x1c0 8 (memRegion (runFsp s0 + 0x1c0#64) 8) csMid,
          ProofLib.memRegion_eight (runFsp s0 + 0x1c0#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply r1a_sepWPp_exists_pre; intro c1c0
      have hpc4 := hb4.pc; have := hb4.spAligned_cur; have hrun4 := hb4.run; have hsp4 := hb4.sp
      change s4.pc = (blkPl_579).base + 1780#64 at hpc4
      apply sepWPp_seq_lscro (mid := runPcPlaced 0x8c0) hb4.inv; try dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        rw [← hsp4]; symm at hsp4; wp_simp_pre only [sepConj_assoc]
        (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hsp4
        refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx23_4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun4]) ⟨by simp only [wp_norm, arm64_norm], fun hvm45 hinv5 => ?_⟩
        apply r1a_bind_sepWPp_state; intro s5; (try simp only [arm64_norm, hx24_4]); (try rw [hsp4])
        have hb5 : InRunPlaced r1a_CodeOk s0 s5 0x8c0 :=
          ⟨by simp only [runPcPlaced_eq, arm64_norm, s5, hx23_4, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [arm64_norm, s5, hrun4], by simp only [arm64_norm, s5, hsp4],
           by simp only [arm64_norm, s5, hb4.fp], hinv5,
           by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s5, hb4.vregs],
           hbase.spAligned⟩
        let cs5 := [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr),
          (0x1c0, 8, (runFsp s0 + 0x1c0#64) ↦₆₄ w.w4), (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5),
          (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)]
        have hfold1c0 : ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) ∗ r1a_localsCtx (runFsp s0) 0 csPre 0x1c0 8 csMid =
            memRegion (runFsp s0 + 0x4d0#64) 48 ∗ r1a_localsCtx (runFsp s0) 0 cs5 0x4d0 48 [] := by
          rw [← r1a_locals_focus (runFsp s0) csPre 0x1c0 8 ((runFsp s0 + 0x1c0#64) ↦₆₄ w.w4) csMid]
          exact r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (memRegion (runFsp s0 + 0x4d0#64) 48) []
        rw [r1a_group_mid2, hfold1c0]
        refine r1a_sepWPp_weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (r1a_memRegion48_words (runFsp s0 + 0x4d0#64)))))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply r1a_sepWPp_exists_pre; intro e0; apply r1a_sepWPp_exists_pre; intro e1; apply r1a_sepWPp_exists_pre; intro e2
        apply r1a_sepWPp_exists_pre; intro e3; apply r1a_sepWPp_exists_pre; intro e4; apply r1a_sepWPp_exists_pre; intro e5
        have hpc5 := hb5.pc; have := hb5.spAligned_cur; have hrun5 := hb5.run; change s5.pc = (blkPl_579).base + 2240#64 at hpc5
        apply sepWPp_seq_lscro (mid := runPcPlaced 0x2bf0) hb5.inv; try dsimp only [runProgPlaced, lsProg_579]
        (iterate 11 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun5])
        intro hinv6; apply r1a_bind_sepWPp_state; intro s6
        have hvm56 : VmPreserved s5 s6 := by simp only [s6, wp_norm, arm64_norm]
        have hb6 : InRunPlaced r1a_CodeOk s0 s6 0x2bf0 :=
          ⟨by simp only [runPcPlaced_eq, arm64_norm, s6, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [arm64_norm, s6, hrun5], by simp only [arm64_norm, s6, hb5.sp],
           by simp only [arm64_norm, s6, hb5.fp], hinv6,
           by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s6, hb5.vregs],
           hbase.spAligned⟩
        have hpc6 := hb6.pc; have := hb6.spAligned_cur; have hrun6 := hb6.run; have hsp6 := hb6.sp; rw [runPcPlaced_eq] at hpc6
        apply sepWPp_seq_lscro (mid := runPcPlaced 0x2c30) hb6.inv; try dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          rw [← hsp6]; symm at hsp6; wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          (iterate 16 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
          symm at hsp6
          refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun6]) ⟨by simp only [wp_norm, arm64_norm], fun hvm67 hinv7 => ?_⟩
          apply r1a_bind_sepWPp_state; intro s7; (try simp only [arm64_norm]); (try rw [hsp6]); rw [r1a_group_mid6]
          have hpool_47 : A.pool lim st4 s4 = A.pool lim st4 s7 :=
            (A.pool_of_vmPreserved ((hvm45.trans hvm56).trans hvm67)).symm
          refine r1a_sepWPp_weaken_pre ?_
            (r1a_tail_after_spe (peerV := peerV) (dir := dir) (meG := meG) (w := w)
              (k := .withString 1 (by decide)) (F_heap := F_heap ∗ anyHeap)
              hh hdrop hbnd hpanic hrej4
              ⟨by simp only [runPcPlaced_eq, arm64_norm, s7, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
               by simp only [arm64_norm, s7, hrun6], by simp only [arm64_norm, s7, hsp6],
               by simp only [arm64_norm, s7, hb6.fp], hinv7,
               by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s7, hb6.vregs],
               hbase.spAligned⟩
              (by simp only [arm64_norm, s7, hsp6])
              (by simp only [arm64_norm, s7, s6, s5, hx19_4])
              (by simp only [arm64_norm, s7, s6, s5, hx20_4])
              (by simp only [arm64_norm, s7, s6, s5, hx21_4])
              (by simpa only [arm64_norm, s7, s6, s5] using htr_04)
              (r1a_hist_ans_step hhans4 (by simp only [arm64_norm, s7, s6, s5]) (by simp only [arm64_norm, s7, s6, s5])))
          have h4words : ∀ {v0 v1 v2 v3 w4 w5 : BitVec 64}, v0 = speWord 1 → v1 = 22#64 → v2 = buf → v3 = 22#64 →
              ((runFsp s0 + 0x4d0#64) ↦₆₄ v0) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ v1) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ v2) ∗
                ((runFsp s0 + 0x4e8#64) ↦₆₄ v3) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ w4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ w5) =
              ((runFsp s0 + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((runFsp s0 + 0x4d8#64) ↦₆₄ 22#64) ∗ ((runFsp s0 + 0x4e0#64) ↦₆₄ buf) ∗
                ((runFsp s0 + 0x4e8#64) ↦₆₄ 22#64) ∗ ((runFsp s0 + 0x4f0#64) ↦₆₄ w4) ∗ ((runFsp s0 + 0x4f8#64) ↦₆₄ w5) := by
            rintro _ _ _ _ _ _ rfl rfl rfl rfl; rfl
          rw [h4words (by simp only [arm64_norm, s7, s6, s5, hx12_4])
              (by simp only [arm64_norm, s7, s6, s5, hx22_4, hx25_4])
              (by simp only [arm64_norm, s7, s6, s5, hx27_4]; bv_bits)
              (by simp only [arm64_norm, s7, s6, s5, hx22_4, hx25_4])]
          have hspe_in := r1a_vec22_withString_intro A.repAlloc (runFsp s0 + 0x4d0#64) buf
            (s6.readReg64 (.gpr 11#5)) (s6.readReg64 (.gpr 13#5)) hbuf0
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hspe_in
          have hfoc' := (r1a_locals_focus (runFsp s0) cs5 0x4d0 48 (speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) (.withString 1 (by decide))) []).symm
          change _ ⊢ runLocals (runFsp s0) (cs5 ++ [(0x4d0, 48, speOwnedAt A.repAlloc (runFsp s0 + 0x4d0#64) (.withString 1 (by decide)))]) ∗ _
          rw [← hfoc', hpool_47]
          refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hspe_in))
          exact Entails.of_eq (by sep_ac_rfl)
        )
      )
    have hf1750 := r1a_locals_focus (runFsp s0)
      [(0x1b8, 8, (runFsp s0 + 0x1b8#64) ↦₆₄ meG.name.ptr), (0x1c0, 8, memRegion (runFsp s0 + 0x1c0#64) 8),
       (0x1c8, 8, (runFsp s0 + 0x1c8#64) ↦₆₄ w.w5), (0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0),
       (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1), (0x4d0, 48, memRegion (runFsp s0 + 0x4d0#64) 48)]
      0x1750 8 ((runFsp s0 + 0x1750#64) ↦₆₄ pathCap) []
    simp only [List.cons_append, List.nil_append] at hf1750
    have hpc3 := hb3.pc; have := hb3.spAligned_cur; have hrun3 := hb3.run; have hsp3 := hb3.sp
    change s3.pc = (blkPl_579).base + 2224#64 at hpc3
    by_cases hp0 : pathCap = 0#64
    · apply sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hb3.inv
      dsimp only [restMem, csErr]; rw [hf1750]; try dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        rw [← hsp3, ← hx0_3]; symm at hsp3 hx0_3; wp_simp_pre only [sepConj_assoc]
        (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hsp3 hx0_3
        refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun3]) ⟨by simp only [wp_norm, arm64_norm], fun hvm34 hinv4 => ?_⟩
        apply r1a_bind_sepWPp_state; intro s4p
        (try simp only [arm64_norm, hx0_3]); (try rw [hsp3]); rw [r1a_group_8b0]
        have hpool_34 : A.pool lim st_a s3 = A.pool lim st_a s4p := (A.pool_of_vmPreserved hvm34).symm
        refine r1a_sepWPp_weaken_pre ?_
          (hafter_free st_a s4p hrej_a
            ⟨by simp only [s4p, runPcPlaced_eq, arm64_norm, hp0, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
             by simp only [s4p, arm64_norm, hrun3], by simp only [s4p, arm64_norm, hsp3],
             by simp only [s4p, arm64_norm, hb3.fp], hinv4,
             by simp only [s4p, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb3.vregs],
             hbase.spAligned⟩
            (by simp only [s4p, arm64_norm, hx12_3]) (by simp only [s4p, arm64_norm, hx19_3])
            (by simp only [s4p, arm64_norm, hx20_3]) (by simp only [s4p, arm64_norm, hx21_3])
            (by simp only [s4p, arm64_norm, hx22_3]) (by simp only [s4p, arm64_norm, hx23_3])
            (by simp only [s4p, arm64_norm, hx24_3]) (by simp only [s4p, arm64_norm, hx25_3])
            (by simp only [s4p, arm64_norm, hx27_3]) (by simpa only [s4p, arm64_norm] using htr_03)
            (r1a_hist_ans_step hhans3 (by simp only [s4p, arm64_norm]) (by simp only [s4p, arm64_norm])))
        rw [← hf1750, hpool_34]
        refine Entails.trans (sepConj_mono (r1a_buf22_merge buf _)
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_left (r1a_ownedBytes_zero hp0)))))))) ?_
        rw [emp_sepConj]; exact Entails.of_eq (by sep_ac_rfl)
      )
    · have hp_be : (pathCap == 0#64) = false := beq_false_of_ne hp0
      apply sepWPp_seq_lscro (mid := runPcPlaced 0x6e0) hb3.inv
      dsimp only [restMem, csErr]; rw [hf1750]; try dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        rw [← hsp3, ← hx0_3]; symm at hsp3 hx0_3; wp_simp_pre only [sepConj_assoc]
        (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hsp3 hx0_3
        refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun3]) ⟨by simp only [wp_norm, arm64_norm], fun hvm3p hinv4 => ?_⟩
        apply r1a_bind_sepWPp_state; intro s3p
        (try simp only [arm64_norm, hx0_3]); (try rw [hsp3]); rw [r1a_group_8b0, ← hf1750]
        have hpool_3p : A.pool lim st_a s3 = A.pool lim st_a s3p := (A.pool_of_vmPreserved hvm3p).symm
        rw [hpool_3p]
        refine r1a_sepWPp_weaken_pre (sepConj_mono_left (r1a_buf22_merge buf _)) ?_
        refine r1a_sepWPp_weaken_pre (Entails.of_eq (show
          memRegion buf 22 ∗ (A.live buf 22 1 ∗ stackAt (runFsp s0) sub ∗ A.pool lim st_a s3p ∗
            (runLocals (runFsp s0) csErr ∗ ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
              addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
              memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ F_heap) ∗ anyHeap) =
          ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
            stackAt (runFsp s0) sub ∗ A.pool lim st_a s3p ∗
            (memRegion buf 22 ∗ A.live buf 22 1 ∗ runLocals (runFsp s0) csErr ∗
              addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
              memRegion g.call 56 ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ (F_heap ∗ anyHeap)) by sep_ac_rfl)) ?_
        apply r1a_free_path_6e0 hh hbnd hpanic hp0
          ⟨by simp only [s3p, runPcPlaced_eq, arm64_norm, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
           by simp only [s3p, arm64_norm, hrun3], by simp only [s3p, arm64_norm, hsp3],
           by simp only [s3p, arm64_norm, hb3.fp], hinv4,
           by simp only [s3p, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb3.vregs],
           hbase.spAligned⟩
          (by simp only [s3p, arm64_norm]) (by simp only [s3p, arm64_norm, hx26_3])
        intro sm4 hb4 r12 r19 r20 r21 r22 r23 r24 r25 r27 _ htrm4 hfilesm4
        refine r1a_sepWPp_weaken_pre ?_
          (hafter_free _ sm4 (hrej_a.dealloc pathCap.toNat 1) hb4
            (by simpa only [s3p, arm64_norm, hx12_3] using r12)
            (by simpa only [s3p, arm64_norm, hx19_3] using r19)
            (by simpa only [s3p, arm64_norm, hx20_3] using r20)
            (by simpa only [s3p, arm64_norm, hx21_3] using r21)
            (by simpa only [s3p, arm64_norm, hx22_3] using r22)
            (by simpa only [s3p, arm64_norm, hx23_3] using r23)
            (by simpa only [s3p, arm64_norm, hx24_3] using r24)
            (by simpa only [s3p, arm64_norm, hx25_3] using r25)
            (by simpa only [s3p, arm64_norm, hx27_3] using r27)
            (by simpa only [htrm4, s3p, arm64_norm] using htr_03)
            (r1a_hist_ans_step hhans3 (by simpa only [s3p, arm64_norm] using htrm4)
              (by simpa only [s3p, arm64_norm] using hfilesm4)))
        exact Entails.of_eq (by sep_ac_rfl)
      )
  )

set_option maxHeartbeats 800000 in
theorem r1a_after_decode [LibsignalPlacement] {M : AllocCostModel}
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
          s0.trace <+: s2.trace → s2.fs.files = runFiles g.i →
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
        intro s2 evs_fi hfi hb2 r19 r20 r21 r22 r28 tr2 fs2 out2
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
            ⟨ikB, r1a_ikOk_sem hik hdec⟩, hikWords, tr2, fs2, out2⟩)
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
            (by simpa only [s2z, arm64_norm] using hfs_1) (by simpa only [s2z, arm64_norm] using hout_1))
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
          (by simpa only [htrm, sc, arm64_norm] using hout_1)
    )

theorem r1a_none_sem [LibsignalPlacement] {S : RunSem} {g : RunCall} {s0 s : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hd : AtDispatchPlaced r1a_CodeOk g .none s0 s) :
    g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hnone⟩
  rw [he.rel.2.2.2.2.2]; unfold runAns; simp [he.parse, hget, hnone]

theorem r1a_init_none_branch [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir : Bytes} {w : CallW} {s0 s_disp s : State} {resStack : Nat}
    {F_heap : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g .none s0 s_disp)
    (hpanic : PanicK g s0 Qp) (hrej : FreeRejK A lim st H g s0 resStack Q Qp)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x654)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = CryptoVerification.LibsignalTripleRatchetRepr.noneCap)
    (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (htr : s0.trace <+: s.trace) (hfs : s.fs.files = runFiles g.i)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runLocals (runFsp s0) [] ∗
        ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ F_heap)
      Q Qp (runOom s0) := by
  have hcarve := r1a_locals_carve_region (runFsp s0) [] 0x2a0 32 []
  have hf2a0 := r1a_locals_focus (runFsp s0) [] 0x2a0 32 (memRegion (runFsp s0 + 0x2a0#64) 32) []
  have h32 : memRegion (runFsp s0 + 0x2a0#64) 32 =
      (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((runFsp s0 + 0x2a0#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ q1) ∗
          ((runFsp s0 + 0x2b0#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ q3)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x2a0#64)
  simp only [List.nil_append] at hcarve hf2a0 ⊢; rw [hcarve, hf2a0, h32]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro q0; apply r1a_sepWPp_exists_pre; intro q1
  apply r1a_sepWPp_exists_pre; intro q2; apply r1a_sepWPp_exists_pre; intro q3
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 := hbase.sp
  change s.pc = (blkPl_579).base + 1620#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x860) hbase.inv
  dsimp only [runProgPlaced, lsProg_579, CryptoVerification.LibsignalTripleRatchetRepr.noneCap] at hpc0 hx21 ⊢
  by_vm_open (
    rw [← hsp0, ← hx25]; symm at hsp0 hx25; wp_simp_pre only [sepConj_assoc]
    (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0 hx25
    refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]) ⟨by simp only [wp_norm, arm64_norm], fun hvm01 hinv1 => ?_⟩
    apply r1a_bind_sepWPp_state; intro s1; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx25]); (try rw [hsp0]); rw [r1a_group4_7]
    have hpool_01 : A.pool lim st s = A.pool lim st s1 := (A.pool_of_vmPreserved hvm01).symm
    refine r1a_sepWPp_weaken_pre ?_
      (r1a_me_none (peerV := peerV) (dir := dir) (w := w) (F_heap := F_heap)
        hh hbnd hpanic hrej
        ⟨by simp only [runPcPlaced_eq, arm64_norm, s1, hx21, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [arm64_norm, s1, hrun0], by simp only [arm64_norm, s1, hsp0],
         by simp only [arm64_norm, s1, hbase.fp], hinv1,
         by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [arm64_norm, s1, hx19]) (by simp only [arm64_norm, s1, hx20])
        (by simp only [arm64_norm, s1]) (by simp only [arm64_norm, s1])
        (by simpa only [arm64_norm, s1] using htr)
        ⟨⟨by simpa only [arm64_norm, s1] using hfs, by simpa only [arm64_norm, s1] using hout⟩, r1a_none_sem he hd⟩)
    have hpack2a0 : (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗
        ((runFsp s0 + 0x2b0#64) ↦₆₄ w.w2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ w.w3)) ∗
        r1a_localsCtx (runFsp s0) 0 [] 0x2a0 32 [] ⊢
        runLocals (runFsp s0) [(0x2a0, 8, (runFsp s0 + 0x2a0#64) ↦₆₄ w.w0), (0x2a8, 8, (runFsp s0 + 0x2a8#64) ↦₆₄ w.w1)] := by
      have ht16 : ((runFsp s0 + 0x2b0#64) ↦₆₄ w.w2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ w.w3) ⊢
          memRegion (runFsp s0 + 0x2b0#64) 16 := by
        have hs := (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 8 8 (by decide)).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs; rw [← hs]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ht16))) ?_
      dsimp only [r1a_localsCtx, runLocals, runLocalsFrom, runLocalBytes]
      have hm := (ProofLib.memRegion_split (runFsp s0 + 0x2b0#64) 16 10032 (by decide)).symm
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.add_zero, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at hm ⊢
      refine Entails.of_eq ?_
      trans (((runFsp s0 + 0x2a0#64) ↦₆₄ w.w0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ w.w1) ∗
        (memRegion (runFsp s0 + 0x2b0#64) 16 ∗ memRegion (runFsp s0 + 0x2c0#64) 10032) ∗
        memRegion (runFsp s0) 672)
      · sep_ac_rfl
      · rw [hm]; sep_ac_rfl
    rw [hpool_01]
    refine Entails.trans (sepConj_mono hpack2a0 (sepConj_mono_left (r1a_call7_to_memRegion56 g.call w))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
