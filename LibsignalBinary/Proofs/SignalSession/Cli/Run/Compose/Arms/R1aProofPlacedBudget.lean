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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Arm `R1a` Proof

Defines the Arm `R1a` allocation-event envelope `Init1Env` and proves `run_hop_init1_placed_ok` and
`run_hop_init1_of_slots_placed_ok` on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
  (r1a_after_decode r1a_init_none_branch r1a_pool_congr_vm r1a_read_err)
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

/-! ## Allocation-Event Envelopes (`Init1AfterReadEnv`, `Init1Env`) -/

/-- Post-`read_file` allocation-event envelope of Arm `R1a`: allocates the 22-byte `"file could not be read"` buffer plus `FreeOnlyEvs` on `Err`, and performs only `FreeOnlyEvs` deallocations on `Ok`. -/
def Init1AfterReadEnv (r : Except Unit (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match r with
  | .error () => ∃ evs_f, FreeOnlyEvs evs_f ∧ evs = rustAllocEvents 22 1 ++ evs_f
  | .ok _ => FreeOnlyEvs evs

/-- Full Arm `R1a` allocation-event envelope (`R+0x214 → R+0x74c` or `RejectKPlacedEnv`). -/
def Init1Env (cEnvs : RunCalleesEnvs) (g : RunCall) (me : MeAtDispatch)
    (_peerV : AddrV) (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match me with
  | .none => FreeOnlyEvs evs
  | .some _ _ =>
    let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
    PathEnv dir (utf8 "identity-key") evs ∨
    (∃ evs_p evs_r,
      PathEnv dir (utf8 "identity-key") evs_p ∧
      cEnvs.readFile (runFiles g.i) pathBs evs_r ∧
      evs = evs_p ++ evs_r) ∨
    (∃ evs_p evs_r evs_t,
      PathEnv dir (utf8 "identity-key") evs_p ∧
      cEnvs.readFile (runFiles g.i) pathBs evs_r ∧
      Init1AfterReadEnv (cliIo.rd (runFiles g.i) pathBs) evs_t ∧
      evs = evs_p ++ evs_r ++ evs_t)


/-! ## `read_file` Post-Call Dispatch -/

set_option maxHeartbeats 800000 in
private theorem r1a_after_read [LibsignalPlacement] {M : AllocCostModel}
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
        s0.trace <+: s2.trace → s2.fs.files = runFiles g.i →
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
      intro evs_fp hfp s2 hb2 r19 r20 r21 r22 r23 r24 r25 r27 r28 tr2 fs2 out2
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
          (identityKeyDecode_vm_placed_ok (callerProg := runProgPlaced H) (i := 579) A)
          (by simp only [arm64_norm, sd, r23, hik_ne, bne, Bool.not_false, Bool.not_true, ↓reduceIte]; rfl)
          (by simp only [arm64_norm, sd, hrun2]) hinv_d (by simp only [arm64_norm, sd, hsp2])
          (by simp only [arm64_norm, sd, hb2.fp])
          (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, sd, hb2.vregs])
          hbase.spAligned (by simp only [runPcPlaced_eq, arm64_norm, sd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          hpanic
          (by dsimp only [withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]
              rw [← sepConj_assoc, hfold4d0, r1a_ownedBytes_expose A.repAlloc ikCap ikPtr ikB, hstk60, hpool_2d]
              have hlen_ik : (BitVec.ofNat 64 ikB.length).toNat = ikB.length := Nat.mod_eq_of_lt (by omega)
              refine Entails.trans (Entails.of_eq (by
                (try simp only [arm64_norm, sd]); (try rw [hsp2])
                dsimp only [lsLogOff, lsLogFilterAddr, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff, lsρ]
                sep_ac_rfl))
                (sepConj_mono_left (Entails.pure_right
                  ⟨by simp only [arm64_norm, sd, r27], by simp only [arm64_norm, sd, r22, hlen_ik],
                   by simp only [arm64_norm, sd, hsp2]⟩ (Entails.refl _))))
          (fun _ => by dsimp only [withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails)
          (fun _ _ => by dsimp only [withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact Entails.refl _)
          (fun _ => by dsimp only [withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]; exact r1a_false_entails) ?_
        intro s3 hb3 hcs3 _ hfiles3
        dsimp only [withVmPreserved, identityKeyDecodeRawSpec, CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]
        rw [sepConj_assoc, sepConj_assoc]
        apply r1a_sepWPp_pure_pre; intro hvm3; apply r1a_sepWPp_pure_pre; intro htr3
        rw [← A.pool_transport lim st_p sd s3 hvm3]
        refine r1a_sepWPp_weaken_pre ?_
          (r1a_after_decode hh hdrop hbnd he hd hcall hpanic
            (hrej_ok ikB evs_fp rfl hfp)
            (fun s1' evs_fi d1 hfi hat1 => hnext_ok ikB evs_fp evs_fi s1' d1 rfl hfp hfi hat1)
            hb3
            (by simpa only [arm64_norm, sd, r19] using hcs3.1)
            (by simpa only [arm64_norm, sd, r20] using hcs3.2.1)
            (by simpa only [arm64_norm, sd, r21] using hcs3.2.2.1)
            (by simpa only [arm64_norm, sd, r25] using hcs3.2.2.2.2.2.2.1)
            (by simpa only [arm64_norm, sd, r27] using hcs3.2.2.2.2.2.2.2.2.1)
            (by simpa only [arm64_norm, sd, r28] using hcs3.2.2.2.2.2.2.2.2.2.1)
            hik hw6 hw2 (by simpa only [htr3, arm64_norm, sd] using tr2)
            ((hfiles3 htr3).trans (by simpa only [arm64_norm, sd] using fs2))
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
          (by simpa only [s2z, arm64_norm] using hfs_ok) (by simpa only [s2z, arm64_norm] using hout_ok))
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
      apply r1a_free_path_6e0 hh hbnd hpanic hp0
        ⟨by simp only [s2p, runPcPlaced_eq, arm64_norm, hik_ne, hp_be, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
         by simp only [s2p, arm64_norm, hrun0], by simp only [s2p, arm64_norm, hsp0],
         by simp only [s2p, arm64_norm, hbase.fp], hinv1,
         by simp only [s2p, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs],
         hbase.spAligned⟩
        (by simp only [s2p, arm64_norm]) (by simp only [s2p, arm64_norm, hx26])
      intro sm4 hb4 _ r19 r20 r21 r22 r23 r24 r25 r27 r28 htrm4 hfilesm4
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
          (by simpa only [hfilesm4, s2p, arm64_norm] using hfs_ok)
          (by simpa only [htrm4, s2p, arm64_norm] using hout_ok))

/-! ## `some` Entry Path and `run_hop_init1_placed_ok` -/

private theorem r1a_inRun [LibsignalPlacement] {s0 s : State} {off : Nat}
    (hpc : s.pc = runPcPlaced off) (hrun : s.status = .Running) (hsp : s.sp = runFsp s0)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64) (hinv : r1a_CodeOk s.mem)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) (hal : s0.spAligned = true) :
    InRunPlaced r1a_CodeOk s0 s off :=
  ⟨hpc, hrun, hsp, hfp, hinv, hv, hal⟩

private theorem r1a_sepWPp_rodata_idkey [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp}
    (hinv : r1a_CodeOk s.mem)
    (h : SepWPp prog ret s ((lsρ r1a_idKeySym ↦ᵣ utf8 "identity-key") ∗ P) Q Qp O) :
    SepWPp prog ret s P Q Qp O :=
  fun R hm hL => h R (by simpa only [sepConj_assoc] using r1a_rodata_idkey_intro hinv hm) hL

private theorem r1a_sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {D P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp}
    (h : SepWPp prog ret s P Q Qp O) : SepWPp prog ret s (D ∗ P) Q Qp O :=
  fun R hm hL => h R (Satisfies.drop_mid (by simpa only [sepConj_comm D P, sepConj_assoc] using hm)) hL

private theorem r1a_sepWPp_of_false_oom {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp (fun _ => ⌜False⌝)) : SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => match h R hm hL with
    | ⟨sf, hs, Or.inl h1⟩ => ⟨sf, hs, Or.inl h1⟩
    | ⟨sf, hs, Or.inr (Or.inl h2)⟩ => ⟨sf, hs, Or.inr (Or.inl h2)⟩
    | ⟨_, _, Or.inr (Or.inr ⟨_, hmo⟩)⟩ => (not_satisfies_false_sepConj hmo).elim

set_option maxHeartbeats 800000 in
private theorem r1a_some_after_668 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW}
    {s0 s_disp s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp)
    (hcall : g.c = .init peerV dir)
    (hfits : FitsEnv M lim st (Init1Env cEnvs g (.some meV meG) peerV dir))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1a_CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init1Env cEnvs g (.some meV meG) peerV dir evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp)
    (hnext : ∀ (s1 : State) (evs : List AllocEvent) (d1 : Init1Data),
      AtInit1Placed r1a_CodeOk g d1 s0 s1 →
      Init1Env cEnvs g (.some meV meG) peerV dir evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack) Q Qp (fun _ => ⌜False⌝))
    (hpathStk : pathNeed ≤ resStack - runFrame)
    (hreadStk : B.readFile ≤ resStack - runFrame)
    (hikStk : 0x60 ≤ resStack - runFrame)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x668)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx22 : s.readReg64 (.gpr 22#5) = w.w5)
    (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
    (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
    (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
    (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length)
    (hw3 : w.w3.setWidth 8 = peerV.device) (htr : s0.trace <+: s.trace)
    (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
          ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3)) ∗
        r1a_localsCtx fsp 0 [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] 0x2a0 32 [] ∗
        ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) Q Qp (runOom s0) := by
  intro fsp
  have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnd.sub64
  obtain ⟨hpOk, hdLen, hnLen, hpLen⟩ := r1a_idKey_path_bounds he hcall
  let peerG := r1a_peerGhostOf peerV w
  have hclose_peer : ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3) ⊢
      addrUpperAt (fsp + 0x2b0#64) peerG := by
    have h2 : w.w2 = BitVec.ofNat 64 peerG.name.bytes.length := hw2
    rw [h2]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_addrUpperAt_close (fsp + 0x2b0#64) peerG w.w3 hw3
  refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right hclose_peer))) ?_
  refine r1a_sepWPp_weaken_pre
    (sepConj_mono_right (sepConj_mono_left (by dsimp only [r1a_localsCtx]; exact sepConj_mono_right (sepConj_mono_left (r1a_addrUpperAt_open (fsp + 0x1d0#64) meG))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply r1a_sepWPp_exists_pre; intro meW1
  have hp_me (X Y P Z W V : SepProp) : X ∗ (Y ∗ (P ∗ Z) ∗ W) ∗ V = P ∗ (X ∗ (Y ∗ Z ∗ W) ∗ V) := by sep_ac_rfl
  rw [hp_me]; apply r1a_sepWPp_pure_left; intro hmeW1
  have hctx_open :
      memRegion (fsp + 0#64) (0x1d0 - 0) ∗
        (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d0#64 + 8#64) ↦₆₄ meW1)) ∗
        (memRegion (fsp + BitVec.ofNat 64 (0x1d0 + 16)) (0x2a0 - (0x1d0 + 16)) ∗ runLocalsFrom fsp (0x2a0 + 32) []) =
      memRegion (fsp + 0x1b0#64) 4 ∗ memRegion (fsp + 0x1b8#64) 8 ∗ memRegion (fsp + 0x1c0#64) 8 ∗
        memRegion (fsp + 0x1c8#64) 8 ∗ memRegion (fsp + 0x260#64) 8 ∗ memRegion (fsp + 0x268#64) 8 ∗
        (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
          memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
          memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) := by
    have a1 := ProofLib.memRegion_split fsp 0x1b0 32 (by decide)
    have a2 := ProofLib.memRegion_split (fsp + 0x1b0#64) 4 28 (by decide)
    have a3 := ProofLib.memRegion_split (fsp + 0x1b4#64) 4 24 (by decide)
    have a4 := ProofLib.memRegion_split (fsp + 0x1b8#64) 8 16 (by decide)
    have a5 := ProofLib.memRegion_split (fsp + 0x1c0#64) 8 8 (by decide)
    have b1 := ProofLib.memRegion_split (fsp + 0x1e0#64) 0x80 64 (by decide)
    have b2 := ProofLib.memRegion_split (fsp + 0x260#64) 8 56 (by decide)
    have b3 := ProofLib.memRegion_split (fsp + 0x268#64) 8 48 (by decide)
    dsimp only [r1a_localsCtx, runLocalsFrom]
    simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at a1 a2 a3 a4 a5 b1 b2 b3 ⊢
    rw [a1, a2, a3, a4, a5, b1, b2, b3]; sep_ac_rfl
  rw [hctx_open, ProofLib.memRegion_four (fsp + 0x1b0#64), ProofLib.memRegion_eight (fsp + 0x1b8#64),
      ProofLib.memRegion_eight (fsp + 0x1c0#64), ProofLib.memRegion_eight (fsp + 0x1c8#64),
      ProofLib.memRegion_eight (fsp + 0x260#64), ProofLib.memRegion_eight (fsp + 0x268#64)]
  dsimp only [addrUpperAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply r1a_sepWPp_exists_pre; intro u0; apply r1a_sepWPp_exists_pre; intro u1
  apply r1a_sepWPp_exists_pre; intro u2; apply r1a_sepWPp_exists_pre; intro u3
  apply r1a_sepWPp_exists_pre; intro u4; apply r1a_sepWPp_exists_pre; intro u5
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 : s.sp = fsp := hbase.sp
  change s.pc = (blkPl_579).base + 1640#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x67c) hbase.inv; (try dsimp only [runProgPlaced, lsProg_579])
  by_vm_open (
    rw [← hsp0, ← hx25]; symm at hsp0 hx25; wp_simp_pre only [sepConj_assoc]
    (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0 hx25
    refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]) ⟨by simp only [wp_norm, arm64_norm], fun hvmsa1 hinva1 => ?_⟩
    apply r1a_bind_sepWPp_state; intro sa1; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx22, hx25, hx28]); (try rw [hsp0])
    have hpca1 : sa1.pc = (blkPl_579).base + 1660#64 := by simp only [sa1, hpc0, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
    have hruna1 : sa1.status = .Running := by simp only [sa1, arm64_norm, hrun0]
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x684) hinva1; (try dsimp only [runProgPlaced, lsProg_579])
    wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0, hruna1])
    intro hinva2; apply r1a_bind_sepWPp_state; intro sa2
    have hpool_a2 : A.pool lim st sa1 = A.pool lim st sa2 :=
      r1a_pool_congr_vm A lim st (by simp only [sa2, sa1, arm64_norm]) (by simp only [sa2, sa1, arm64_norm])
        (by simp only [sa2, sa1, arm64_norm]) (by simp only [sa2, sa1, arm64_norm]) (fun _ => by simp only [sa2, sa1, arm64_norm])
    have hpca2 : sa2.pc = (blkPl_579).base + 1668#64 := by simp only [sa2, sa1, hpca1, hpc0, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
    have hruna2 : sa2.status = .Running := by simp only [sa2, sa1, arm64_norm, hrun0, hruna1]
    have hala2 : (sa2.sp &&& 15#64 == 0#64) = true := by simp only [sa2, sa1, arm64_norm]; exact hbase.spAligned_cur
    apply sepWPp_seq_lscro (mid := (blkPl_596).base) hinva2; (try dsimp only [runProgPlaced, lsProg_579])
    by_vm_open (
    rw [← hsp0, ← hx25]; symm at hsp0 hx25
    wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    (iterate 8 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
    symm at hsp0 hx25
    refine SepWP.done (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm, hrun0, hruna1, hruna2]) ⟨by simp only [wp_norm, arm64_norm], fun hvmsa hinva => ?_⟩
    apply r1a_bind_sepWPp_state; intro sa; (try simp only [sa2, sa1, arm64_norm, r1a_low64, r1a_high64, hx22, hx25, hx28]); (try rw [hsp0])
    have hpool_sa : A.pool lim st s = A.pool lim st sa :=
      (A.pool_of_vmPreserved hvmsa1).symm.trans (hpool_a2.trans (A.pool_of_vmPreserved hvmsa).symm)
    rw [hpool_sa]
    let cs7 :=
      [(0x1b0, 4, (fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
       (0x1b8, 8, (fsp + 0x1b8#64) ↦₆₄ meG.name.ptr),
       (0x1c0, 8, memRegion (fsp + 0x1c0#64) 8),
       (0x1c8, 8, (fsp + 0x1c8#64) ↦₆₄ w.w5),
       (0x260, 16, addrUpperAt (fsp + 0x260#64) meG),
       (0x2a0, 32, protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64)),
       (0x4d0, 48, memRegion (fsp + 0x4d0#64) 48)]
    have hpack_locals :
        (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
          (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗
          (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x1c0#64) ↦₆₄ u3) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗
            (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
            (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
              memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
              memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ⊢
        memRegion (fsp + 0x1750#64) 24 ∗ r1a_localsCtx fsp 0 cs7 0x1750 24 [] := by
      have hme260 := r1a_addrUpperAt_close (fsp + 0x260#64) meG meW1 hmeW1
      have hd1d0 : ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ⊢
          memRegion (fsp + 0x1d0#64) 16 := by
        have s := (ProofLib.memRegion_split (fsp + 0x1d0#64) 8 8 (by decide)).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
      have hpeer2a0 : ((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
          addrUpperAt (fsp + 0x2b0#64) peerG ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ⊢
          protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) := by
        rw [protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]
        dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
      dsimp only [addrUpperAt] at hpeer2a0; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer2a0 hme260 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
          (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
            ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7) ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name) ∗
        (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
        (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1)) ∗
        ((fsp + 0x1c0#64) ↦₆₄ u3) ∗
        (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
          ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗
          memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗
          memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hpeer2a0 (sepConj_mono hme260 (sepConj_mono hd1d0 (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))) ?_
      have m1 := (ProofLib.memRegion_split (fsp + 0x1d0#64) 16 0x80 (by decide)).symm
      dsimp only [cs7, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at m1 ⊢
      rw [show protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ addrUpperAt (fsp + 0x260#64) meG ∗
          memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1c0#64) 8 ∗
          (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 432 ∗ memRegion (fsp + 0x1b4#64) 4 ∗
            memRegion (fsp + 0x1e0#64) 128 ∗ memRegion (fsp + 0x270#64) 48 ∗ memRegion (fsp + 0x2c0#64) 10032) =
        memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗
          ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗
          ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ (memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1e0#64) 128) ∗
          addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
          protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 10032 by sep_ac_rfl, m1]
      have splitTail : memRegion (fsp + 0x2c0#64) 10032 =
          memRegion (fsp + 0x2c0#64) 528 ∗ memRegion (fsp + 0x4d0#64) 48 ∗
            memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1750#64) 24 ∗ memRegion (fsp + 0x1768#64) 4744 := by
        have t1 := ProofLib.memRegion_split (fsp + 0x2c0#64) 528 9504 (by decide)
        have t2 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 9456 (by decide)
        have t3 := ProofLib.memRegion_split (fsp + 0x500#64) 4688 4768 (by decide)
        have t4 := ProofLib.memRegion_split (fsp + 0x1750#64) 24 4744 (by decide)
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at t1 t2 t3 t4; rw [t1, t2, t3, t4]
      rw [splitTail]; exact Entails.of_eq (by sep_ac_rfl)
    let ptrIdk := lsρ r1a_idKeySym
    let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
    have hdir_exp : ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir = (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir := by
      rw [hw6]; exact r1a_ownedBytes_expose A.repAlloc w.w4 w.w5 dir
    refine r1a_sepWPp_weaken_pre
      (Entails.trans (Entails.of_eq (by
        rw [hdir_exp]
        exact show _ =
          ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
            (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x2b8#64) ↦₈ peerG.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗
            (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x1c0#64) ↦₆₄ _) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗
              (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
              (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
                memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
                memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name) ∗
          ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
            ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
            ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
          ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st sa ∗
            r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
            memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
            (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
            tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
            runSaved s0) by sep_ac_rfl))
        (sepConj_mono hpack_locals (sepConj_mono_left (r1a_call7_to_memRegion56 g.call w)))) ?_
    apply r1a_sepWPp_rodata_idkey hinva
    have hsa_sp : sa.sp = fsp := by simp only [sa, sa2, sa1, arm64_norm, hsp0]
    have hsa_tr : s0.trace <+: sa.trace := by simpa only [sa, sa2, sa1, arm64_norm] using htr
    have hfits_path : FitsEnv M lim st (PathEnv dir (utf8 "identity-key")) :=
      fun evs hp => hfits evs (Or.inl hp)
    have hpath_ok := path_placed_ok (callerProg := runProgPlaced H) (i := 579) hh hpathStk
    unfold pathSpecPlaced at hpath_ok
    apply r1a_call_run (hh.fs (runProgPlaced H) 579) hpath_ok
      (x := (({ dirA := w.w5, dir := dir, dirRo := false, nameA := ptrIdk, name := utf8 "identity-key", nameRo := true, ret := fsp + 0x1750#64 } : PathGhost), st))
      (F := r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗
        r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
        memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
        tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
        runSaved s0)
      (retOff := 0x6a4)
      (by simp only [sa, sa2, sa1, arm64_norm]; rfl) (by simp only [sa, sa2, sa1, arm64_norm, hrun0]) hinva hsa_sp
      (by simp only [sa, sa2, sa1, arm64_norm, hbase.fp])
      (by simp only [sa, sa2, sa1, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
      hbase.spAligned (by simp only [sa, sa2, sa1, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      hpanic
      (by dsimp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt]
          simp only [Bool.false_eq_true, ↓reduceIte]; rw [hsa_sp]
          have hpure : sa.readReg64 .x0 = fsp + 0x1750#64 ∧ sa.readReg64 .x1 = w.w5 ∧
              (sa.readReg64 .x2).toNat = dir.length ∧ sa.readReg64 .x3 = ptrIdk ∧
              (sa.readReg64 .x4).toNat = (utf8 "identity-key").length ∧
              dir.length < 2 ^ 32 ∧ (utf8 "identity-key").length < 2 ^ 32 ∧
              FitsEnv M lim st (PathEnv dir (utf8 "identity-key")) :=
            ⟨by simp only [sa, sa2, sa1, arm64_norm, hsp0, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
             by simp only [sa, sa2, sa1, arm64_norm, hx22],
             by simp only [sa, sa2, sa1, arm64_norm, hw6]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by omega),
             by simp only [sa, sa2, sa1, ptrIdk, lsρ, lsmpl, r1a_idKeySym, arm64_norm],
             by rw [r1a_utf8_idkey_len]; simp only [sa, sa2, sa1, arm64_norm],
             hdLen, hnLen, hfits_path⟩
          refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
            (sepConj_mono_left (entails_pure_intro_left hpure (Entails.refl _))))
      (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
    intro sb hbb hcsb _ hfilesb
    dsimp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply r1a_sepWPp_exists_pre; intro evs_p
    apply r1a_sepWPp_pure_left; rintro ⟨htr_ba, hp_evs⟩
    let st_p := M.stepEvents evs_p st
    refine r1a_sepWPp_weaken_pre
      (Entails.of_eq (show _ =
        (ptrIdk ↦ᵣ utf8 "identity-key") ∗ vecU8 A.repAlloc (fsp + 0x1750#64) pathBs ∗
          ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st_p sb ∗
            (r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗
              r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
              memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              runSaved s0)) by dsimp only [pathBs, st_p]; rw [hsa_sp]; sep_ac_rfl)) ?_
    apply r1a_sepWPp_drop_left
    refine r1a_sepWPp_weaken_pre (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 0x1750#64) pathBs)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply r1a_sepWPp_exists_pre; intro pathCap; apply r1a_sepWPp_exists_pre; intro pathPtr
    have hsb_fs : sb.fs.files = runFiles g.i := (hfilesb htr_ba).trans (by simpa only [sa, sa2, sa1, arm64_norm] using hfs)
    have hsb_out : ProcessOutcome.traceStreamBytes .stdout sb.trace = [] := by
      rw [htr_ba]; simpa only [sa, sa2, sa1, arm64_norm] using hout
    have hsb_tr : s0.trace <+: sb.trace := by rw [htr_ba]; exact hsa_tr
    have hx27_b : sb.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
      (by simpa only [sa, sa2, sa1, arm64_norm] using hcsb.2.2.2.2.2.2.2.2.1 : sb.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
    have hpcb := hbb.pc; have := hbb.spAligned_cur; have hrunb := hbb.run; have hspb : sb.sp = fsp := hbb.sp
    change sb.pc = (blkPl_579).base + 1700#64 at hpcb
    apply sepWPp_seq_lscro (mid := lsρ lsReadFileSym) hbb.inv; (try dsimp only [runProgPlaced, lsProg_579])
    by_vm_open (
      rw [← hspb]; symm at hspb; wp_simp_pre only [sepConj_assoc]
      (iterate 6 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hspb
      refine SepWP.done (by simp only [lsReadFileSym, arm64_norm]) (by simp only [arm64_norm, hrunb]) ⟨by simp only [wp_norm, arm64_norm], fun hvmbc hinvc => ?_⟩
      apply r1a_bind_sepWPp_state; intro sc
      (try simp only [arm64_norm]); (try rw [hspb])
      have hpool_bc : A.pool lim st_p sb = A.pool lim st_p sc := (A.pool_of_vmPreserved hvmbc).symm
      rw [hpool_bc]
      let cs8 := cs7 ++ [(0x1750, 8, (fsp + 0x1750#64) ↦₆₄ pathCap)]
      have hctx_read :
          (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗
            r1a_localsCtx fsp 0 cs7 0x1750 24 [] ⊢
          memRegion (fsp + 0x23b0#64) 24 ∗ r1a_localsCtx fsp 0 cs8 0x23b0 24 [] := by
        have h16 : ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length) ⊢
            memRegion (fsp + 0x1758#64) 16 := by
          have s := (ProofLib.memRegion_split (fsp + 0x1758#64) 8 8 (by decide)).symm
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right h16)) ?_
        have s1 := (ProofLib.memRegion_split (fsp + 0x1758#64) 16 4744 (by decide)).symm
        have s2 := ProofLib.memRegion_split (fsp + 0x1758#64) 3160 1600 (by decide)
        have s3 := ProofLib.memRegion_split (fsp + 0x23b0#64) 24 1576 (by decide)
        simp only [cs8, cs7, List.append_assoc, List.cons_append, List.nil_append]
        dsimp only [r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]
        simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 ⊢
        rw [show (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ memRegion (fsp + 0x1758#64) 16) ∗
            (memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗
              memRegion (fsp + 0x1b4#64) 4 ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
              memRegion (fsp + 0x1c0#64) 8 ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗
              addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
              protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗
              memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1768#64) 4744) =
          (memRegion (fsp + 0x1758#64) 16 ∗ memRegion (fsp + 0x1768#64) 4744) ∗ memRegion fsp 432 ∗
            ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗
            ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗
            ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗
            addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗
            memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗
            ((fsp + 0x1750#64) ↦₆₄ pathCap) by sep_ac_rfl, s1, s2, s3]
        exact Entails.of_eq (by sep_ac_rfl)
      have hstk_sp := r1a_stackAt_split fsp hreadStk hsub64
      have hpath_exp := r1a_ownedBytes_expose A.repAlloc pathCap pathPtr pathBs
      have hdir_back : (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir = ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir :=
        hdir_exp.symm
      have hsc_sp : sc.sp = fsp := by simp only [sc, arm64_norm, hspb]
      have hsc_fs : sc.fs.files = runFiles g.i := by simpa only [sc, arm64_norm] using hsb_fs
      have hsc_tr : s0.trace <+: sc.trace := by simpa only [sc, arm64_norm] using hsb_tr
      have hfits_read : FitsEnv M lim st_p (cEnvs.readFile sc.fs.files pathBs) := fun evs_r hr =>
        ((fitsEvents_append M lim evs_p evs_r st).mp
          (hfits (evs_p ++ evs_r) (Or.inr (Or.inl ⟨evs_p, evs_r, hp_evs, hsc_fs ▸ hr, rfl⟩)))).2
      refine r1a_sepWPp_weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          ((((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗
            ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗
            r1a_localsCtx fsp 0 cs7 0x1750 24 []) ∗
            ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
            ((w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir) ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st_p sc ∗
            (memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0) by sep_ac_rfl))
          (by rw [hpath_exp, hdir_back, hstk_sp]; exact sepConj_mono_left hctx_read)) ?_
      apply r1a_call_run (hh.fs (runProgPlaced H) 579) (subroutine_ok_withLsCodeRoLoaded_of_plain hc.readFile)
        (x := (({ pathA := pathPtr, path := pathBs, ret := fsp + 0x23b0#64 } : ReadFileGhost), st_p))
        (F := r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A.repAlloc pathCap pathPtr pathBs ∗
          ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗
          memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0)
        (retOff := 0x6bc)
        (by simp only [sc, lsReadFileSym, arm64_norm]) (by simp only [sc, arm64_norm, hrunb]) hinvc hsc_sp
        (by simp only [sc, arm64_norm, hbb.fp])
        (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbb.vregs])
        hbase.spAligned (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        hpanic
        (by dsimp only [readFileSpecPlaced]; rw [hsc_sp]
            have hpure : sc.readReg64 .x0 = pathPtr ∧ (sc.readReg64 .x1).toNat = pathBs.length ∧
                sc.readReg64 .x8 = fsp + 0x23b0#64 ∧ pathBs.length < 2 ^ 32 ∧ cliWrOk pathBs ∧
                FitsEnv M lim st_p (cEnvs.readFile sc.fs.files pathBs) :=
              ⟨by simp only [sc, arm64_norm],
               by simp only [sc, arm64_norm]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by dsimp only [pathBs]; omega),
               by simp only [sc, arm64_norm]; rw [hspb], hpLen, hpOk, hfits_read⟩
            refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (sepConj_mono_left (entails_pure_intro_left hpure (Entails.refl _))))
        (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
      intro sd hbd hcsd _ hfilesd
      dsimp only [readFileSpecPlaced]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply r1a_sepWPp_exists_pre; intro evs_r
      apply r1a_sepWPp_exists_pre; intro r
      apply r1a_sepWPp_pure_left; intro hr_evs
      apply r1a_sepWPp_pure_left; intro hpost_r
      have hr_evs' : cEnvs.readFile (runFiles g.i) pathBs evs_r := hsc_fs ▸ hr_evs
      have hr_rd : r = cliIo.rd (runFiles g.i) pathBs := hsc_fs ▸ hpost_r.1
      obtain ⟨htr_d, herr_f, hok_f⟩ :=
        r1a_readFile_post_facts he hd hcall hsc_tr hsc_fs
          (by simpa only [sc, arm64_norm] using hsb_out) hfilesd (by simpa only [pathBs] using hpost_r)
      let st_r := M.stepEvents evs_r st_p
      have hremerge :
          ioVecAt A.repAlloc (fsp + 0x23b0#64) r ∗ (pathPtr ↦ₛ pathBs) ∗ stackAt sc.sp B.readFile ∗
            A.pool lim st_r sd ∗
            (r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A.repAlloc pathCap pathPtr pathBs ∗
              ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗
              memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0) =
          runLocals fsp (cs8 ++ [(0x23b0, 24, ioVecAt A.repAlloc (fsp + 0x23b0#64) r)]) ∗
            ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
            addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st_r sd := by
        rw [hsc_sp, r1a_locals_focus fsp cs8 0x23b0 24 (ioVecAt A.repAlloc (fsp + 0x23b0#64) r) [], hpath_exp, hstk_sp]
        sep_ac_rfl
      rw [hremerge]
      exact r1a_after_read hh hdrop hbnd he hd hcall
        (fun hr_err => by
          have herr_rd : cliIo.rd (runFiles g.i) pathBs = .error () := hr_rd.symm.trans hr_err
          have hev22 : Init1Env cEnvs g (.some meV meG) peerV dir ((evs_p ++ evs_r) ++ rustAllocEvents 22 1) :=
            Or.inr (Or.inr ⟨evs_p, evs_r, rustAllocEvents 22 1, hp_evs, hr_evs',
              by dsimp only [Init1AfterReadEnv, pathBs] at herr_rd ⊢; rw [herr_rd]; exact ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩, rfl⟩)
          have hf22 := ((fitsEvents_append M lim (evs_p ++ evs_r) (rustAllocEvents 22 1) st).mp (hfits _ hev22)).2
          rwa [M.stepEvents_append] at hf22)
        hpanic
        (fun hr_err s2 evs_f hf hat => by
          have herr_rd : cliIo.rd (runFiles g.i) pathBs = .error () := hr_rd.symm.trans hr_err
          have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (rustAllocEvents 22 1 ++ evs_f)) :=
            Or.inr (Or.inr ⟨evs_p, evs_r, rustAllocEvents 22 1 ++ evs_f, hp_evs, hr_evs',
              by dsimp only [Init1AfterReadEnv, pathBs] at herr_rd ⊢; rw [herr_rd]; exact ⟨evs_f, hf, rfl⟩, rfl⟩)
          have hst : M.stepEvents evs_f (M.stepEvents (rustAllocEvents 22 1) st_r) = M.stepEvents (evs_p ++ evs_r ++ (rustAllocEvents 22 1 ++ evs_f)) st := by
            dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
          exact hrej s2 _ StoresGhost.opened .postDispatch hat ⟨_, hev, hst⟩)
        (fun ikB evs_fp hr_ok hfp s2 evs_fd hfd hat => by
          have hok_rd : cliIo.rd (runFiles g.i) pathBs = .ok ikB := hr_rd.symm.trans hr_ok
          have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (evs_fp ++ evs_fd)) :=
            Or.inr (Or.inr ⟨evs_p, evs_r, evs_fp ++ evs_fd, hp_evs, hr_evs',
              by dsimp only [Init1AfterReadEnv, pathBs] at hok_rd ⊢; rw [hok_rd]; exact r1a_freeOnly_append hfp hfd, rfl⟩)
          have hst : M.stepEvents evs_fd (M.stepEvents evs_fp st_r) = M.stepEvents (evs_p ++ evs_r ++ (evs_fp ++ evs_fd)) st := by
            dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
          exact hrej s2 _ StoresGhost.opened .postDispatch hat ⟨_, hev, hst⟩)
        (fun ikB evs_fp evs_fi s1' d1 hr_ok hfp hfi hat1 => by
          have hok_rd : cliIo.rd (runFiles g.i) pathBs = .ok ikB := hr_rd.symm.trans hr_ok
          have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) :=
            Or.inr (Or.inr ⟨evs_p, evs_r, evs_fp ++ evs_fi, hp_evs, hr_evs',
              by dsimp only [Init1AfterReadEnv, pathBs] at hok_rd ⊢; rw [hok_rd]; exact r1a_freeOnly_append hfp hfi, rfl⟩)
          have hm := r1a_sepWPp_of_false_oom (oom := runOom s0) (hnext s1' (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) d1 hat1 hev)
          have hst : M.stepEvents evs_fi (M.stepEvents evs_fp st_r) = M.stepEvents (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) st := by
            dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
          rwa [hst])
        hikStk hbd
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx19] using hcsd.1.trans hcsb.1)
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx20] using hcsd.2.1.trans hcsb.2.1)
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx21] using hcsd.2.2.1.trans hcsb.2.2.1)
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx22] using hcsd.2.2.2.1.trans hcsb.2.2.2.1)
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx24] using hcsd.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.1)
        (by simpa only [sc, arm64_norm] using hcsd.2.2.2.2.2.2.2.1)
        (by simpa only [sc, sa, sa2, sa1, arm64_norm, hw6] using hcsd.2.2.2.2.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.2.2.2.2.1)
        hw6 hw2 htr_d herr_f hok_f
      )
    )
  )

theorem run_hop_init1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopInit1Placed (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (Init1Env cEnvs)
      H B S needs resStack := by
  intro g st s0 s me peerV dir Q Qp hh hc hdrop hres hres64 he hd hcall hfits hpanic hrej hnext
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres hres64
  obtain ⟨_, _, _, _, _, hreadStk, hpathStk, _, _, _, _, hikStk, _⟩ :=
    runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) hres hres64
  have htag : s.readReg64 (.gpr 8#5) = 1#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hpc0 := hd.base.pc; have := hd.base.spAligned_cur; have hrun0 := hd.base.run
  change s.pc = (blkPl_579).base + 532#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x654) hd.base.inv; try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
  intro hinv1; apply r1a_bind_sepWPp_state; intro s1
  have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x654 := r1a_inRun
    (by simp only [runPcPlaced_eq, arm64_norm, s1, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, s1, hrun0]) (by simp only [arm64_norm, s1, hd.base.sp]) (by simp only [arm64_norm, s1, hd.base.fp]) hinv1
    (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hd.base.vregs]) hd.base.spAligned
  have htr1 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using hd.trace
  have hfs1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hd.fs
  have hout1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [] := by simpa only [arm64_norm, s1] using hd.stdout
  have hpool_01 : A.pool lim st s = A.pool lim st s1 := r1a_pool_congr_vm A lim st
    (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (fun _ => by simp only [s1, arm64_norm])
  have hdm : dispatchMeHeap (A.atState lim st s) me = dispatchMeHeap A.repAlloc me := by cases me <;> rfl
  dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced]
  rw [callAt_atState A lim st s g.call g.c, storesAt_opened_atState A lim st s g.stores, hdm, RustCliAllocBudget.atState_pool, hpool_01, congrArg (callAt A.repAlloc g.call) hcall]
  dsimp only [callAt, callHeap, addrWords]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply r1a_sepWPp_exists_pre; intro w
  have hp_w (A0 W0 W1 W2 W3 W4 W5 W6 N0 P' R' : SepProp) :
      A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ P' ∗ R' = P' ∗ A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ R' := by sep_ac_rfl
  rw [hp_w]; apply r1a_sepWPp_pure_left; intro hw3
  rcases me with _ | ⟨meV, meG⟩
  · dsimp only [dispatchMeHeap, dispatchCells]
    exact r1a_sepWPp_weaken_pre (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; sep_ac_rfl))
      (r1a_init_none_branch (peerV := peerV) (dir := dir) (w := w)
        (F_heap := coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff)
        hh hbnd he hd hpanic
        (fun s2 evs hf hat => hrej s2 (M.stepEvents evs st) StoresGhost.opened .postDispatch hat ⟨evs, hf, rfl⟩)
        hb1 (by simp only [s1, arm64_norm, hd.x19]) (by simp only [s1, arm64_norm, hd.x20])
        (by simp only [s1, arm64_norm, hd.meRegs]) (by simp only [s1, arm64_norm, hd.x25]) htr1 hfs1 hout1)
  · dsimp only [dispatchMeHeap, dispatchCells]; rcases hd.meRegs with ⟨hx21_0, hx28_0, _, _, _⟩
    have hmep := ownedBytes_pure A.repAlloc meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes
    have hpeerp := ownedBytes_pure A.repAlloc w.w0 w.w1 w.w2 peerV.name
    have hdirp := ownedBytes_pure A.repAlloc w.w4 w.w5 w.w6 dir
    refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
      addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        (memRegion g.res runResSize ∗
          ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
            ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
            ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    rw [r1a_addrNameHeap_eq_owned meG, hmep, hpeerp, hdirp, ← r1a_addrNameHeap_eq_owned meG]
    have hp3 {P1 P2 P3 : Prop} (A1 A2 A3 R0 : SepProp) :
        (⌜P1⌝ ∗ A1) ∗ (⌜P2⌝ ∗ A2) ∗ (⌜P3⌝ ∗ A3) ∗ R0 = ⌜P1⌝ ∗ ⌜P2⌝ ∗ ⌜P3⌝ ∗ (A1 ∗ A2 ∗ A3 ∗ R0) := by sep_ac_rfl
    rw [hp3]; apply r1a_sepWPp_pure_left; rintro ⟨_, _, hme_lt, _⟩
    apply r1a_sepWPp_pure_left; rintro ⟨hw2, _, _, _⟩
    apply r1a_sepWPp_pure_left; rintro ⟨hw6, _, _, _⟩
    refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
      runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
        ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 by sep_ac_rfl)) ?_
    have hcmn : (meG.name.cap + 1#64 == 0#64) = false := beq_add_one_zero_false_of_lt hme_lt
    have hcarve := r1a_locals_carve_region (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 []
    have hf2a0 := r1a_locals_focus (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 (memRegion (runFsp s0 + 0x2a0#64) 32) []
    have h32 : memRegion (runFsp s0 + 0x2a0#64) 32 =
        (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
          ((runFsp s0 + 0x2a0#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ q1) ∗
            ((runFsp s0 + 0x2b0#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ q3)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x2a0#64)
    simp only [List.nil_append, List.append_nil] at hcarve hf2a0; rw [hcarve, hf2a0, h32]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro q0; apply r1a_sepWPp_exists_pre; intro q1
    apply r1a_sepWPp_exists_pre; intro q2; apply r1a_sepWPp_exists_pre; intro q3
    have hpc1 := hb1.pc; have hal0 : (s0.sp &&& 15#64 == 0#64) = true := hd.base.spAligned
    have hal1 : (s1.sp &&& 15#64 == 0#64) = true := hb1.spAligned_cur
    have hrun1 := hb1.run; have hsp1 := hb1.sp; change s1.pc = (blkPl_579).base + 1620#64 at hpc1
    have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [s1, arm64_norm, hx21_0]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = g.call := by simp only [s1, arm64_norm, hd.x25]
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x668) hb1.inv; (try dsimp only [runProgPlaced, lsProg_579])
    by_vm_open (
      rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]
      (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1
      refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]) ⟨by simp only [wp_norm, arm64_norm], fun hvm12 hinv2 => ?_⟩
      apply r1a_bind_sepWPp_state; intro s2
      (try simp only [arm64_norm, r1a_low64, r1a_high64, hx25_1]); (try rw [hsp1])
      have hpool_12 : A.pool lim st s1 = A.pool lim st s2 := (A.pool_of_vmPreserved hvm12).symm
      rw [hpool_12]
      exact r1a_sepWPp_weaken_pre (Entails.of_eq (by rw [hw2]; sep_ac_rfl))
        (r1a_some_after_668 (sEnvs := sEnvs) (needs := needs) (peerV := peerV) (dir := dir) (w := w)
          hh hc hdrop hbnd he hd hcall hfits hpanic hrej hnext hpathStk hreadStk hikStk
          (r1a_inRun
            (by simp only [runPcPlaced_eq, arm64_norm, s2, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
            (by simp only [arm64_norm, s2, hrun1]) (by simp only [arm64_norm, s2, hsp1])
            (by simp only [arm64_norm, s2, hb1.fp]) hinv2
            (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s2, hb1.vregs])
            hd.base.spAligned)
          (by simp only [arm64_norm, s2, s1, hd.x19]) (by simp only [arm64_norm, s2, s1, hd.x20])
          (by simp only [arm64_norm, s2, hx21_1]) (by simp only [arm64_norm, s2])
          (by simp only [arm64_norm, s2]) (by simp only [arm64_norm, s2, hx25_1])
          (by simp only [arm64_norm, s2, s1, hd.x27]) (by simp only [arm64_norm, s2, s1, hx28_0])
          hw6 hw2 hw3 (by simpa only [arm64_norm, s2] using htr1)
          (by simpa only [arm64_norm, s2] using hfs1) (by simpa only [arm64_norm, s2] using hout1))
    )


set_option maxHeartbeats 800000 in
theorem run_hop_init1_of_slots_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B slots =
      CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B (slotsOfPlaced A lim sEnvs S needs)) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget.RunHopInit1PlacedOf
      (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (Init1Env cEnvs) H B S slots resStack := by
  have h_some_after_668 {st : M.σ}
      {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW}
      {s0 s_disp s : State} {Q Qp : State → SepProp → Prop}
      (hh : RunHooksPlaced A lim H)
      (hc : RunCalleesPlaced A lim cEnvs H B slots)
      (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
      (hbnd : r1b_StackBounds B resStack)
      (he : AtRunEntryPlaced r1a_CodeOk S g s0)
      (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp)
      (hcall : g.c = .init peerV dir)
      (hfits : FitsEnv M lim st (Init1Env cEnvs g (.some meV meG) peerV dir))
      (hpanic : PanicK g s0 Qp)
      (hrej : RejectKPlacedEnv r1a_CodeOk H A lim
        (fun _ _ st' => ∃ evs, Init1Env cEnvs g (.some meV meG) peerV dir evs ∧ st' = M.stepEvents evs st)
        g s0 resStack Q Qp)
      (hnext : ∀ (s1 : State) (evs : List AllocEvent) (d1 : Init1Data),
        AtInit1Placed r1a_CodeOk g d1 s0 s1 →
        Init1Env cEnvs g (.some meV meG) peerV dir evs →
        SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
          (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack) Q Qp (fun _ => ⌜False⌝))
      (hpathStk : pathNeed ≤ resStack - runFrame)
      (hreadStk : B.readFile ≤ resStack - runFrame)
      (hikStk : 0x60 ≤ resStack - runFrame)
      (hbase : InRunPlaced r1a_CodeOk s0 s 0x668)
      (hx19 : s.readReg64 (.gpr 19#5) = g.stores) (hx20 : s.readReg64 (.gpr 20#5) = g.res)
      (hx21 : s.readReg64 (.gpr 21#5) = meG.name.cap) (hx22 : s.readReg64 (.gpr 22#5) = w.w5)
      (hx24 : s.readReg64 (.gpr 24#5) = w.w4) (hx25 : s.readReg64 (.gpr 25#5) = g.call)
      (hx27 : s.readReg64 (.gpr 27#5) = runFsp s0 + 0x1750#64)
      (hx28 : s.readReg64 (.gpr 28#5) = meG.name.ptr)
      (hw6 : w.w6 = BitVec.ofNat 64 dir.length) (hw2 : w.w2 = BitVec.ofNat 64 peerV.name.length)
      (hw3 : w.w3.setWidth 8 = peerV.device) (htr : s0.trace <+: s.trace)
      (hfs : s.fs.files = runFiles g.i) (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
        ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
            ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3)) ∗
          r1a_localsCtx fsp 0 [(0x1d0, 16, addrUpperAt (fsp + 0x1d0#64) meG)] 0x2a0 32 [] ∗
          ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
            ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
            ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
          addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
          ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st s) Q Qp (runOom s0) := by
    intro fsp
    have hsub64 : resStack - runFrame ≤ 2 ^ 64 := hbnd.sub64
    obtain ⟨hpOk, hdLen, hnLen, hpLen⟩ := r1a_idKey_path_bounds he hcall
    let peerG := r1a_peerGhostOf peerV w
    have hclose_peer : ((fsp + 0x2b0#64) ↦₆₄ w.w2) ∗ ((fsp + 0x2b8#64) ↦₆₄ w.w3) ⊢
        addrUpperAt (fsp + 0x2b0#64) peerG := by
      have h2 : w.w2 = BitVec.ofNat 64 peerG.name.bytes.length := hw2
      rw [h2]; simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_addrUpperAt_close (fsp + 0x2b0#64) peerG w.w3 hw3
    refine r1a_sepWPp_weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right hclose_peer))) ?_
    refine r1a_sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_left (by dsimp only [r1a_localsCtx]; exact sepConj_mono_right (sepConj_mono_left (r1a_addrUpperAt_open (fsp + 0x1d0#64) meG))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro meW1
    have hp_me (X Y P Z W V : SepProp) : X ∗ (Y ∗ (P ∗ Z) ∗ W) ∗ V = P ∗ (X ∗ (Y ∗ Z ∗ W) ∗ V) := by sep_ac_rfl
    rw [hp_me]; apply r1a_sepWPp_pure_left; intro hmeW1
    have hctx_open :
        memRegion (fsp + 0#64) (0x1d0 - 0) ∗
          (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d0#64 + 8#64) ↦₆₄ meW1)) ∗
          (memRegion (fsp + BitVec.ofNat 64 (0x1d0 + 16)) (0x2a0 - (0x1d0 + 16)) ∗ runLocalsFrom fsp (0x2a0 + 32) []) =
        memRegion (fsp + 0x1b0#64) 4 ∗ memRegion (fsp + 0x1b8#64) 8 ∗ memRegion (fsp + 0x1c0#64) 8 ∗
          memRegion (fsp + 0x1c8#64) 8 ∗ memRegion (fsp + 0x260#64) 8 ∗ memRegion (fsp + 0x268#64) 8 ∗
          (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
            memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
            memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) := by
      have a1 := ProofLib.memRegion_split fsp 0x1b0 32 (by decide)
      have a2 := ProofLib.memRegion_split (fsp + 0x1b0#64) 4 28 (by decide)
      have a3 := ProofLib.memRegion_split (fsp + 0x1b4#64) 4 24 (by decide)
      have a4 := ProofLib.memRegion_split (fsp + 0x1b8#64) 8 16 (by decide)
      have a5 := ProofLib.memRegion_split (fsp + 0x1c0#64) 8 8 (by decide)
      have b1 := ProofLib.memRegion_split (fsp + 0x1e0#64) 0x80 64 (by decide)
      have b2 := ProofLib.memRegion_split (fsp + 0x260#64) 8 56 (by decide)
      have b3 := ProofLib.memRegion_split (fsp + 0x268#64) 8 48 (by decide)
      dsimp only [r1a_localsCtx, runLocalsFrom]
      simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at a1 a2 a3 a4 a5 b1 b2 b3 ⊢
      rw [a1, a2, a3, a4, a5, b1, b2, b3]; sep_ac_rfl
    rw [hctx_open, ProofLib.memRegion_four (fsp + 0x1b0#64), ProofLib.memRegion_eight (fsp + 0x1b8#64),
        ProofLib.memRegion_eight (fsp + 0x1c0#64), ProofLib.memRegion_eight (fsp + 0x1c8#64),
        ProofLib.memRegion_eight (fsp + 0x260#64), ProofLib.memRegion_eight (fsp + 0x268#64)]
    dsimp only [addrUpperAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply r1a_sepWPp_exists_pre; intro u0; apply r1a_sepWPp_exists_pre; intro u1
    apply r1a_sepWPp_exists_pre; intro u2; apply r1a_sepWPp_exists_pre; intro u3
    apply r1a_sepWPp_exists_pre; intro u4; apply r1a_sepWPp_exists_pre; intro u5
    have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run; have hsp0 : s.sp = fsp := hbase.sp
    change s.pc = (blkPl_579).base + 1640#64 at hpc0
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x67c) hbase.inv; (try dsimp only [runProgPlaced, lsProg_579])
    by_vm_open (
      rw [← hsp0, ← hx25]; symm at hsp0 hx25; wp_simp_pre only [sepConj_assoc]
      (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0 hx25
      refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0]) ⟨by simp only [wp_norm, arm64_norm], fun hvmsa1 hinva1 => ?_⟩
      apply r1a_bind_sepWPp_state; intro sa1; (try simp only [arm64_norm, r1a_low64, r1a_high64, hx22, hx25, hx28]); (try rw [hsp0])
      have hpca1 : sa1.pc = (blkPl_579).base + 1660#64 := by simp only [sa1, hpc0, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
      have hruna1 : sa1.status = .Running := by simp only [sa1, arm64_norm, hrun0]
      apply sepWPp_seq_lscro (mid := runPcPlaced 0x684) hinva1; (try dsimp only [runProgPlaced, lsProg_579])
      wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
      apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0, hruna1])
      intro hinva2; apply r1a_bind_sepWPp_state; intro sa2
      have hpool_a2 : A.pool lim st sa1 = A.pool lim st sa2 :=
        r1a_pool_congr_vm A lim st (by simp only [sa2, sa1, arm64_norm]) (by simp only [sa2, sa1, arm64_norm])
          (by simp only [sa2, sa1, arm64_norm]) (by simp only [sa2, sa1, arm64_norm]) (fun _ => by simp only [sa2, sa1, arm64_norm])
      have hpca2 : sa2.pc = (blkPl_579).base + 1668#64 := by simp only [sa2, sa1, hpca1, hpc0, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
      have hruna2 : sa2.status = .Running := by simp only [sa2, sa1, arm64_norm, hrun0, hruna1]
      have hala2 : (sa2.sp &&& 15#64 == 0#64) = true := by simp only [sa2, sa1, arm64_norm]; exact hbase.spAligned_cur
      apply sepWPp_seq_lscro (mid := (blkPl_596).base) hinva2; (try dsimp only [runProgPlaced, lsProg_579])
      by_vm_open (
      rw [← hsp0, ← hx25]; symm at hsp0 hx25
      wp_simp_pre only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      (iterate 8 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp0 hx25
      refine SepWP.done (by simp only [arm64_norm]; try rfl) (by simp only [arm64_norm, hrun0, hruna1, hruna2]) ⟨by simp only [wp_norm, arm64_norm], fun hvmsa hinva => ?_⟩
      apply r1a_bind_sepWPp_state; intro sa; (try simp only [sa2, sa1, arm64_norm, r1a_low64, r1a_high64, hx22, hx25, hx28]); (try rw [hsp0])
      have hpool_sa : A.pool lim st s = A.pool lim st sa :=
        (A.pool_of_vmPreserved hvmsa1).symm.trans (hpool_a2.trans (A.pool_of_vmPreserved hvmsa).symm)
      rw [hpool_sa]
      let cs7 :=
        [(0x1b0, 4, (fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32),
         (0x1b8, 8, (fsp + 0x1b8#64) ↦₆₄ meG.name.ptr),
         (0x1c0, 8, memRegion (fsp + 0x1c0#64) 8),
         (0x1c8, 8, (fsp + 0x1c8#64) ↦₆₄ w.w5),
         (0x260, 16, addrUpperAt (fsp + 0x260#64) meG),
         (0x2a0, 32, protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64)),
         (0x4d0, 48, memRegion (fsp + 0x4d0#64) 48)]
      have hpack_locals :
          (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
            (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗
            (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x1c0#64) ↦₆₄ u3) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗
              (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
              (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
                memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
                memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ⊢
          memRegion (fsp + 0x1750#64) 24 ∗ r1a_localsCtx fsp 0 cs7 0x1750 24 [] := by
        have hme260 := r1a_addrUpperAt_close (fsp + 0x260#64) meG meW1 hmeW1
        have hd1d0 : ((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ⊢
            memRegion (fsp + 0x1d0#64) 16 := by
          have s := (ProofLib.memRegion_split (fsp + 0x1d0#64) 8 8 (by decide)).symm
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
        have hpeer2a0 : ((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
            addrUpperAt (fsp + 0x2b0#64) peerG ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ⊢
            protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) := by
          rw [protocolAddressAt_eq_parts A.repAlloc peerG (fsp + 0x2a0#64), r1a_addrNameHeap_eq_owned peerG]
          dsimp only [peerG, r1a_peerGhostOf]; rw [← hw2]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by sep_ac_rfl)
        dsimp only [addrUpperAt] at hpeer2a0; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpeer2a0 hme260 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
            (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
              ((fsp + 0x2b8#64) ↦₈ peerV.device) ∗ memRegion (fsp + 0x2b9#64) 7) ∗
            ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name) ∗
          (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
          (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1)) ∗
          ((fsp + 0x1c0#64) ↦₆₄ u3) ∗
          (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗
            memRegion (fsp + 0x1e0#64) 0x80 ∗ memRegion (fsp + 0x270#64) 0x30 ∗
            memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hpeer2a0 (sepConj_mono hme260 (sepConj_mono hd1d0 (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))) ?_
        have m1 := (ProofLib.memRegion_split (fsp + 0x1d0#64) 16 0x80 (by decide)).symm
        dsimp only [cs7, r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]
        simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp] at m1 ⊢
        rw [show protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ addrUpperAt (fsp + 0x260#64) meG ∗
            memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1c0#64) 8 ∗
            (((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion fsp 432 ∗ memRegion (fsp + 0x1b4#64) 4 ∗
              memRegion (fsp + 0x1e0#64) 128 ∗ memRegion (fsp + 0x270#64) 48 ∗ memRegion (fsp + 0x2c0#64) 10032) =
          memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗
            ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗
            ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ (memRegion (fsp + 0x1d0#64) 16 ∗ memRegion (fsp + 0x1e0#64) 128) ∗
            addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
            protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 10032 by sep_ac_rfl, m1]
        have splitTail : memRegion (fsp + 0x2c0#64) 10032 =
            memRegion (fsp + 0x2c0#64) 528 ∗ memRegion (fsp + 0x4d0#64) 48 ∗
              memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1750#64) 24 ∗ memRegion (fsp + 0x1768#64) 4744 := by
          have t1 := ProofLib.memRegion_split (fsp + 0x2c0#64) 528 9504 (by decide)
          have t2 := ProofLib.memRegion_split (fsp + 0x4d0#64) 48 9456 (by decide)
          have t3 := ProofLib.memRegion_split (fsp + 0x500#64) 4688 4768 (by decide)
          have t4 := ProofLib.memRegion_split (fsp + 0x1750#64) 24 4744 (by decide)
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at t1 t2 t3 t4; rw [t1, t2, t3, t4]
        rw [splitTail]; exact Entails.of_eq (by sep_ac_rfl)
      let ptrIdk := lsρ r1a_idKeySym
      let pathBs := dir ++ [0x2f#8] ++ utf8 "identity-key"
      have hdir_exp : ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir = (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir := by
        rw [hw6]; exact r1a_ownedBytes_expose A.repAlloc w.w4 w.w5 dir
      refine r1a_sepWPp_weaken_pre
        (Entails.trans (Entails.of_eq (by
          rw [hdir_exp]
          exact show _ =
            ((((fsp + 0x2a0#64) ↦₆₄ w.w0) ∗ ((fsp + 0x2a8#64) ↦₆₄ w.w1) ∗
              (((fsp + 0x2b0#64) ↦₆₄ BitVec.ofNat 64 peerG.name.bytes.length) ∗
                ((fsp + 0x2b8#64) ↦₈ peerG.device) ∗ memRegion (fsp + 0x2b9#64) 7)) ∗
              (((fsp + 0x1b0#64) ↦₃₂ peerG.device.zeroExtend 32) ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
                ((fsp + 0x1c0#64) ↦₆₄ _) ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗
                (((fsp + 0x260#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x268#64) ↦₆₄ meW1)) ∗
                (((fsp + 0x1d0#64) ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((fsp + 0x1d8#64) ↦₆₄ meW1) ∗
                  memRegion fsp 0x1b0 ∗ memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1e0#64) 0x80 ∗
                  memRegion (fsp + 0x270#64) 0x30 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))) ∗
              ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name) ∗
            ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
              ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
              ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
            ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st sa ∗
              r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
              memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
              (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
              tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
              runSaved s0) by sep_ac_rfl))
          (sepConj_mono hpack_locals (sepConj_mono_left (r1a_call7_to_memRegion56 g.call w)))) ?_
      apply r1a_sepWPp_rodata_idkey hinva
      have hsa_sp : sa.sp = fsp := by simp only [sa, sa2, sa1, arm64_norm, hsp0]
      have hsa_tr : s0.trace <+: sa.trace := by simpa only [sa, sa2, sa1, arm64_norm] using htr
      have hfits_path : FitsEnv M lim st (PathEnv dir (utf8 "identity-key")) :=
        fun evs hp => hfits evs (Or.inl hp)
      have hpath_ok := path_placed_ok (callerProg := runProgPlaced H) (i := 579) hh hpathStk
      unfold pathSpecPlaced at hpath_ok
      apply r1a_call_run (hh.fs (runProgPlaced H) 579) hpath_ok
        (x := (({ dirA := w.w5, dir := dir, dirRo := false, nameA := ptrIdk, name := utf8 "identity-key", nameRo := true, ret := fsp + 0x1750#64 } : PathGhost), st))
        (F := r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗
          r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
          memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
          tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
          runSaved s0)
        (retOff := 0x6a4)
        (by simp only [sa, sa2, sa1, arm64_norm]; rfl) (by simp only [sa, sa2, sa1, arm64_norm, hrun0]) hinva hsa_sp
        (by simp only [sa, sa2, sa1, arm64_norm, hbase.fp])
        (by simp only [sa, sa2, sa1, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
        hbase.spAligned (by simp only [sa, sa2, sa1, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
        hpanic
        (by dsimp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt]
            simp only [Bool.false_eq_true, ↓reduceIte]; rw [hsa_sp]
            have hpure : sa.readReg64 .x0 = fsp + 0x1750#64 ∧ sa.readReg64 .x1 = w.w5 ∧
                (sa.readReg64 .x2).toNat = dir.length ∧ sa.readReg64 .x3 = ptrIdk ∧
                (sa.readReg64 .x4).toNat = (utf8 "identity-key").length ∧
                dir.length < 2 ^ 32 ∧ (utf8 "identity-key").length < 2 ^ 32 ∧
                FitsEnv M lim st (PathEnv dir (utf8 "identity-key")) :=
              ⟨by simp only [sa, sa2, sa1, arm64_norm, hsp0, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
               by simp only [sa, sa2, sa1, arm64_norm, hx22],
               by simp only [sa, sa2, sa1, arm64_norm, hw6]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by omega),
               by simp only [sa, sa2, sa1, ptrIdk, lsρ, lsmpl, r1a_idKeySym, arm64_norm],
               by rw [r1a_utf8_idkey_len]; simp only [sa, sa2, sa1, arm64_norm],
               hdLen, hnLen, hfits_path⟩
            refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (sepConj_mono_left (entails_pure_intro_left hpure (Entails.refl _))))
        (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
      intro sb hbb hcsb _ hfilesb
      dsimp only [CryptoVerification.SpqrV1.ChainProofs.bytesAt]
      simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply r1a_sepWPp_exists_pre; intro evs_p
      apply r1a_sepWPp_pure_left; rintro ⟨htr_ba, hp_evs⟩
      let st_p := M.stepEvents evs_p st
      refine r1a_sepWPp_weaken_pre
        (Entails.of_eq (show _ =
          (ptrIdk ↦ᵣ utf8 "identity-key") ∗ vecU8 A.repAlloc (fsp + 0x1750#64) pathBs ∗
            ((w.w5 ↦ₛ dir) ∗ stackAt fsp (resStack - runFrame) ∗ A.pool lim st_p sb ∗
              (r1a_localsCtx fsp 0 cs7 0x1750 24 [] ∗ memRegion g.call 56 ∗
                r1a_ownedSlack A.repAlloc w.w4 w.w5 dir ∗ addrNameHeap A.repAlloc meG ∗
                memRegion g.res runResSize ∗ storesAt A.repAlloc g.stores StoresGhost.opened ∗
                (g.inp ↦ₛ inputOf g.i g.c) ∗ coinsInstalledPlaced g.coins (coinsOf g.i) ∗
                tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
                runSaved s0)) by dsimp only [pathBs, st_p]; rw [hsa_sp]; sep_ac_rfl)) ?_
      apply r1a_sepWPp_drop_left
      refine r1a_sepWPp_weaken_pre (sepConj_mono_left (vecU8_to_ownedBytes A.repAlloc (fsp + 0x1750#64) pathBs)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
      apply r1a_sepWPp_exists_pre; intro pathCap; apply r1a_sepWPp_exists_pre; intro pathPtr
      have hsb_fs : sb.fs.files = runFiles g.i := (hfilesb htr_ba).trans (by simpa only [sa, sa2, sa1, arm64_norm] using hfs)
      have hsb_out : ProcessOutcome.traceStreamBytes .stdout sb.trace = [] := by
        rw [htr_ba]; simpa only [sa, sa2, sa1, arm64_norm] using hout
      have hsb_tr : s0.trace <+: sb.trace := by rw [htr_ba]; exact hsa_tr
      have hx27_b : sb.readReg64 (.gpr 27#5) = fsp + 0x1750#64 :=
        (by simpa only [sa, sa2, sa1, arm64_norm] using hcsb.2.2.2.2.2.2.2.2.1 : sb.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5)).trans hx27
      have hpcb := hbb.pc; have := hbb.spAligned_cur; have hrunb := hbb.run; have hspb : sb.sp = fsp := hbb.sp
      change sb.pc = (blkPl_579).base + 1700#64 at hpcb
      apply sepWPp_seq_lscro (mid := lsρ lsReadFileSym) hbb.inv; (try dsimp only [runProgPlaced, lsProg_579])
      by_vm_open (
        rw [← hspb]; symm at hspb; wp_simp_pre only [sepConj_assoc]
        (iterate 6 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
        symm at hspb
        refine SepWP.done (by simp only [lsReadFileSym, arm64_norm]) (by simp only [arm64_norm, hrunb]) ⟨by simp only [wp_norm, arm64_norm], fun hvmbc hinvc => ?_⟩
        apply r1a_bind_sepWPp_state; intro sc
        (try simp only [arm64_norm]); (try rw [hspb])
        have hpool_bc : A.pool lim st_p sb = A.pool lim st_p sc := (A.pool_of_vmPreserved hvmbc).symm
        rw [hpool_bc]
        let cs8 := cs7 ++ [(0x1750, 8, (fsp + 0x1750#64) ↦₆₄ pathCap)]
        have hctx_read :
            (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗
              ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗
              r1a_localsCtx fsp 0 cs7 0x1750 24 [] ⊢
            memRegion (fsp + 0x23b0#64) 24 ∗ r1a_localsCtx fsp 0 cs8 0x23b0 24 [] := by
          have h16 : ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗ ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length) ⊢
              memRegion (fsp + 0x1758#64) 16 := by
            have s := (ProofLib.memRegion_split (fsp + 0x1758#64) 8 8 (by decide)).symm
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at s; rw [← s]
            exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
          refine Entails.trans (sepConj_mono_left (sepConj_mono_right h16)) ?_
          have s1 := (ProofLib.memRegion_split (fsp + 0x1758#64) 16 4744 (by decide)).symm
          have s2 := ProofLib.memRegion_split (fsp + 0x1758#64) 3160 1600 (by decide)
          have s3 := ProofLib.memRegion_split (fsp + 0x23b0#64) 24 1576 (by decide)
          simp only [cs8, cs7, List.append_assoc, List.cons_append, List.nil_append]
          dsimp only [r1a_localsCtx, runLocalsFrom, runLocalBytes, BitVec.ofNat_eq_ofNat]
          simp only [Nat.reduceAdd, Nat.reduceSub, Nat.sub_self, ProofLib.memRegion_zero, emp_sepConj, sepConj_emp, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 ⊢
          rw [show (((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ memRegion (fsp + 0x1758#64) 16) ∗
              (memRegion fsp 432 ∗ ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗
                memRegion (fsp + 0x1b4#64) 4 ∗ ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗
                memRegion (fsp + 0x1c0#64) 8 ∗ ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗
                addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
                protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗
                memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗ memRegion (fsp + 0x1768#64) 4744) =
            (memRegion (fsp + 0x1758#64) 16 ∗ memRegion (fsp + 0x1768#64) 4744) ∗ memRegion fsp 432 ∗
              ((fsp + 0x1b0#64) ↦₃₂ peerV.device.zeroExtend 32) ∗ memRegion (fsp + 0x1b4#64) 4 ∗
              ((fsp + 0x1b8#64) ↦₆₄ meG.name.ptr) ∗ memRegion (fsp + 0x1c0#64) 8 ∗
              ((fsp + 0x1c8#64) ↦₆₄ w.w5) ∗ memRegion (fsp + 0x1d0#64) 144 ∗
              addrUpperAt (fsp + 0x260#64) meG ∗ memRegion (fsp + 0x270#64) 48 ∗
              protocolAddressAt A.repAlloc peerG (fsp + 0x2a0#64) ∗ memRegion (fsp + 0x2c0#64) 528 ∗
              memRegion (fsp + 0x4d0#64) 48 ∗ memRegion (fsp + 0x500#64) 4688 ∗
              ((fsp + 0x1750#64) ↦₆₄ pathCap) by sep_ac_rfl, s1, s2, s3]
          exact Entails.of_eq (by sep_ac_rfl)
        have hstk_sp := r1a_stackAt_split fsp hreadStk hsub64
        have hpath_exp := r1a_ownedBytes_expose A.repAlloc pathCap pathPtr pathBs
        have hdir_back : (w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir = ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir :=
          hdir_exp.symm
        have hsc_sp : sc.sp = fsp := by simp only [sc, arm64_norm, hspb]
        have hsc_fs : sc.fs.files = runFiles g.i := by simpa only [sc, arm64_norm] using hsb_fs
        have hsc_tr : s0.trace <+: sc.trace := by simpa only [sc, arm64_norm] using hsb_tr
        have hfits_read : FitsEnv M lim st_p (cEnvs.readFile sc.fs.files pathBs) := fun evs_r hr =>
          ((fitsEvents_append M lim evs_p evs_r st).mp
            (hfits (evs_p ++ evs_r) (Or.inr (Or.inl ⟨evs_p, evs_r, hp_evs, hsc_fs ▸ hr, rfl⟩)))).2
        refine r1a_sepWPp_weaken_pre
          (Entails.trans (Entails.of_eq (show _ =
            ((((fsp + 0x1750#64) ↦₆₄ pathCap) ∗ ((fsp + 0x1758#64) ↦₆₄ pathPtr) ∗
              ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 pathBs.length)) ∗
              r1a_localsCtx fsp 0 cs7 0x1750 24 []) ∗
              ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
              ((w.w5 ↦ₛ dir) ∗ r1a_ownedSlack A.repAlloc w.w4 w.w5 dir) ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool lim st_p sc ∗
              (memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
                CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0) by sep_ac_rfl))
            (by rw [hpath_exp, hdir_back, hstk_sp]; exact sepConj_mono_left hctx_read)) ?_
        apply r1a_call_run (hh.fs (runProgPlaced H) 579) (subroutine_ok_withLsCodeRoLoaded_of_plain hc.readFile)
          (x := (({ pathA := pathPtr, path := pathBs, ret := fsp + 0x23b0#64 } : ReadFileGhost), st_p))
          (F := r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A.repAlloc pathCap pathPtr pathBs ∗
            ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
            memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗
            memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
            storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
            CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0)
          (retOff := 0x6bc)
          (by simp only [sc, lsReadFileSym, arm64_norm]) (by simp only [sc, arm64_norm, hrunb]) hinvc hsc_sp
          (by simp only [sc, arm64_norm, hbb.fp])
          (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbb.vregs])
          hbase.spAligned (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
          hpanic
          (by dsimp only [readFileSpecPlaced]; rw [hsc_sp]
              have hpure : sc.readReg64 .x0 = pathPtr ∧ (sc.readReg64 .x1).toNat = pathBs.length ∧
                  sc.readReg64 .x8 = fsp + 0x23b0#64 ∧ pathBs.length < 2 ^ 32 ∧ cliWrOk pathBs ∧
                  FitsEnv M lim st_p (cEnvs.readFile sc.fs.files pathBs) :=
                ⟨by simp only [sc, arm64_norm],
                 by simp only [sc, arm64_norm]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by dsimp only [pathBs]; omega),
                 by simp only [sc, arm64_norm]; rw [hspb], hpLen, hpOk, hfits_read⟩
              refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
                (sepConj_mono_left (entails_pure_intro_left hpure (Entails.refl _))))
          (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
        intro sd hbd hcsd _ hfilesd
        dsimp only [readFileSpecPlaced]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply r1a_sepWPp_exists_pre; intro evs_r
        apply r1a_sepWPp_exists_pre; intro r
        apply r1a_sepWPp_pure_left; intro hr_evs
        apply r1a_sepWPp_pure_left; intro hpost_r
        have hr_evs' : cEnvs.readFile (runFiles g.i) pathBs evs_r := hsc_fs ▸ hr_evs
        have hr_rd : r = cliIo.rd (runFiles g.i) pathBs := hsc_fs ▸ hpost_r.1
        obtain ⟨htr_d, herr_f, hok_f⟩ :=
          r1a_readFile_post_facts he hd hcall hsc_tr hsc_fs
            (by simpa only [sc, arm64_norm] using hsb_out) hfilesd (by simpa only [pathBs] using hpost_r)
        let st_r := M.stepEvents evs_r st_p
        have hremerge :
            ioVecAt A.repAlloc (fsp + 0x23b0#64) r ∗ (pathPtr ↦ₛ pathBs) ∗ stackAt sc.sp B.readFile ∗
              A.pool lim st_r sd ∗
              (r1a_localsCtx fsp 0 cs8 0x23b0 24 [] ∗ r1a_ownedSlack A.repAlloc pathCap pathPtr pathBs ∗
                ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
                memRegion (fsp - BitVec.ofNat 64 (resStack - runFrame)) ((resStack - runFrame) - B.readFile) ∗
                memRegion g.call 56 ∗ addrNameHeap A.repAlloc meG ∗ memRegion g.res runResSize ∗
                storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
                coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
                CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0) =
            runLocals fsp (cs8 ++ [(0x23b0, 24, ioVecAt A.repAlloc (fsp + 0x23b0#64) r)]) ∗
              ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
              addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
              memRegion g.res runResSize ∗ memRegion g.call 56 ∗
              storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
              coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
              CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
              stackAt fsp (resStack - runFrame) ∗ A.pool lim st_r sd := by
          rw [hsc_sp, r1a_locals_focus fsp cs8 0x23b0 24 (ioVecAt A.repAlloc (fsp + 0x23b0#64) r) [], hpath_exp, hstk_sp]
          sep_ac_rfl
        rw [hremerge]
        exact r1a_after_read hh hdrop hbnd he hd hcall
          (fun hr_err => by
            have herr_rd : cliIo.rd (runFiles g.i) pathBs = .error () := hr_rd.symm.trans hr_err
            have hev22 : Init1Env cEnvs g (.some meV meG) peerV dir ((evs_p ++ evs_r) ++ rustAllocEvents 22 1) :=
              Or.inr (Or.inr ⟨evs_p, evs_r, rustAllocEvents 22 1, hp_evs, hr_evs',
                by dsimp only [Init1AfterReadEnv, pathBs] at herr_rd ⊢; rw [herr_rd]; exact ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩, rfl⟩)
            have hf22 := ((fitsEvents_append M lim (evs_p ++ evs_r) (rustAllocEvents 22 1) st).mp (hfits _ hev22)).2
            rwa [M.stepEvents_append] at hf22)
          hpanic
          (fun hr_err s2 evs_f hf hat => by
            have herr_rd : cliIo.rd (runFiles g.i) pathBs = .error () := hr_rd.symm.trans hr_err
            have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (rustAllocEvents 22 1 ++ evs_f)) :=
              Or.inr (Or.inr ⟨evs_p, evs_r, rustAllocEvents 22 1 ++ evs_f, hp_evs, hr_evs',
                by dsimp only [Init1AfterReadEnv, pathBs] at herr_rd ⊢; rw [herr_rd]; exact ⟨evs_f, hf, rfl⟩, rfl⟩)
            have hst : M.stepEvents evs_f (M.stepEvents (rustAllocEvents 22 1) st_r) = M.stepEvents (evs_p ++ evs_r ++ (rustAllocEvents 22 1 ++ evs_f)) st := by
              dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
            exact hrej s2 _ StoresGhost.opened .postDispatch hat ⟨_, hev, hst⟩)
          (fun ikB evs_fp hr_ok hfp s2 evs_fd hfd hat => by
            have hok_rd : cliIo.rd (runFiles g.i) pathBs = .ok ikB := hr_rd.symm.trans hr_ok
            have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (evs_fp ++ evs_fd)) :=
              Or.inr (Or.inr ⟨evs_p, evs_r, evs_fp ++ evs_fd, hp_evs, hr_evs',
                by dsimp only [Init1AfterReadEnv, pathBs] at hok_rd ⊢; rw [hok_rd]; exact r1a_freeOnly_append hfp hfd, rfl⟩)
            have hst : M.stepEvents evs_fd (M.stepEvents evs_fp st_r) = M.stepEvents (evs_p ++ evs_r ++ (evs_fp ++ evs_fd)) st := by
              dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
            exact hrej s2 _ StoresGhost.opened .postDispatch hat ⟨_, hev, hst⟩)
          (fun ikB evs_fp evs_fi s1' d1 hr_ok hfp hfi hat1 => by
            have hok_rd : cliIo.rd (runFiles g.i) pathBs = .ok ikB := hr_rd.symm.trans hr_ok
            have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) :=
              Or.inr (Or.inr ⟨evs_p, evs_r, evs_fp ++ evs_fi, hp_evs, hr_evs',
                by dsimp only [Init1AfterReadEnv, pathBs] at hok_rd ⊢; rw [hok_rd]; exact r1a_freeOnly_append hfp hfi, rfl⟩)
            have hm := r1a_sepWPp_of_false_oom (oom := runOom s0) (hnext s1' (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) d1 hat1 hev)
            have hst : M.stepEvents evs_fi (M.stepEvents evs_fp st_r) = M.stepEvents (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) st := by
              dsimp only [st_r, st_p]; simp only [M.stepEvents_append]
            rwa [hst])
          hikStk hbd
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx19] using hcsd.1.trans hcsb.1)
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx20] using hcsd.2.1.trans hcsb.2.1)
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx21] using hcsd.2.2.1.trans hcsb.2.2.1)
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx22] using hcsd.2.2.2.1.trans hcsb.2.2.2.1)
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hx24] using hcsd.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.1)
          (by simpa only [sc, arm64_norm] using hcsd.2.2.2.2.2.2.2.1)
          (by simpa only [sc, sa, sa2, sa1, arm64_norm, hw6] using hcsd.2.2.2.2.2.2.2.2.2.1.trans hcsb.2.2.2.2.2.2.2.2.2.1)
          hw6 hw2 htr_d herr_f hok_f
        )
      )
    )
  intro g st s0 s me peerV dir Q Qp hh hc hdrop hres_slots hres64 he hd hcall hfits hpanic hrej hnext
  have hres : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hneed_eq ▸ hres_slots
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres hres64
  obtain ⟨_, _, _, _, _, hreadStk, hpathStk, _, _, _, _, hikStk, _⟩ :=
    runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) hres hres64
  have htag : s.readReg64 (.gpr 8#5) = 1#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hpc0 := hd.base.pc; have := hd.base.spAligned_cur; have hrun0 := hd.base.run
  change s.pc = (blkPl_579).base + 532#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x654) hd.base.inv; try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
  intro hinv1; apply r1a_bind_sepWPp_state; intro s1
  have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x654 := r1a_inRun
    (by simp only [runPcPlaced_eq, arm64_norm, s1, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, s1, hrun0]) (by simp only [arm64_norm, s1, hd.base.sp]) (by simp only [arm64_norm, s1, hd.base.fp]) hinv1
    (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hd.base.vregs]) hd.base.spAligned
  have htr1 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using hd.trace
  have hfs1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hd.fs
  have hout1 : ProcessOutcome.traceStreamBytes .stdout s1.trace = [] := by simpa only [arm64_norm, s1] using hd.stdout
  have hpool_01 : A.pool lim st s = A.pool lim st s1 := r1a_pool_congr_vm A lim st
    (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm]) (fun _ => by simp only [s1, arm64_norm])
  have hdm : dispatchMeHeap (A.atState lim st s) me = dispatchMeHeap A.repAlloc me := by cases me <;> rfl
  dsimp only [dispatchMemPlaced, CryptoVerification.SignalSession.Cli.RunCompose.dispatchMemPlaced]
  rw [callAt_atState A lim st s g.call g.c, storesAt_opened_atState A lim st s g.stores, hdm, RustCliAllocBudget.atState_pool, hpool_01, congrArg (callAt A.repAlloc g.call) hcall]
  dsimp only [callAt, callHeap, addrWords]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply r1a_sepWPp_exists_pre; intro w
  have hp_w (A0 W0 W1 W2 W3 W4 W5 W6 N0 P' R' : SepProp) :
      A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ P' ∗ R' = P' ∗ A0 ∗ W0 ∗ W1 ∗ W2 ∗ W3 ∗ W4 ∗ W5 ∗ W6 ∗ N0 ∗ R' := by sep_ac_rfl
  rw [hp_w]; apply r1a_sepWPp_pure_left; intro hw3
  rcases me with _ | ⟨meV, meG⟩
  · dsimp only [dispatchMeHeap, dispatchCells]
    exact r1a_sepWPp_weaken_pre (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; sep_ac_rfl))
      (r1a_init_none_branch (peerV := peerV) (dir := dir) (w := w)
        (F_heap := coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff)
        hh hbnd he hd hpanic
        (fun s2 evs hf hat => hrej s2 (M.stepEvents evs st) StoresGhost.opened .postDispatch hat ⟨evs, hf, rfl⟩)
        hb1 (by simp only [s1, arm64_norm, hd.x19]) (by simp only [s1, arm64_norm, hd.x20])
        (by simp only [s1, arm64_norm, hd.meRegs]) (by simp only [s1, arm64_norm, hd.x25]) htr1 hfs1 hout1)
  · dsimp only [dispatchMeHeap, dispatchCells]; rcases hd.meRegs with ⟨hx21_0, hx28_0, _, _, _⟩
    have hmep := ownedBytes_pure A.repAlloc meG.name.cap meG.name.ptr (BitVec.ofNat 64 meG.name.bytes.length) meG.name.bytes
    have hpeerp := ownedBytes_pure A.repAlloc w.w0 w.w1 w.w2 peerV.name
    have hdirp := ownedBytes_pure A.repAlloc w.w4 w.w5 w.w6 dir
    refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
      addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗
        ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        (memRegion g.res runResSize ∗
          ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
            ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
            ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
          storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
          CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
          runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
          stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    rw [r1a_addrNameHeap_eq_owned meG, hmep, hpeerp, hdirp, ← r1a_addrNameHeap_eq_owned meG]
    have hp3 {P1 P2 P3 : Prop} (A1 A2 A3 R0 : SepProp) :
        (⌜P1⌝ ∗ A1) ∗ (⌜P2⌝ ∗ A2) ∗ (⌜P3⌝ ∗ A3) ∗ R0 = ⌜P1⌝ ∗ ⌜P2⌝ ∗ ⌜P3⌝ ∗ (A1 ∗ A2 ∗ A3 ∗ R0) := by sep_ac_rfl
    rw [hp3]; apply r1a_sepWPp_pure_left; rintro ⟨_, _, hme_lt, _⟩
    apply r1a_sepWPp_pure_left; rintro ⟨hw2, _, _, _⟩
    apply r1a_sepWPp_pure_left; rintro ⟨hw6, _, _, _⟩
    refine r1a_sepWPp_weaken_pre (Entails.of_eq (show _ =
      runLocals (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] ∗
        ((g.call ↦₆₄ w.w0) ∗ ((g.call + 8#64) ↦₆₄ w.w1) ∗ ((g.call + 16#64) ↦₆₄ w.w2) ∗
          ((g.call + 24#64) ↦₆₄ w.w3) ∗ ((g.call + 32#64) ↦₆₄ w.w4) ∗
          ((g.call + 40#64) ↦₆₄ w.w5) ∗ ((g.call + 48#64) ↦₆₄ w.w6)) ∗
        addrNameHeap A.repAlloc meG ∗ ownedBytes A.repAlloc w.w4 w.w5 w.w6 dir ∗
        ownedBytes A.repAlloc w.w0 w.w1 w.w2 peerV.name ∗ memRegion g.res runResSize ∗
        storesAt A.repAlloc g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        coinsInstalledPlaced g.coins (coinsOf g.i) ∗ tokenInitPlacedAt ∗
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ runSaved s0 ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s1 by sep_ac_rfl)) ?_
    have hcmn : (meG.name.cap + 1#64 == 0#64) = false := beq_add_one_zero_false_of_lt hme_lt
    have hcarve := r1a_locals_carve_region (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 []
    have hf2a0 := r1a_locals_focus (runFsp s0) [(0x1d0, 16, addrUpperAt (runFsp s0 + 0x1d0#64) meG)] 0x2a0 32 (memRegion (runFsp s0 + 0x2a0#64) 32) []
    have h32 : memRegion (runFsp s0 + 0x2a0#64) 32 =
        (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
          ((runFsp s0 + 0x2a0#64) ↦₆₄ q0) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ q1) ∗
            ((runFsp s0 + 0x2b0#64) ↦₆₄ q2) ∗ ((runFsp s0 + 0x2b8#64) ↦₆₄ q3)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1a_memRegion32_eq_words (runFsp s0 + 0x2a0#64)
    simp only [List.nil_append, List.append_nil] at hcarve hf2a0; rw [hcarve, hf2a0, h32]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply r1a_sepWPp_exists_pre; intro q0; apply r1a_sepWPp_exists_pre; intro q1
    apply r1a_sepWPp_exists_pre; intro q2; apply r1a_sepWPp_exists_pre; intro q3
    have hpc1 := hb1.pc; have hal0 : (s0.sp &&& 15#64 == 0#64) = true := hd.base.spAligned
    have hal1 : (s1.sp &&& 15#64 == 0#64) = true := hb1.spAligned_cur
    have hrun1 := hb1.run; have hsp1 := hb1.sp; change s1.pc = (blkPl_579).base + 1620#64 at hpc1
    have hx21_1 : s1.readReg64 (.gpr 21#5) = meG.name.cap := by simp only [s1, arm64_norm, hx21_0]
    have hx25_1 : s1.readReg64 (.gpr 25#5) = g.call := by simp only [s1, arm64_norm, hd.x25]
    apply sepWPp_seq_lscro (mid := runPcPlaced 0x668) hb1.inv; (try dsimp only [runProgPlaced, lsProg_579])
    by_vm_open (
      rw [← hsp1]; symm at hsp1; wp_simp_pre only [sepConj_assoc]
      (iterate 5 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
      symm at hsp1
      refine SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun1]) ⟨by simp only [wp_norm, arm64_norm], fun hvm12 hinv2 => ?_⟩
      apply r1a_bind_sepWPp_state; intro s2
      (try simp only [arm64_norm, r1a_low64, r1a_high64, hx25_1]); (try rw [hsp1])
      have hpool_12 : A.pool lim st s1 = A.pool lim st s2 := (A.pool_of_vmPreserved hvm12).symm
      rw [hpool_12]
      exact r1a_sepWPp_weaken_pre (Entails.of_eq (by rw [hw2]; sep_ac_rfl))
        (h_some_after_668 (peerV := peerV) (dir := dir) (w := w)
          hh hc hdrop hbnd he hd hcall hfits hpanic hrej hnext hpathStk hreadStk hikStk
          (r1a_inRun
            (by simp only [runPcPlaced_eq, arm64_norm, s2, hx21_1, hcmn, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
            (by simp only [arm64_norm, s2, hrun1]) (by simp only [arm64_norm, s2, hsp1])
            (by simp only [arm64_norm, s2, hb1.fp]) hinv2
            (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s2, hb1.vregs])
            hd.base.spAligned)
          (by simp only [arm64_norm, s2, s1, hd.x19]) (by simp only [arm64_norm, s2, s1, hd.x20])
          (by simp only [arm64_norm, s2, hx21_1]) (by simp only [arm64_norm, s2])
          (by simp only [arm64_norm, s2]) (by simp only [arm64_norm, s2, hx25_1])
          (by simp only [arm64_norm, s2, s1, hd.x27]) (by simp only [arm64_norm, s2, s1, hx28_0])
          hw6 hw2 hw3 (by simpa only [arm64_norm, s2] using htr1)
          (by simpa only [arm64_norm, s2] using hfs1) (by simpa only [arm64_norm, s2] using hout1))
    )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
