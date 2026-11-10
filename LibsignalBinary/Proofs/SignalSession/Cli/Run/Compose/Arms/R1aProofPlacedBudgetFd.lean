/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Relocatable Arm `R1a` Proof

Proves `run_hop_init1_of_slots_placed_ok_fd` and `run_hop_init1_placed_ok_fd` on Block `579`,
preserving `FdsGe3Closed` across `Dir::path`, `read_file` (`0x6b8 → 0x6bc`), and `IdentityKey::decode`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWPp_seq_lscro subroutine_ok_withLsCodeRoLoaded_of_plain
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (lsReadFileSym)
open CryptoVerification.SignalSession.Cli (PathGhost ReadFileGhost StoresGhost ioVecAt utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW RunCall addrWords callAt callHeap cliIo cliWrOk coinsInstalledPlaced coinsOf
   handleErrorSymCli inputOf ownedBytes runResSize storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (beq_add_one_zero_false_of_lt entails_pure_intro_left ownedBytes_pure vecU8_to_ownedBytes)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_596)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtRunEntryPlaced Bytes InRunPlaced Init1Data MeAtDispatch PanicK
   RunNeeds RunSem addrNameHeap addrUpperAt addrUpperAt_entails_memRegion dispatchCells
   dispatchMeHeap init1Cells protocolAddressAt_eq_parts r1b_StackBounds runFiles runFsp
   runLocalBytes runLocals runLocalsFrom runOom runPcPlaced runPcPlaced_eq runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots pathNeed runFrame runNeed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget fitsEvents_append
   rustAllocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudgetFd
  (path_placed_caller_ok_of_allocFs_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed withLsRetAddr624AndFds withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopInit1PlacedFd RunHopInit1PlacedFdOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
  (Init1AfterReadEnv Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
  (r1a_CodeOk r1a_addrNameHeap_eq_owned r1a_addrUpperAt_close r1a_addrUpperAt_open
   r1a_bind_sepWPp_state r1a_call7_to_memRegion56 r1a_call_run r1a_false_entails
   r1a_freeOnly_append r1a_high64 r1a_idKeySym r1a_idKey_path_bounds r1a_localsBound r1a_localsCtx
   r1a_localsEnd r1a_locals_carve_region r1a_locals_focus r1a_low64 r1a_memRegion32_eq_words
   r1a_ownedBytes_expose r1a_ownedSlack r1a_peerGhostOf r1a_pool_setMem_write16
   r1a_pool_setMem_write32 r1a_pool_setMem_write32_2 r1a_pool_setMem_write64
   r1a_pool_setMem_write64_2 r1a_pool_setMem_write64_4 r1a_pool_setMem_write8
   r1a_readFile_post_facts r1a_rodata_idkey_intro r1a_sepWPp_exists_pre r1a_sepWPp_pure_left
   r1a_sepWPp_weaken_pre r1a_stackAt_split r1a_utf8_idkey_len)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMid
  (r1a_init_none_branch r1a_pool_congr_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetMidFd
  (r1a_after_read_fd)
open scoped LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_stackBounds_of_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState dispatchMemPlaced init1MemPlaced runNeed_bounds_placed storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (pathSpecPlaced readFileSpecPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  r1a_pool_setMem_write8 r1a_pool_setMem_write16 r1a_pool_setMem_write32
  r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
  r1a_pool_setMem_write64_4
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp, local arm64_norm, local wp_norm]
private theorem r1a_fs_setMem_local (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem r1a_fs_setPState_local (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := rfl

/-! ## `InRunPlaced` and `Dir::path` Wrappers -/

private theorem r1a_inRun_fd [LibsignalPlacement] {s0 s : State} {off : Nat}
    (hpc : s.pc = runPcPlaced off) (hrun : s.status = .Running) (hsp : s.sp = runFsp s0)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64) (hinv : r1a_CodeOk s.mem)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) (hal : s0.spAligned = true) :
    InRunPlaced r1a_CodeOk s0 s off :=
  ⟨hpc, hrun, hsp, hfp, hinv, hv, hal⟩

private theorem r1a_sepWPp_rodata_idkey_fd [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp}
    (hinv : r1a_CodeOk s.mem)
    (h : SepWPp prog ret s ((lsρ r1a_idKeySym ↦ᵣ utf8 "identity-key") ∗ P) Q Qp O) :
    SepWPp prog ret s P Q Qp O :=
  fun R hm hL => h R (by simpa only [sepConj_assoc] using r1a_rodata_idkey_intro hinv hm) hL

private theorem r1a_sepWPp_drop_left_fd {prog : Program} {ret : BitVec 64} {s : State}
    {D P : SepProp} {Q Qp : State → SepProp → Prop} {O : State → SepProp}
    (h : SepWPp prog ret s P Q Qp O) : SepWPp prog ret s (D ∗ P) Q Qp O :=
  fun R hm hL => h R (Satisfies.drop_mid (by simpa only [sepConj_comm D P, sepConj_assoc] using hm)) hL

private theorem r1a_sepWPp_of_false_oom_fd {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp (fun _ => ⌜False⌝)) : SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => match h R hm hL with
    | ⟨sf, hs, Or.inl h1⟩ => ⟨sf, hs, Or.inl h1⟩
    | ⟨sf, hs, Or.inr (Or.inl h2)⟩ => ⟨sf, hs, Or.inr (Or.inl h2)⟩
    | ⟨_, _, Or.inr (Or.inr ⟨_, hmo⟩)⟩ => (not_satisfies_false_sepConj hmo).elim

theorem r1a_path_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) {stk : Nat} (hstk : pathNeed ≤ stk) :
    subroutine_ok (runProgPlaced H) (blkPl_596).base
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv stk)) :=
  path_placed_caller_ok_of_allocFs_fd (callerProg := runProgPlaced H) (i := 579)
    (resStack := doReserveStackX) hh.allocFs (by decide) hstk
    (hh.panics handleErrorSymCli (by decide)) (by decide)

/-! ## `some` Entry Path and Top-Level `run_hop_init1_placed_ok_fd` -/

set_option maxHeartbeats 800000 in
private theorem r1a_some_after_668_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {slots : RunSlots}
    {g : RunCall} {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {w : CallW}
    {s0 s_disp s : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B slots)
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
      FdsGe3Closed s1.fs →
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
    (hfs : s.fs.files = runFiles g.i) (hfds : FdsGe3Closed s.fs)
    (hout : ProcessOutcome.traceStreamBytes .stdout s.trace = []) :
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
    apply r1a_sepWPp_rodata_idkey_fd hinva
    have hsa_sp : sa.sp = fsp := by simp only [sa, sa2, sa1, arm64_norm, hsp0]
    have hsa_tr : s0.trace <+: sa.trace := by simpa only [sa, sa2, sa1, arm64_norm] using htr
    have hsa_fds : FdsGe3Closed sa.fs := by simpa only [sa, sa2, sa1, arm64_norm] using hfds
    have hfits_path : FitsEnv M lim st (PathEnv dir (utf8 "identity-key")) :=
      fun evs hp => hfits evs (Or.inl hp)
    have hpath_ok0 := r1a_path_placed_ok_fd hh hpathStk
    unfold pathSpecPlaced at hpath_ok0
    have hpath_ok := subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed hpath_ok0
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
      (by dsimp only [withFdsGe3Closed, CryptoVerification.SpqrV1.ChainProofs.bytesAt]
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
            (sepConj_mono_left (entails_pure_intro_left hsa_fds (entails_pure_intro_left hpure (Entails.refl _)))))
      (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
    intro sb hbb hcsb _ hfilesb
    dsimp only [withFdsGe3Closed, CryptoVerification.SpqrV1.ChainProofs.bytesAt]
    rw [sepConj_assoc]
    apply r1a_sepWPp_pure_left; intro hsb_fds
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
    apply r1a_sepWPp_drop_left_fd
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
      have hsc_fds : FdsGe3Closed sc.fs := by simpa only [sc, arm64_norm] using hsb_fds
      have hsc_tr : s0.trace <+: sc.trace := by simpa only [sc, arm64_norm] using hsb_tr
      have hsc_lr : sc.readReg64 .lr = runPcPlaced 0x6bc := by
        simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
      have hsc_lr_ls : LsRetAddr624 (sc.readReg64 .lr) := by
        rw [hsc_lr, show runPcPlaced 0x6bc = (blkPl_579).base + 1724#64 from by
          simp only [runPcPlaced_eq, BitVec.ofNat_eq_ofNat]]
        exact lsRetAddr624_blockPlacement_base_add 579 1724#64 (by decide) (by decide)
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
        hbase.spAligned hsc_lr
        hpanic
        (by dsimp only [withLsRetAddr624AndFds, withPreGuard, withFdsGe3Closed, readFileSpecPlaced]; rw [hsc_sp]
            have hpure : sc.readReg64 .x0 = pathPtr ∧ (sc.readReg64 .x1).toNat = pathBs.length ∧
                sc.readReg64 .x8 = fsp + 0x23b0#64 ∧ pathBs.length < 2 ^ 32 ∧ cliWrOk pathBs ∧
                FitsEnv M lim st_p (cEnvs.readFile sc.fs.files pathBs) :=
              ⟨by simp only [sc, arm64_norm],
               by simp only [sc, arm64_norm]; (try simp only [BitVec.toNat_ofNat]); exact Nat.mod_eq_of_lt (by dsimp only [pathBs]; omega),
               by simp only [sc, arm64_norm]; rw [hspb], hpLen, hpOk, hfits_read⟩
            refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (sepConj_mono_left
                (entails_pure_intro_left hsc_lr_ls
                  (entails_pure_intro_left hsc_fds
                    (entails_pure_intro_left hpure (Entails.refl _))))))
        (fun _ => r1a_false_entails) (fun _ _ => Entails.refl _) (fun _ => r1a_false_entails)
      intro sd hbd hcsd _ hfilesd
      dsimp only [withLsRetAddr624AndFds, withPreGuard, withFdsGe3Closed, readFileSpecPlaced]
      rw [sepConj_assoc]
      apply r1a_sepWPp_pure_left; intro hsd_fds
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
      exact r1a_after_read_fd hh hdrop hbnd he hd hcall
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
        (fun ikB evs_fp evs_fi s1' d1 hr_ok hfp hfi hat1 hfds1 => by
          have hok_rd : cliIo.rd (runFiles g.i) pathBs = .ok ikB := hr_rd.symm.trans hr_ok
          have hev : Init1Env cEnvs g (.some meV meG) peerV dir (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) :=
            Or.inr (Or.inr ⟨evs_p, evs_r, evs_fp ++ evs_fi, hp_evs, hr_evs',
              by dsimp only [Init1AfterReadEnv, pathBs] at hok_rd ⊢; rw [hok_rd]; exact r1a_freeOnly_append hfp hfi, rfl⟩)
          have hm := r1a_sepWPp_of_false_oom_fd (oom := runOom s0)
            (hnext s1' (evs_p ++ evs_r ++ (evs_fp ++ evs_fi)) d1 hat1 hfds1 hev)
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
        hw6 hw2 htr_d hsd_fds herr_f hok_f
      )
    )
  )

set_option maxHeartbeats 800000 in
/-- Slot-parametric `FdsGe3Closed`-threaded proof of `RunHopInit1PlacedFdOf` on Block `579`. -/
theorem run_hop_init1_of_slots_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : RunSlots} {resStack : Nat}
    (hneed_eq : runNeed B slots = runNeed B (slotsOfPlaced A lim sEnvs S needs)) :
    RunHopInit1PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (Init1Env cEnvs)
      H B S slots resStack := by
  rintro g st s0 s me peerV dir Q Qp hh hc hdrop hres hres64 he ⟨hd, hfds⟩ hcall hfits hpanic hrej hnext
  have hres_slots : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hneed_eq ▸ hres
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres_slots hres64
  obtain ⟨_, _, _, _, _, hreadStk, hpathStk, _, _, _, _, hikStk, _⟩ :=
    runNeed_bounds_placed (A := A) (lim := lim) (envs := sEnvs) hres_slots hres64
  have htag : s.readReg64 (.gpr 8#5) = 1#64 := by simpa [hcall, CallV.tag] using hd.x8
  have hpc0 := hd.base.pc; have := hd.base.spAligned_cur; have hrun0 := hd.base.run
  change s.pc = (blkPl_579).base + 532#64 at hpc0
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x654) hd.base.inv; try dsimp only [runProgPlaced, lsProg_579]
  (iterate 3 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [runPcPlaced_eq, arm64_norm, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [arm64_norm, hrun0])
  intro hinv1; apply r1a_bind_sepWPp_state; intro s1
  have hb1 : InRunPlaced r1a_CodeOk s0 s1 0x654 := r1a_inRun_fd
    (by simp only [runPcPlaced_eq, arm64_norm, s1, htag, bne, Bool.not_false, Bool.not_true, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, s1, hrun0]) (by simp only [arm64_norm, s1, hd.base.sp]) (by simp only [arm64_norm, s1, hd.base.fp]) hinv1
    (by simp only [calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, s1, hd.base.vregs]) hd.base.spAligned
  have htr1 : s0.trace <+: s1.trace := by simpa only [arm64_norm, s1] using hd.trace
  have hfs1 : s1.fs.files = runFiles g.i := by simpa only [arm64_norm, s1] using hd.fs
  have hfds1 : FdsGe3Closed s1.fs := by simpa only [arm64_norm, s1] using hfds
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
        (r1a_some_after_668_fd (peerV := peerV) (dir := dir) (w := w)
          hh hc hdrop hbnd he hd hcall hfits hpanic hrej
          (fun s1' evs d1 hat1 hfds1 hev => hnext s1' evs d1 ⟨hat1, hfds1⟩ hev)
          hpathStk hreadStk hikStk
          (r1a_inRun_fd
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
          (by simpa only [arm64_norm, s2] using hfs1)
          (by simpa only [arm64_norm, s2] using hfds1)
          (by simpa only [arm64_norm, s2] using hout1))
    )

theorem run_hop_init1_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopInit1PlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs (Init1Env cEnvs)
      H B S needs resStack :=
  run_hop_init1_of_slots_placed_ok_fd (sEnvs := sEnvs) (needs := needs) rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetFd
