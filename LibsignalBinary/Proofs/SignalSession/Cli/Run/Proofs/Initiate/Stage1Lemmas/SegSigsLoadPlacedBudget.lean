/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable Stage 1 Segment 4 (`0x01fc → 0x0390`): `load_session(peer)`

Verifies `stage1_load_session_placed_ok` on `initProgPlaced` over `RustCliAllocBudget M` and
`VmPreserved`, stepping through `sessLoadShim` (block `604`), `sessLoadPoll` (block `569`),
`memcpy(312)`, optional `futDrop`, and `__rust_dealloc(24, 8)` to establish `AtStage2Placed` and
`stage2MemPlaced` at `0x0390`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded LoadShimCall)
open CryptoVerification.LibsignalTripleRatchet (memcpyName)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost SessFileWf SessLoadPollGhost StoresGhost addressText dirAt pathOf sessLoadBoxAt
   sessLoadFutVtSym sessLoadOutAt)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs
  (InitOk₀ bundleEOf? cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage2Placed InInitiatePlaced coinsCursorAtPlaced initArgsAtPlaced initLocalsSize
   initPcPlaced initProgExtPlaced initProgPlaced initSaved sessFileWf_false_of_nil)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (cs_fp cs_vregs cs_x19 cs_x20 cs_x22 cs_x23 false_entails load_frame_5ba_merge
   load_frame_5ba_split memRegion_48_words memRegion_merge memcpyScratchSpec pure_sepConj_intro
   sepWPp_drop_left sepWPp_exists_left sepWPp_exists_pos2 sepWPp_exists_pos3 sepWPp_mono_pre
   sepWPp_pure_elim sepWPp_with_rodata sessLoadBoxAt_entails_memRegion spAligned_of_frame
   spAligned_of_sp_eq sp_sub_4192_sub_3216 sp_sub_96_add_96 sp_sub_96_sub_4096)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas.Stage1Norm
  (extractLsb_append_hi extractLsb_append_lo extractLsb_pack32_0 extractLsb_pack32_0_16
   extractLsb_pack32_8 extractLsb_pack32_16 extractLsb_pack32_16_16 extractLsb_pack32_24
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre fs_writeReg_pre
   fs_writeVReg128_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg32_writeVReg128_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg64_writeVReg128_pre
   readReg_setMem_setPC_pre readReg_setPC_pre readReg_writeVReg128_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   sp_setMem_setPC_pre sp_setPC_pre sp_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
   trace_writeVReg128_pre)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced stage2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.CalleesPlacedBudget
  (init_dealloc_placed_ok_at init_memcpyScratch_vm_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
  (initCallLscro rodata_sessLoadFut_align_placed' rodata_sessLoadFut_drop_placed'
   rodata_sessLoadFut_poll_placed' rodata_sessLoadFut_size_placed' rodata_sessVt_loadSlot_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
  (sepWP_done_tpidr sepWPp_step_to_vm_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
  (stage2MemPlaced_of_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre
  fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre
  readVReg128_writeReg64_pre readVReg128_writeReg32_pre readVReg128_writeReg_pre
  extractLsb_append_lo extractLsb_append_hi
  extractLsb_pack32_0 extractLsb_pack32_8
  extractLsb_pack32_16 extractLsb_pack32_24
  extractLsb_pack32_0_16 extractLsb_pack32_16_16

/-! ## Spatial cut predicates and `SessLoadPollGhost` constructor -/

/-- `SessLoadPollGhost` argument passed to `sessLoadPoll` at `0x022c`. -/
abbrev sessLoadPollGhostOf (x : InitGhost) (s0 : State) (futPtr : BitVec 64) :
    SessLoadPollGhost :=
  { call :=
      { fut := futPtr
        out := (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64
        addr := x.peer
        addrA := x.peerA }
    self := x.stores + 0xf0#64
    dir := StoresGhost.opened.sessions }

/-- Spatial state at `0x020c` after `sessLoadShim` returns. -/
abbrev afterLoadShimMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 sAS : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    A.live (sAS.readReg64 .x0) 24 8 ∗
    sessLoadBoxAt (sAS.readReg64 .x0) (x.stores + 0xf0#64) x.peerA 0#8 ∗
    A.pool lim st sAS ∗ stackAt fsp (stk - cliInitiateFrame) ∗
    storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    lsLogOff ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)

/-- Spatial state at `0x0230` after `sessLoadPoll` returns with `ans = .ok none`. -/
def afterLoadPollMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 sAP : State) (futPtr m0 m1 m2 m3 m4 m5 : BitVec 64) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  (((fsp + 5632#64) ↦₆₄ (0#64 - 1#64)) ∗
      ((fsp + 5640#64) ↦₆₄ m0) ∗ ((fsp + 5648#64) ↦₆₄ m1) ∗
      ((fsp + 5656#64) ↦₆₄ m2) ∗ ((fsp + 5664#64) ↦₆₄ m3) ∗
      ((fsp + 5672#64) ↦₆₄ m4) ∗ ((fsp + 5680#64) ↦₆₄ m5) ∗
      memRegion (fsp + 0x1638#64) 312) ∗
    (sessLoadBoxAt futPtr (x.stores + 0xf0#64) x.peerA 1#8 ∗
      dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗
      A.pool lim st sAP ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
    (A.live futPtr 24 8 ∗
      dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
      dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
      dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
      dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
      dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc x.me x.meA ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      lsLogOff ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 6 ∗
      ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
      ((fsp + 0x5c8#64) ↦₆₄ lsρ sessLoadFutVtSym) ∗
      memRegion (fsp + 0x5d0#64) 40 ∗
      memRegion (fsp + 0x5f8#64) 312 ∗
      memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
      memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770))

/-- Spatial state at `0x02f0` / `0x0308` after `memcpy(fsp + 0x5f8, fsp + 0x1638, 312)`. -/
def afterLoadMemcpyMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 s : State) (futPtr : BitVec 64) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  (memRegion (fsp + 0x5f8#64) 312 ∗ memRegion (fsp + 0x1638#64) 312 ∗
      stackAt fsp (stk - cliInitiateFrame)) ∗
    memRegion (fsp + 0x1600#64) 56 ∗
    A.live futPtr 24 8 ∗
    sessLoadBoxAt futPtr (x.stores + 0xf0#64) x.peerA 1#8 ∗
    storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    lsLogOff ∗ A.pool lim st s ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) 6 ∗
    ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
    ((fsp + 0x5c8#64) ↦₆₄ lsρ sessLoadFutVtSym) ∗
    memRegion (fsp + 0x5d0#64) 40 ∗
    memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
    memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770)

theorem afterLoadMemcpyMemPlaced_of_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 : State) {s1 s2 : State} (futPtr : BitVec 64) (hvm : VmPreserved s1 s2) :
    afterLoadMemcpyMemPlaced A lim st x stk s0 s1 futPtr =
      afterLoadMemcpyMemPlaced A lim st x stk s0 s2 futPtr := by
  unfold afterLoadMemcpyMemPlaced
  rw [A.pool_of_vmPreserved hvm]

/-! ## `sessLoadShim` (`0x01fc → 0x020c`) -/

set_option maxHeartbeats 1600000 in
/-- Invokes `sessLoadShim` (block `604`, `0x01fc → 0x020c`). -/
theorem stage1_load_to_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 24))
    (hctrl : InInitiatePlaced s0 s3 0x01fc)
    (htr : s3.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAS : State) (evs1 : List AllocEvent),
      BoxAllocEnv 24 evs1 →
      sAS.readReg64 .x0 ≠ 0#64 →
      (sAS.readReg64 .x0).toNat % 8 = 0 →
      InInitiatePlaced s0 sAS 0x020c →
      sAS.trace = s0.trace →
      sAS.readReg64 (.gpr 1#5) = lsρ sessLoadFutVtSym →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAS
        (afterLoadShimMemPlaced A lim (M.stepEvents evs1 st) x stk s0 sAS) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage2MemPlaced A lim st x stk s0 s3) Q Qp oom := by
  have hpc3 : s3.pc = (blkPl_521).base + 508#64 := hctrl.pc
  have hrun3 := hctrl.run; have hsp3 := hctrl.sp
  have hfp3 := hctrl.fp; have hx19_3 := hctrl.x19; have hfs30 := hctrl.files0
  have hvregs3 := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal3 := spAligned_of_frame hal0 hsp3
  unfold stage2MemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hsp3 ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp3] using hal3
  unfold initArgsAtPlaced
  refine sepWPp_with_rodata (rodata_sessVt_loadSlot_placed hStore hctrl.inv) ?_
  generalize hshimA : lsmpl.base 604 = shimAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed shimAddr hctrl.inv ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sShim hsShim hpcS hrunS hinvS hvmS
    subst hshimA
    refine sepWPp_drop_left ?_
    have hspS : sShim.sp = fsp := by rw [← hsShim]; simp [wp_norm, arm64_norm, hsp3]
    have hx0S : sShim.readReg64 .x0 = x.stores + 0xf0#64 := by
      rw [← hsShim]; simp [wp_norm, arm64_norm]
    have hx1S : sShim.readReg64 .x1 = x.peerA := by
      rw [← hsShim]; simp [wp_norm, arm64_norm]
    have hlrS : sShim.readReg64 .lr = initPcPlaced 0x020c := by
      rw [← hsShim]
      change _ = (blkPl_521).base + 524#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hfpS : sShim.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsShim]; simp [wp_norm, arm64_norm, hfp3]
    have hx19S : sShim.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsShim]; simp [wp_norm, arm64_norm, hx19_3]
    have hvregsS : calleeSavedVRegs sShim = calleeSavedVRegs s0 := by
      rw [← hsShim]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs3]
    have htrS : sShim.trace = s0.trace := by rw [← hsShim]; simp [wp_norm, arm64_norm, htr]
    have hfsS : sShim.fs.files = s0.fs.files := by
      rw [← hsShim]; simp [wp_norm, arm64_norm, hfs30]
    clear hsShim
    have halS : sShim.spAligned = true := spAligned_of_sp_eq hal3 (hspS.trans hsp3.symm)
    have hpoolS : A.pool lim st s3 = A.pool lim st sShim := (A.pool_of_vmPreserved hvmS).symm
    rw [hpoolS]
    let loadShimArg : LoadShimCall := { self := x.stores + 0xf0#64, addrA := x.peerA }
    let shimFrame : SepProp :=
      storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sShim _ Q Qp oom
    refine initCallLscro hh hpanic hStore.sessLoadShim (gx := (loadShimArg, st)) (F := shimFrame)
      hpcS hrunS halS hinvS htrS hfsS hlrS ?_ (fun _ => false_entails _) ?_
    · dsimp only [shimFrame, loadShimArg, initArgsAtPlaced]
      rw [hspS]
      repeat rw [sepConj_assoc]
      exact pure_sepConj_intro ⟨hx0S, hx1S, hFitsShim⟩ (by sep_frame)
    intro sAS hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
    dsimp only [loadShimArg, shimFrame]
    refine sepWPp_exists_left fun evs1 => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun ⟨hvtAS, hfutNZ, hfutAl, htrAS, hevs1⟩ => ?_
    have htrAS' : sAS.trace = s0.trace := htrAS.trans htrS
    have hfsAS' : sAS.fs.files = s0.fs.files := hfsAS htrAS'
    have hspAS' : sAS.sp = fsp := hspAS.trans hspS
    have hctrlAS : InInitiatePlaced s0 sAS 0x020c :=
      ⟨hpcAS, hrunAS, hspAS'.trans hfsp.symm, (cs_fp hcsAS).trans hfpS,
        (cs_x19 hcsAS).trans hx19S, hfsAS', hinvAS, (cs_vregs hcsAS).trans hvregsS, hal0⟩
    rw [hspS]
    refine sepWPp_mono_pre
      (P' := afterLoadShimMemPlaced A lim (M.stepEvents evs1 st) x stk s0 sAS)
      (by unfold afterLoadShimMemPlaced; dsimp only; rw [← hfsp]; sep_frame) ?_
    exact hnext sAS evs1 hevs1 hfutNZ hfutAl hctrlAS htrAS' hvtAS)

/-! ## `sessLoadPoll` and `ans = .ok none` unpacking (`0x020c → 0x0230`) -/

set_option maxHeartbeats 1600000 in
/-- Invokes `sessLoadPoll` (block `569`, `0x020c → 0x0230`) and resolves `InitOk₀.noSession` to `ans = .ok none`. -/
theorem stage1_load_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st1 : M.σ} {stk : Nat} {s0 sAS : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsPoll : FitsEnv M lim st1
      (eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 (sAS.readReg64 .x0))))
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hfs0 : s0.fs.files = x.F)
    (hctrlAS : InInitiatePlaced s0 sAS 0x020c)
    (htrAS' : sAS.trace = s0.trace)
    (hvtAS : sAS.readReg64 (.gpr 1#5) = lsρ sessLoadFutVtSym)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAP : State) (evs2 : List AllocEvent) (m0 m1 m2 m3 m4 m5 : BitVec 64),
      eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 (sAS.readReg64 .x0)) evs2 →
      InInitiatePlaced s0 sAP 0x0230 →
      sAP.trace = s0.trace →
      sAP.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAP
        (afterLoadPollMemPlaced A lim (M.stepEvents evs2 st1) x stk s0 sAP
          (sAS.readReg64 .x0) m0 m1 m2 m3 m4 m5) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAS
      (afterLoadShimMemPlaced A lim st1 x stk s0 sAS) Q Qp oom := by
  have hpcAS : sAS.pc = (blkPl_521).base + 524#64 := hctrlAS.pc
  have hrunAS := hctrlAS.run; have hspAS' := hctrlAS.sp
  have hfpAS := hctrlAS.fp; have hx19AS := hctrlAS.x19; have hfsAS' := hctrlAS.files0
  have hinvAS := hctrlAS.inv; have hvregsAS := hctrlAS.vregs; have hal0 := hctrlAS.spAligned
  have halAS := spAligned_of_frame hal0 hspAS'
  unfold afterLoadShimMemPlaced; dsimp only
  dsimp only [sessLoadPollGhostOf] at hFitsPoll hnext
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAS' hFitsPoll hnext ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAS'] using halAS
  rw [load_frame_5ba_split fsp]
  repeat rw [sepConj_assoc]
  refine sepWPp_exists_pos2 fun f0 => ?_
  refine sepWPp_exists_pos3 fun f1 => ?_
  let futPtr := sAS.readReg64 .x0
  have hx1AS : sAS.readReg64 (.gpr 1#5) = lsρ sessLoadFutVtSym := hvtAS
  refine sepWPp_with_rodata (rodata_sessLoadFut_poll_placed' hinvAS) ?_
  generalize hpollA : lsmpl.base 569 = pollAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed pollAddr hinvAS ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sPoll hsPoll hpcP hrunP hinvP hvmP
    subst hpollA
    refine sepWPp_drop_left ?_
    have hspP : sPoll.sp = fsp := by rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']
    have hx0P : sPoll.readReg64 .x0 = futPtr := by
      rw [← hsPoll]; simp [futPtr, wp_norm, arm64_norm]
    have hx8P : sPoll.readReg64 .x8 = fsp + 0x1600#64 := by
      rw [← hsPoll]; simp [wp_norm, arm64_norm]; try bv_omega
    have hx20P : sPoll.readReg64 (.gpr 20#5) = fsp + 0x1600#64 := by
      rw [← hsPoll]; simp [wp_norm, arm64_norm]; try bv_omega
    have hlrP : sPoll.readReg64 .lr = initPcPlaced 0x0230 := by
      rw [← hsPoll]
      change _ = (blkPl_521).base + 560#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hfpP : sPoll.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsPoll]; simp [wp_norm, arm64_norm, hfpAS]
    have hx19P : sPoll.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsPoll]; simp [wp_norm, arm64_norm, hx19AS]
    have hvregsP : calleeSavedVRegs sPoll = calleeSavedVRegs s0 := by
      rw [← hsPoll]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAS]
    have htrP : sPoll.trace = s0.trace := by rw [← hsPoll]; simp [wp_norm, arm64_norm, htrAS']
    have hfsP : sPoll.fs.files = s0.fs.files := by
      rw [← hsPoll]; simp [wp_norm, arm64_norm, hfsAS']
    clear hsPoll
    have halP : sPoll.spAligned = true := spAligned_of_sp_eq halAS (hspP.trans hspAS'.symm)
    have hpoolP : A.pool lim st1 sAS = A.pool lim st1 sPoll := (A.pool_of_vmPreserved hvmP).symm
    rw [hpoolP]
    try rw [hspAS']
    try rw [hx1AS]
    let pollGhost : SessLoadPollGhost :=
      { call := { fut := futPtr, out := fsp + 0x1600#64, addr := x.peer, addrA := x.peerA }
        self := x.stores + 0xf0#64
        dir := StoresGhost.opened.sessions }
    have hFitsPollP : FitsEnv M lim st1 (eEnvs.sessLoadPoll sPoll.fs.files pollGhost) := by
      rw [hfsP, hfs0]
      exact hFitsPoll
    have hsessGet : ∀ bs,
        StoresGhost.opened.sessions.get cliIo.rd sPoll.fs.files (addressText x.peer.val) = .ok bs →
        SessFileWf (fun _ => False) bs := by
      intro bs hbs
      rw [hfsP, hfs0, hinitOk.noSession] at hbs
      cases hbs
      exact sessFileWf_false_of_nil
    let pollFrame : SepProp :=
      A.live futPtr 24 8 ∗
        dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessLoadFutVtSym) ∗
        memRegion (fsp + 0x5d0#64) 40 ∗
        memRegion (fsp + 0x5f8#64) 312 ∗
        memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770)
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sPoll _ Q Qp oom
    refine initCallLscro hh hpanic hStore.sessLoadPoll (gx := (pollGhost, st1)) (F := pollFrame)
      hpcP hrunP halP hinvP htrP hfsP hlrP ?_ (fun _ => false_entails _) ?_
    · dsimp only [pollFrame, pollGhost, futPtr, Reg.x0]
      unfold storesAt
      rw [hspP]
      repeat rw [sepConj_assoc]
      refine pure_sepConj_intro
        ⟨hx0P, hx8P, hinitOk.nameLt, hinitOk.textLt, by
          dsimp only [StoresGhost.opened, DirGhost.new]
          have h := hinitOk.sessPathLt; unfold pathOf at h
          split at h
          · rename_i heq; rw [heq]; dsimp; omega
          · simp only [List.length_append] at h; omega,
          ⟨hinitOk.sessPathOk, hinitOk.sessPathLt⟩, hsessGet, hFitsPollP⟩ ?_
      sep_frame
    intro sAP hpcAP hrunAP hspAP hcsAP hinvAP hfsAP
    dsimp only [pollGhost, pollFrame]
    refine sepWPp_exists_left fun evs2 => ?_
    rw [sepConj_assoc]
    refine sepWPp_exists_left fun gr => ?_
    refine sepWPp_exists_left fun ans => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun ⟨⟨hgr, htrAP⟩, hans, hevs2⟩ => ?_
    have htrAP' : sAP.trace = s0.trace := htrAP.trans htrP
    have hfsAP' : sAP.fs.files = s0.fs.files := hfsAP htrAP'
    have hspAP' : sAP.sp = fsp := hspAP.trans hspP
    have hx20AP : sAP.readReg64 (.gpr 20#5) = fsp + 0x1600#64 := (cs_x20 hcsAP).trans hx20P
    rw [hfsP, hfs0] at hgr hevs2
    have hansNone : ans = .ok none := by
      rw [hinitOk.noSession] at hgr
      subst hgr
      exact hans
    rw [hansNone]
    dsimp only [sessLoadOutAt]
    have h360 : memRegion (fsp + 0x1600#64 + 8#64) 360 =
        memRegion (fsp + 0x1608#64) 48 ∗ memRegion (fsp + 0x1638#64) 312 := by
      rw [show (360 : Nat) = 48 + 312 by decide, memRegion_split _ 48 312 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [h360, sepConj_assoc, sepConj_assoc, memRegion_48_words (fsp + 0x1608#64)]
    refine sepWPp_exists_pos2 fun m5 => ?_; refine sepWPp_exists_pos2 fun m4 => ?_
    refine sepWPp_exists_pos2 fun m3 => ?_; refine sepWPp_exists_pos2 fun m2 => ?_
    refine sepWPp_exists_pos2 fun m1 => ?_; refine sepWPp_exists_pos2 fun m0 => ?_
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hctrlAP : InInitiatePlaced s0 sAP 0x0230 :=
      ⟨hpcAP, hrunAP, hspAP'.trans hfsp.symm, (cs_fp hcsAP).trans hfpP,
        (cs_x19 hcsAP).trans hx19P, hfsAP', hinvAP, (cs_vregs hcsAP).trans hvregsP, hal0⟩
    refine sepWPp_mono_pre
      (P' := afterLoadPollMemPlaced A lim (M.stepEvents evs2 st1) x stk s0 sAP futPtr
        m0 m1 m2 m3 m4 m5)
      (by unfold afterLoadPollMemPlaced; dsimp only; rw [hspP, ← hfsp]; sep_frame) ?_
    exact hnext sAP evs2 m0 m1 m2 m3 m4 m5 hevs2 hctrlAP htrAP' hx20AP)

/-! ## `memcpy(312)` (`0x0230 → 0x02f0`) -/

set_option maxHeartbeats 1600000 in
/-- Steps `0x0230 → 0x02f0` across `memcpy(fsp + 0x5f8, fsp + 0x1638, 312)` while transporting `A.pool`. -/
theorem stage1_load_memcpy_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st2 : M.σ} {stk : Nat} {s0 sAP : State}
    {futPtr m0 m1 m2 m3 m4 m5 : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrlAP : InInitiatePlaced s0 sAP 0x0230)
    (htrAP' : sAP.trace = s0.trace)
    (hx20AP : sAP.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAM : State,
      InInitiatePlaced s0 sAM 0x02f0 →
      sAM.trace = s0.trace →
      sAM.readReg64 (.gpr 22#5) = 0#64 - 1#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAM
        (afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAM futPtr) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAP
      (afterLoadPollMemPlaced A lim st2 x stk s0 sAP futPtr m0 m1 m2 m3 m4 m5) Q Qp oom := by
  have hpcAP : sAP.pc = (blkPl_521).base + 560#64 := hctrlAP.pc
  have hrunAP := hctrlAP.run; have hspAP' := hctrlAP.sp
  have hfpAP := hctrlAP.fp; have hx19AP := hctrlAP.x19; have hfsAP' := hctrlAP.files0
  have hinvAP := hctrlAP.inv; have hvregsAP := hctrlAP.vregs; have hal0 := hctrlAP.spAligned
  have halAP := spAligned_of_frame hal0 hspAP'
  unfold afterLoadPollMemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAP' hx20AP ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAP'] using halAP
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed (lsρ memcpyName) hinvAP ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sMc hsMc hpcM hrunM hinvM hvmM
    have hspM : sMc.sp = fsp := by rw [← hsMc]; simp [wp_norm, arm64_norm, hspAP']
    have hx0M : sMc.readReg64 .x0 = fsp + 0x5f8#64 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm]; try bv_omega
    have hx1M : sMc.readReg64 .x1 = fsp + 0x1638#64 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm]; try bv_omega
    have hx2M : (sMc.readReg64 .x2).toNat = 312 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm]
    have hx22M : sMc.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm]
    have hlrM : sMc.readReg64 .lr = initPcPlaced 0x02f0 := by
      rw [← hsMc]
      change _ = (blkPl_521).base + 752#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hfpM : sMc.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm, hfpAP]
    have hx19M : sMc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsMc]; simp [wp_norm, arm64_norm, hx19AP]
    have hvregsM : calleeSavedVRegs sMc = calleeSavedVRegs s0 := by
      rw [← hsMc]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAP]
    have htrM : sMc.trace = s0.trace := by rw [← hsMc]; simp [wp_norm, arm64_norm, htrAP']
    have hfsM : sMc.fs.files = s0.fs.files := by
      rw [← hsMc]; simp [wp_norm, arm64_norm, hfsAP']
    clear hsMc
    have halM : sMc.spAligned = true := spAligned_of_sp_eq halAP (hspM.trans hspAP'.symm)
    have hpoolM : A.pool lim st2 sAP = A.pool lim st2 sMc := (A.pool_of_vmPreserved hvmM).symm
    rw [hpoolM]
    have hmcCall := init_memcpyScratch_vm_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) (n := 312) hh hstk hstk64
    have hpcM' : sMc.pc = lsρ memcpyName := hpcM
    have h56 :
        ((fsp + 5632#64) ↦₆₄ (0#64 - 1#64)) ∗
          ((fsp + 5640#64) ↦₆₄ m0) ∗ ((fsp + 5648#64) ↦₆₄ m1) ∗
          ((fsp + 5656#64) ↦₆₄ m2) ∗ ((fsp + 5664#64) ↦₆₄ m3) ∗
          ((fsp + 5672#64) ↦₆₄ m4) ∗ ((fsp + 5680#64) ↦₆₄ m5) ⊢
          memRegion (fsp + 0x1600#64) 56 := by
      have hm0 : ((fsp + 0x1600#64) ↦₆₄ (0#64 - 1#64)) ⊢ memRegion (fsp + 0x1600#64) 8 := by
        rw [ProofLib.memRegion_eight]
        exact Entails.sepExists_right _ (Entails.refl _)
      have hm48 :
          ((fsp + 5640#64) ↦₆₄ m0) ∗ ((fsp + 5648#64) ↦₆₄ m1) ∗
            ((fsp + 5656#64) ↦₆₄ m2) ∗ ((fsp + 5664#64) ↦₆₄ m3) ∗
            ((fsp + 5672#64) ↦₆₄ m4) ∗ ((fsp + 5680#64) ↦₆₄ m5) ⊢
            memRegion (fsp + 0x1608#64) 48 := by
        rw [memRegion_48_words (fsp + 0x1608#64)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        sep_frame
      rw [show memRegion (fsp + 0x1600#64) 56 =
            memRegion (fsp + 0x1600#64) 8 ∗ memRegion (fsp + 0x1608#64) 48 from by
          rw [show (56 : Nat) = 8 + 48 by decide, memRegion_split _ 8 48 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]]
      exact sepConj_mono hm0 hm48
    let mcFrame : SepProp :=
      memRegion (fsp + 0x1600#64) 56 ∗
        A.live futPtr 24 8 ∗
        sessLoadBoxAt futPtr (x.stores + 0xf0#64) x.peerA 1#8 ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ A.pool lim st2 sMc ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ sessLoadFutVtSym) ∗
        memRegion (fsp + 0x5d0#64) 40 ∗
        memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770)
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sMc _ Q Qp oom
    refine initCallLscro hh hpanic hmcCall (gx := (fsp + 0x5f8#64, fsp + 0x1638#64)) (F := mcFrame)
      hpcM' hrunM halM hinvM htrM hfsM hlrM ?_ (fun _ => false_entails _) ?_
    · dsimp only [mcFrame]
      unfold withVmPreserved memcpyScratchSpec storesAt
      dsimp only
      rw [hspM]
      repeat rw [sepConj_assoc]
      refine pure_sepConj_intro ⟨hx0M, hx1M, hx2M⟩ ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56))))
      sep_frame
    intro sAM hpcAM hrunAM hspAM hcsAM hinvAM hfsAM
    unfold withVmPreserved memcpyScratchSpec; dsimp only [mcFrame]
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun hvmMc => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun htrAM => ?_
    have htrAM' : sAM.trace = s0.trace := htrAM.trans htrM
    have hfsAM' : sAM.fs.files = s0.fs.files := hfsAM htrAM'
    have hspAM' : sAM.sp = fsp := hspAM.trans hspM
    have hx22AM : sAM.readReg64 (.gpr 22#5) = 0#64 - 1#64 := (cs_x22 hcsAM).trans hx22M
    have hpoolAM : A.pool lim st2 sMc = A.pool lim st2 sAM := (A.pool_of_vmPreserved hvmMc).symm
    rw [hpoolAM]
    have hctrlAM : InInitiatePlaced s0 sAM 0x02f0 :=
      ⟨hpcAM, hrunAM, hspAM'.trans hfsp.symm, (cs_fp hcsAM).trans hfpM,
        (cs_x19 hcsAM).trans hx19M, hfsAM', hinvAM, (cs_vregs hcsAM).trans hvregsM, hal0⟩
    refine sepWPp_mono_pre
      (P' := afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAM futPtr)
      (by unfold afterLoadMemcpyMemPlaced; dsimp only; rw [hspM, ← hfsp]; sep_frame) ?_
    exact hnext sAM hctrlAM htrAM' hx22AM)

/-! ## Optional `futDrop`, `dealloc`, and handoff (`0x02f0 → 0x0390`) -/

set_option maxHeartbeats 1600000 in
/-- `__rust_dealloc(futPtr, 24, 8)` and `stage2MemPlaced` packing (`0x0308 → 0x031c`). -/
theorem stage1_load_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st2 : M.σ} {stk : Nat} {s0 sAD : State}
    {futPtr : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hal0 : s0.spAligned = true)
    (hpcAD : sAD.pc = (blkPl_521).base + 776#64)
    (hrunAD : sAD.status = .Running)
    (hspAD' : sAD.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hx20AD : sAD.readReg64 (.gpr 20#5) = futPtr)
    (hx22AD : sAD.readReg64 (.gpr 22#5) = 0#64 - 1#64)
    (hx23AD : sAD.readReg64 (.gpr 23#5) = lsρ sessLoadFutVtSym)
    (hfpAD : sAD.readReg64 .fp = s0.sp - 0x60#64)
    (hx19AD : sAD.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hvregsAD : calleeSavedVRegs sAD = calleeSavedVRegs s0)
    (htrAD' : sAD.trace = s0.trace)
    (hfsAD' : sAD.fs.files = s0.fs.files)
    (hinvAD : LibsignalCodeRoLoaded lsmpl sAD.mem)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAF : State,
      InInitiatePlaced s0 sAF 0x031c →
      sAF.trace = s0.trace →
      sAF.readReg64 (.gpr 22#5) = 0#64 - 1#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAF
        (stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 24 8) st2) x stk s0 sAF)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAD
      (afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAD futPtr) Q Qp oom := by
  have halAD := spAligned_of_frame hal0 hspAD'
  unfold afterLoadMemcpyMemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAD' ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAD'] using halAD
  refine sepWPp_with_rodata (rodata_sessLoadFut_size_placed' hinvAD) ?_
  refine sepWPp_with_rodata (rodata_sessLoadFut_align_placed' hinvAD) ?_
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed (lsρ lsRustDeallocSymCli) hinvAD ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro sF hsF hpcF hrunF hinvF hvmF
    refine sepWPp_drop_left (sepWPp_drop_left ?_)
    have hspF : sF.sp = fsp := by rw [← hsF]; simp [wp_norm, arm64_norm, hspAD']
    have hx0F : sF.readReg64 .x0 = futPtr := by rw [← hsF]; simp [wp_norm, arm64_norm]
    have hx1F : (sF.readReg64 .x1).toNat = 24 := by rw [← hsF]; simp [wp_norm, arm64_norm]
    have hx2F : (sF.readReg64 .x2).toNat = 8 := by rw [← hsF]; simp [wp_norm, arm64_norm]
    have hx22F : sF.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
      rw [← hsF]; simp [wp_norm, arm64_norm, hx22AD]
    have hlrF : sF.readReg64 .lr = initPcPlaced 0x031c := by
      rw [← hsF]
      change _ = (blkPl_521).base + 796#64
      simp [wp_norm, arm64_norm]; try bv_omega
    have hfpF : sF.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsF]; simp [wp_norm, arm64_norm, hfpAD]
    have hx19F : sF.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsF]; simp [wp_norm, arm64_norm, hx19AD]
    have hvregsF : calleeSavedVRegs sF = calleeSavedVRegs s0 := by
      rw [← hsF]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAD]
    have htrF : sF.trace = s0.trace := by rw [← hsF]; simp [wp_norm, arm64_norm, htrAD']
    have hfsF : sF.fs.files = s0.fs.files := by rw [← hsF]; simp [wp_norm, arm64_norm, hfsAD']
    clear hsF
    have halF : sF.spAligned = true := spAligned_of_sp_eq halAD (hspF.trans hspAD'.symm)
    have hpoolF : A.pool lim st2 sAD = A.pool lim st2 sF := (A.pool_of_vmPreserved hvmF).symm
    rw [hpoolF]
    have hdealloc := init_dealloc_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
    have hpcF' : sF.pc = lsρ lsRustDeallocSymCli := hpcF
    let frameNoPool : SepProp :=
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        lsLogOff ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sF _ Q Qp oom
    refine initCallLscro hh hpanic hdealloc (gx := (futPtr, 24, 8, st2)) (F := frameNoPool)
      hpcF' hrunF halF hinvF htrF hfsF hlrF ?_ (fun _ => false_entails _) ?_
    · dsimp only [frameNoPool]
      unfold rustCliDeallocBudgetExternSpecWithStack
      dsimp only
      rw [hspF]
      have hboxMem := sessLoadBoxAt_entails_memRegion futPtr (x.stores + 0xf0#64) x.peerA 1#8
      have h368 : memRegion (fsp + 0x1600#64) 56 ∗ memRegion (fsp + 0x1638#64) 312 =
          memRegion (fsp + 0x1600#64) 368 :=
        memRegion_merge (fsp + 0x1600#64) (fsp + 0x1638#64) 56 312 368
          (by bv_omega) (by decide) (by decide)
      have hmergeLoad368 :
          memRegion (fsp + 0x5ba#64) 6 ∗
            ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
            ((fsp + 0x5c8#64) ↦₆₄ lsρ sessLoadFutVtSym) ∗
            memRegion (fsp + 0x5d0#64) 40 ∗
            memRegion (fsp + 0x5f8#64) 312 ∗
            memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
            (memRegion (fsp + 0x1600#64) 56 ∗ memRegion (fsp + 0x1638#64) 312) ∗
            memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770) ⊢
            memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
        rw [h368]
        exact load_frame_5ba_merge fsp futPtr (lsρ sessLoadFutVtSym)
      repeat rw [sepConj_assoc]
      refine pure_sepConj_intro
        ⟨hx0F, hx1F, hx2F, ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩,
          by rw [hlrF]; exact lsRetAddr624_blockPlacement_base_add 521 _ (by decide) (by decide)⟩ ?_
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hboxMem (sepConj_mono_right (sepConj_mono_left hmergeLoad368)))))
      sep_frame
    intro sAF hpcAF hrunAF hspAF hcsAF hinvAF hfsAF
    unfold rustCliDeallocBudgetExternSpecWithStack; dsimp only
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun htrAF => ?_
    have htrAF' : sAF.trace = s0.trace := htrAF.trans htrF
    have hfsAF' : sAF.fs.files = s0.fs.files := hfsAF htrAF'
    have hspAF' : sAF.sp = fsp := hspAF.trans hspF
    have hx22AF : sAF.readReg64 (.gpr 22#5) = 0#64 - 1#64 := (cs_x22 hcsAF).trans hx22F
    have hctrlAF : InInitiatePlaced s0 sAF 0x031c :=
      ⟨hpcAF, hrunAF, hspAF'.trans hfsp.symm, (cs_fp hcsAF).trans hfpF,
        (cs_x19 hcsAF).trans hx19F, hfsAF', hinvAF, (cs_vregs hcsAF).trans hvregsF, hal0⟩
    refine sepWPp_mono_pre
      (P' := stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 24 8) st2) x stk s0 sAF)
      (by unfold stage2MemPlaced; dsimp only [frameNoPool]; rw [hspF, ← hfsp]; sep_frame) ?_
    exact hnext sAF hctrlAF htrAF' hx22AF)

set_option maxHeartbeats 1600000 in
/-- Optional `futDrop` and `__rust_dealloc(24, 8)` (`0x02f0 → 0x031c`). -/
theorem stage1_load_drop_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st2 : M.σ} {stk : Nat} {s0 sAM : State}
    {futPtr : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrlAM : InInitiatePlaced s0 sAM 0x02f0)
    (htrAM' : sAM.trace = s0.trace)
    (hx22AM : sAM.readReg64 (.gpr 22#5) = 0#64 - 1#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAF : State,
      InInitiatePlaced s0 sAF 0x031c →
      sAF.trace = s0.trace →
      sAF.readReg64 (.gpr 22#5) = 0#64 - 1#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAF
        (stage2MemPlaced A lim (M.stepEvents (rustDeallocEvents 24 8) st2) x stk s0 sAF)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAM
      (afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAM futPtr) Q Qp oom := by
  have hpcAM : sAM.pc = (blkPl_521).base + 752#64 := hctrlAM.pc
  have hrunAM := hctrlAM.run; have hspAM' := hctrlAM.sp
  have hfpAM := hctrlAM.fp; have hx19AM := hctrlAM.x19; have hfsAM' := hctrlAM.files0
  have hinvAM := hctrlAM.inv; have hvregsAM := hctrlAM.vregs; have hal0 := hctrlAM.spAligned
  have halAM := spAligned_of_frame hal0 hspAM'
  have hfspAl : ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAM'] using halAM
  refine sepWPp_with_rodata (rodata_sessLoadFut_drop_placed' hinvAM) ?_
  by_cases hdz0 : lsmpl.base 547 = 0#64
  · rw [hdz0]
    unfold afterLoadMemcpyMemPlaced; dsimp only
    generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAM' hfspAl ⊢
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    refine sepWPp_step_to_vm_placed ((blkPl_521).base + 776#64) hinvAM ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro sAD hsAD hpcAD hrunAD hinvAD hvmAD
      refine sepWPp_drop_left ?_
      have hspAD : sAD.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
        rw [← hsAD, hfsp]; simp [wp_norm, arm64_norm, hspAM']
      have hx20AD : sAD.readReg64 (.gpr 20#5) = futPtr := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx22AD : sAD.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hx22AM]
      have hx23AD : sAD.readReg64 (.gpr 23#5) = lsρ sessLoadFutVtSym := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hfpAD : sAD.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfpAM]
      have hx19AD : sAD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hx19AM]
      have hvregsAD : calleeSavedVRegs sAD = calleeSavedVRegs s0 := by
        rw [← hsAD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAM]
      have htrAD : sAD.trace = s0.trace := by rw [← hsAD]; simp [wp_norm, arm64_norm, htrAM']
      have hfsAD : sAD.fs.files = s0.fs.files := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfsAM']
      clear hsAD
      have hpoolAD : A.pool lim st2 sAM = A.pool lim st2 sAD :=
        (A.pool_of_vmPreserved hvmAD).symm
      rw [hpoolAD, ← hfsp]
      exact stage1_load_dealloc_placed_ok hh hstk hstk64 hal0
        hpcAD hrunAD hspAD hx20AD hx22AD hx23AD hfpAD hx19AD hvregsAD htrAD hfsAD hinvAD
        hpanic hnext)
  · have hdz : (lsmpl.base 547 == 0#64) = false := beq_eq_false_iff_ne.2 hdz0
    generalize hdropA : lsmpl.base 547 = dropAddr at hdz ⊢
    unfold afterLoadMemcpyMemPlaced; dsimp only
    generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAM' hfspAl ⊢
    dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    refine sepWPp_step_to_vm_placed dropAddr hinvAM ?_
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm])
      intro sDrop hsDrop hpcD hrunD hinvD hvmD
      subst hdropA
      refine sepWPp_drop_left ?_
      have hspD : sDrop.sp = fsp := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hspAM']
      have hx20D : sDrop.readReg64 (.gpr 20#5) = futPtr := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hx22D : sDrop.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hx22AM]
      have hx23D : sDrop.readReg64 (.gpr 23#5) = lsρ sessLoadFutVtSym := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hlrD : sDrop.readReg64 .lr = initPcPlaced 0x0308 := by
        rw [← hsDrop]
        change _ = (blkPl_521).base + 776#64
        simp [wp_norm, arm64_norm]; try bv_omega
      have hfpD : sDrop.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hfpAM]
      have hx19D : sDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hx19AM]
      have hvregsD : calleeSavedVRegs sDrop = calleeSavedVRegs s0 := by
        rw [← hsDrop]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAM]
      have htrD : sDrop.trace = s0.trace := by rw [← hsDrop]; simp [wp_norm, arm64_norm, htrAM']
      have hfsD : sDrop.fs.files = s0.fs.files := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm, hfsAM']
      clear hsDrop
      have halD : sDrop.spAligned = true := spAligned_of_sp_eq halAM (hspD.trans hspAM'.symm)
      rw [← hfsp]
      change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sDrop
        (afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAM futPtr) Q Qp oom
      refine initCallLscro hh hpanic hStore.futDrop (gx := ())
        (F := afterLoadMemcpyMemPlaced A lim st2 x stk s0 sAM futPtr)
        hpcD hrunD halD hinvD htrD hfsD hlrD
        (by unfold futDropBudgetSpec; rw [emp_sepConj]; exact Entails.refl _)
        (fun _ => false_entails _) ?_
      intro sAD hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
      unfold futDropBudgetSpec; dsimp only
      refine sepWPp_pure_elim fun ⟨htrAD, hvmCall⟩ => ?_
      have htrAD' : sAD.trace = s0.trace := htrAD.trans htrD
      have hvmAD : VmPreserved sAM sAD := hvmD.trans hvmCall
      rw [afterLoadMemcpyMemPlaced_of_vmPreserved A lim st2 x stk s0 futPtr hvmAD]
      exact stage1_load_dealloc_placed_ok hh hstk hstk64 hal0
        hpcAD hrunAD ((hspAD.trans hspD).trans hfsp.symm)
        ((cs_x20 hcsAD).trans hx20D) ((cs_x22 hcsAD).trans hx22D)
        ((cs_x23 hcsAD).trans hx23D) ((cs_fp hcsAD).trans hfpD)
        ((cs_x19 hcsAD).trans hx19D) ((cs_vregs hcsAD).trans hvregsD)
        htrAD' (hfsAD htrAD') hinvAD hpanic hnext)

set_option maxHeartbeats 1200000 in
/-- Steps `0x031c → 0x0380 → 0x0390` (`x22 = -1`) to establish `AtStage2Placed` and `stage2MemPlaced`. -/
theorem stage1_load_handoff_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {x : InitGhost} {be : PreKeyBundleFields} {st3 : M.σ} {stk : Nat} {s0 sAF : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hbe : bundleEOf? x.bundle = some be)
    (hfs0 : s0.fs.files = x.F)
    (hctrlAF : InInitiatePlaced s0 sAF 0x031c)
    (htrAF' : sAF.trace = s0.trace)
    (hx22AF : sAF.readReg64 (.gpr 22#5) = 0#64 - 1#64)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hsigs : PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true)
    (hnext : ∀ (s4 : State) (be' : PreKeyBundleFields),
      AtStage2Placed W X x be' s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage2MemPlaced A lim st3 x stk s0 s4) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAF
      (stage2MemPlaced A lim st3 x stk s0 sAF) Q Qp oom := by
  have hpcAF : sAF.pc = (blkPl_521).base + 796#64 := hctrlAF.pc
  have hrunAF := hctrlAF.run; have hspAF' := hctrlAF.sp
  have hfpAF := hctrlAF.fp; have hx19AF := hctrlAF.x19; have hfsAF' := hctrlAF.files0
  have hinvAF := hctrlAF.inv; have hvregsAF := hctrlAF.vregs; have hal0 := hctrlAF.spAligned
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed ((blkPl_521).base + 912#64) hinvAF ?_
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm])
    intro s4 hs4 hpc4 hrun4 hinv4 hvm4
    have hsp4 : s4.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [← hs4]; simp [wp_norm, arm64_norm, hspAF']
    have hfp4 : s4.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hs4]; simp [wp_norm, arm64_norm, hfpAF]
    have hx19_4 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hs4]; simp [wp_norm, arm64_norm, hx19AF]
    have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
      rw [← hs4]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAF]
    have htr4 : s4.trace = s0.trace := by rw [← hs4]; simp [wp_norm, arm64_norm, htrAF']
    have hfs40 : s4.fs.files = s0.fs.files := by rw [← hs4]; simp [wp_norm, arm64_norm, hfsAF']
    have hfs4F : s4.fs.files = x.F := hfs40.trans hfs0
    have hx22_4 : s4.readReg64 (.gpr 22#5) = 0#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
    have hx23_4 :
        s4.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64 := by
      rw [← hs4]; simp [wp_norm, arm64_norm]
    have hx25_4 : s4.readReg64 (.gpr 25#5) = 0xFFFFFFFFFFFFFFFF#64 := by
      rw [← hs4]; simp [wp_norm, arm64_norm]
    have hx26_4 : s4.readReg64 (.gpr 26#5) = 8#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
    have hx27_4 : s4.readReg64 (.gpr 27#5) = 0#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
    clear hs4
    rw [stage2MemPlaced_of_vmPreserved A lim st3 x stk s0 hvm4]
    have hctrl4 : InInitiatePlaced s0 s4 0x0390 :=
      ⟨hpc4, hrun4, hsp4, hfp4, hx19_4, hfs40, hinv4, hvregs4, hal0⟩
    exact hnext s4 be
      ⟨hctrl4, htr4, hfs4F, hx8, hbe, htrust, hsigs, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4⟩)

/-! ## Full Segment 4 composition (`0x01fc → 0x0390`) -/

/-- Budget-threaded `load_session(peer)` to `AtStage2Placed` (`0x01fc → 0x0390`). -/
theorem stage1_load_session_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {st0 st : M.σ} {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 24))
    (hFitsPoll : ∀ (evs1 : List AllocEvent) (futPtr : BitVec 64),
      BoxAllocEnv 24 evs1 → futPtr ≠ 0#64 → futPtr.toNat % 8 = 0 →
      FitsEnv M lim (M.stepEvents evs1 st)
        (eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futPtr)))
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hbe : bundleEOf? x.bundle = some be)
    (hctrl : InInitiatePlaced s0 s3 0x01fc)
    (htr : s3.trace = s0.trace)
    (hfs : s3.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hsigs : PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (be' : PreKeyBundleFields) (evs1 evs2 : List AllocEvent)
      (futPtr : BitVec 64),
      BoxAllocEnv 24 evs1 →
      futPtr ≠ 0#64 →
      futPtr.toNat % 8 = 0 →
      eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futPtr) evs2 →
      AtStage2Placed W X x be' s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage2MemPlaced A lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 24 8) st) x stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage2MemPlaced A lim st x stk s0 s3) Q Qp oom := by
  have hfs0 : s0.fs.files = x.F := hctrl.files0.symm.trans hfs
  exact stage1_load_to_poll_placed_ok hh hStore hFitsShim hctrl htr hpanic
    fun sAS evs1 hevs1 hfutNZ hfutAl hctrlAS htrAS' hvtAS =>
      stage1_load_poll_placed_ok hh hStore
        (hFitsPoll evs1 (sAS.readReg64 .x0) hevs1 hfutNZ hfutAl)
        hinitOk hfs0 hctrlAS htrAS' hvtAS hpanic
        fun sAP evs2 m0 m1 m2 m3 m4 m5 hevs2 hctrlAP htrAP' hx20AP =>
          stage1_load_memcpy_placed_ok hh hstk hstk64 hctrlAP htrAP' hx20AP hpanic
            fun sAM hctrlAM htrAM' hx22AM =>
              stage1_load_drop_dealloc_placed_ok hh hStore hstk hstk64 hctrlAM htrAM' hx22AM hpanic
                fun sAF hctrlAF htrAF' hx22AF => by
                  rw [← M.stepEvents_append evs2 (rustDeallocEvents 24 8) (M.stepEvents evs1 st),
                    ← M.stepEvents_append evs1 (evs2 ++ rustDeallocEvents 24 8) st,
                    ← List.append_assoc]
                  exact stage1_load_handoff_placed_ok hx8 hbe hfs0 hctrlAF htrAF' hx22AF htrust
                    hsigs fun s4 be' hAt2 =>
                      hnext s4 be' evs1 evs2 (sAS.readReg64 .x0) hevs1 hfutNZ hfutAl hevs2 hAt2

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget
