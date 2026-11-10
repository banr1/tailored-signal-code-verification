/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
meta import Lean -- shake: keep

/-!
# Budget-Threaded Stage 1 Segment 1 Prefix (`0x0000 → 0x00b8`): Prologue, `idTrustShim`, and `idTrustPoll`

Defines the budget-threaded cut assertions `initEntryMemPlaced'`, `afterTrustShimMemPlaced`, and
`afterTrustPollMemPlaced` and proves `stage1_prologue_to_shim_placed_ok` (`0x0000 → 0x009c`) and
`stage1_trust_to_poll_placed_ok` (`0x009c → 0x00b8`) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPC_521 blkPl_521 lsProg_521)
open CryptoVerification.LibsignalPublicApi.StoreKit (IdentityShimCall trustPollOutAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdFileWf IdPollGhost StoresGhost dirAt idTrustBoxAt idTrustFutVtSym idTrustOf
   idTrustOutAt idTrustOutAt_ok pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced InInitiatePlaced coinsCursorAtPlaced coinsInstalledPlaced_eq_cursorZero
   initArgsAtPlaced initLocalsSize initPcPlaced initProgExtPlaced initProgPlaced initSaved stk_ge_frame)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (bundleRestAt byte_and_pad7_entails_word64 cliBundleAt_unpack cliBundleBody
   cliBundleBody_pack cs_fp cs_vregs cs_x19 false_entails idTrust_always_ok memRegion_saved_split
   pointsTo16_zero_eq poll_frame_5ba_split prologue_high_5ba_merge_sp prologue_locals_split
   prologue_low_d0_merge_sp pure_sepConj_elim pure_sepConj_intro sepWPp_drop_left
   sepWPp_exists_left sepWPp_exists_pos2 sepWPp_exists_pos3 sepWPp_exists_pos4 sepWPp_mono_pre
   sepWPp_pure_elim sepWPp_with_rodata spAligned_of_frame spAligned_of_sp_eq sp_sub_4192_sub_3216
   sp_sub_96_add_96 sp_sub_96_sub_4096 stackAt_entry_split)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks vmPreserved_setPC vmPreserved_writeReg64)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayoutPlacedBudget
  (initCallLscro rodata_idTrustFut_poll_placed' rodata_idVt_trustSlot_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlacedBudget
  (sepWP_done_tpidr sepWPp_step_to_vm_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-! ## Spatial cut predicates and poll ghost constructor -/

/-- Spatial entry footprint of `DefsPlacedBudget.initSlotSpecPlaced` after extracting pure preconditions. -/
abbrev initEntryMemPlaced' [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    tokenInitPlacedAt ∗
    lsLogOff ∗ A.pool lim st s0 ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Spatial state at `0x009c` after `idTrustShim` returns. -/
abbrev afterTrustShimMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 sAfterShim : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    A.live (sAfterShim.readReg64 .x0) 32 8 ∗
    idTrustBoxAt (sAfterShim.readReg64 .x0) x.stores x.peerA (x.bundleA + 120#64) 0#8 0#8 ∗
    A.pool lim st sAfterShim ∗ stackAt fsp (stk - cliInitiateFrame) ∗
    storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    lsLogOff ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)

/-- Spatial state at `0x00b8` after `idTrustPoll` returns and its 48-byte `sret` is unpacked. -/
def afterTrustPollMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 sAfterPoll : State) (futPtr : BitVec 64) (opkId2 : BitVec 32)
    (w_tb o2 o3 o4 o5 : BitVec 64) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  (((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
      ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
      ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
      ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5)) ∗
    (idTrustBoxAt futPtr x.stores x.peerA (x.bundleA + 120#64) 1#8 0#8 ∗
      dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
      protocolAddressAt A.repAlloc x.peer x.peerA ∗
      ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      lsLogOff ∗ A.pool lim st sAfterPoll ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
    (A.live futPtr 32 8 ∗
      dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
      dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
      dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
      dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      tokenInitPlacedAt ∗
      bundleRestAt x opkId2 ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      initSaved s0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 6 ∗
      ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
      ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
      memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))

/-- `IdPollGhost` argument passed to `idTrustPoll` at `0x00b4`. -/
abbrev trustPollGhostOf (x : InitGhost) (s0 : State) (futPtr : BitVec 64) : IdPollGhost :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  { call := { fut := futPtr, out := fsp + 0x1600#64,
              call := { addr := x.peer, addrA := x.peerA,
                        key := x.bundle.idKey, keyA := x.bundleA + 120#64 } }
    self := x.stores
    peers := StoresGhost.opened.identity.peers }

/-! ## Prologue and `idTrustShim` (`0x0000 → 0x009c`) -/

private theorem sepWP_cut_vm {P : Program} {b mid tgt : BitVec 64}
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
  h.trans (by simp [vmPreserved_setPC, vmPreserved_writeReg64])

local syntax "init_vm_cut " term:max " , " term:max " => " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| init_vm_cut $mid:term , $hvm:term => $rest:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_cut_vm (mid := $mid) $hvm))
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
        throwError "init_vm_cut: inner tactic left {rem.length} unsolved goal(s)"
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2
      Lean.Elab.Tactic.setGoals savedGoals.tail!

set_option maxHeartbeats 1600000 in
/-- Budget-threaded prologue and `is_trusted_identity` shim call (`0x0000 → 0x009c`). -/
theorem stage1_prologue_to_shim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterShim : State) (evs1 : List AllocEvent)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      BoxAllocEnv 32 evs1 →
      sAfterShim.readReg64 .x0 ≠ 0#64 →
      (sAfterShim.readReg64 .x0).toNat % 8 = 0 →
      InInitiatePlaced s0 sAfterShim 0x009c →
      sAfterShim.trace = s0.trace →
      sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
        (afterTrustShimMemPlaced A lim (M.stepEvents evs1 st) x stk s0 sAfterShim) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced' A lim st x stk s0) Q Qp oom := by
  have hpc0 : s0.pc = (blkPl_521).base := hs0.pc
  have hrun0 := hs0.run; have hal0 := hs0.spAligned
  have hx0 := hs0.x0; have hx1 := hs0.x1; have hx2 := hs0.x2; have hx3 := hs0.x3
  have hx4 := hs0.x4; have hx5 := hs0.x5; have hx6 := hs0.x6; have hx7 := hs0.x7
  have hx8 := hs0.x8; have hfs0 := hs0.files
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  dsimp only [initEntryMemPlaced']
  rw [coinsInstalledPlaced_eq_cursorZero,
    stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (s0.sp - 0x60#64) 0x60 ∗
        memRegion fsp initLocalsSize ∗
        storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        lsLogOff ∗ A.pool lim st s0 ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by sep_frame) ?_
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨h1, h2, h3, hopk⟩ => ?_
  rw [memRegion_saved_split (s0.sp - 0x60#64)]
  refine sepWPp_exists_pos2 fun w11 => ?_; refine sepWPp_exists_pos2 fun w10 => ?_
  refine sepWPp_exists_pos2 fun w9 => ?_; refine sepWPp_exists_pos2 fun w8 => ?_
  refine sepWPp_exists_pos2 fun w7 => ?_; refine sepWPp_exists_pos2 fun w6 => ?_
  refine sepWPp_exists_pos2 fun w5 => ?_; refine sepWPp_exists_pos2 fun w4 => ?_
  refine sepWPp_exists_pos2 fun w3 => ?_; refine sepWPp_exists_pos2 fun w2 => ?_
  refine sepWPp_exists_pos2 fun w1 => ?_; refine sepWPp_exists_pos2 fun w0 => ?_
  refine sepWPp_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (prologue_locals_split fsp)))) ?_
  refine sepWPp_exists_pos3 fun l0 => ?_; refine sepWPp_exists_pos3 fun l80 => ?_
  refine sepWPp_exists_pos3 fun l88 => ?_; refine sepWPp_exists_pos3 fun l90 => ?_
  refine sepWPp_exists_pos3 fun l98 => ?_; refine sepWPp_exists_pos3 fun la0 => ?_
  refine sepWPp_exists_pos3 fun la8 => ?_; refine sepWPp_exists_pos3 fun lb0 => ?_
  refine sepWPp_exists_pos3 fun lb8 => ?_; refine sepWPp_exists_pos3 fun lc0 => ?_
  refine sepWPp_exists_pos3 fun lc8 => ?_
  refine sepWPp_exists_pos3 fun a0 => ?_; refine sepWPp_exists_pos3 fun a1 => ?_
  refine sepWPp_exists_pos3 fun a2 => ?_; refine sepWPp_exists_pos3 fun a3 => ?_
  refine sepWPp_exists_pos3 fun a4 => ?_; refine sepWPp_exists_pos3 fun a5 => ?_
  refine sepWPp_exists_pos3 fun a6 => ?_; refine sepWPp_exists_pos3 fun a7 => ?_
  refine sepWPp_exists_pos3 fun a8 => ?_; refine sepWPp_exists_pos3 fun a9 => ?_
  refine sepWPp_exists_pos3 fun a10 => ?_; refine sepWPp_exists_pos3 fun flag16 => ?_
  refine sepWPp_exists_pos3 fun wk0 => ?_; refine sepWPp_exists_pos3 fun wk1 => ?_
  refine sepWPp_exists_pos3 fun wk2 => ?_; refine sepWPp_exists_pos3 fun probe => ?_
  refine sepWPp_mono_pre (P' :=
      storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        lsLogOff ∗ A.pool lim st s0 ∗
        cliBundleBody x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
        ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
        ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
        ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
        ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
        ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ∗
        ((fsp + 0xd0#64) ↦₆₄ a0) ∗ ((fsp + 0xd8#64) ↦₆₄ a1) ∗
        ((fsp + 0xe0#64) ↦₆₄ a2) ∗ ((fsp + 0xe8#64) ↦₆₄ a3) ∗
        ((fsp + 0xf0#64) ↦₆₄ a4) ∗ ((fsp + 0xf8#64) ↦₆₄ a5) ∗
        ((fsp + 0x100#64) ↦₆₄ a6) ∗ ((fsp + 0x108#64) ↦₆₄ a7) ∗
        ((fsp + 0x110#64) ↦₃₂ a8) ∗ memRegion (fsp + 0x114#64) 4 ∗
        ((fsp + 0x118#64) ↦₆₄ a9) ∗ ((fsp + 0x120#64) ↦₆₄ a10) ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + 0x5ba#64) 30 ∗
        ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
        memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
        ((fsp + 0xc90#64) ↦₆₄ probe) ∗
        memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) ∗
        (((s0.sp - 0x60#64) + 0x00#64) ↦₆₄ w0) ∗ (((s0.sp - 0x60#64) + 0x08#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x60#64) + 0x10#64) ↦₆₄ w2) ∗ (((s0.sp - 0x60#64) + 0x18#64) ↦₆₄ w3) ∗
        (((s0.sp - 0x60#64) + 0x20#64) ↦₆₄ w4) ∗ (((s0.sp - 0x60#64) + 0x28#64) ↦₆₄ w5) ∗
        (((s0.sp - 0x60#64) + 0x30#64) ↦₆₄ w6) ∗ (((s0.sp - 0x60#64) + 0x38#64) ↦₆₄ w7) ∗
        (((s0.sp - 0x60#64) + 0x40#64) ↦₆₄ w8) ∗ (((s0.sp - 0x60#64) + 0x48#64) ↦₆₄ w9) ∗
        (((s0.sp - 0x60#64) + 0x50#64) ↦₆₄ w10) ∗ (((s0.sp - 0x60#64) + 0x58#64) ↦₆₄ w11))
    (by sep_frame) ?_
  simp (disch := decide) only
    [fsp, cliInitiateFrame, BitVec.add_zero, bv_sub_add_lit, Nat.reduceSub]
  refine sepWPp_with_rodata (rodata_idVt_trustSlot_placed hStore hs0.inv) ?_
  generalize hshimA : lsmpl.base 601 = shimAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_vm_placed shimAddr hs0.inv ?_
  init_vm_cut ((blkPl_521).base + 68#64) , (VmPreserved.refl s0) =>
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [arm64_norm, wp_norm], fun _hpc44 _hrun44 hvm44 => ?_⟩
    wp_step
    init_vm_cut shimAddr , (vmPreserved_adrp_step hvm44) =>
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by simp only [arm64_norm, wp_norm], fun hpcS0 hrunS0 hvmS0 =>
          SepWP.done hpcS0 hrunS0 ⟨hvmS0, ?_⟩⟩
      intro sShim hsShim hpcS hrunS hinvS hvmS
      subst hshimA
      refine sepWPp_drop_left ?_
      have hspS : sShim.sp = fsp := by
        rw [← hsShim]; simp [wp_norm, arm64_norm, fsp, cliInitiateFrame]
      have hx0S : sShim.readReg64 .x0 = x.stores := by
        rw [← hsShim]; simp [wp_norm, arm64_norm]
      have hx1S : sShim.readReg64 .x1 = x.peerA := by
        rw [← hsShim]; simp [wp_norm, arm64_norm]
      have hx2S : sShim.readReg64 .x2 = x.bundleA + 120#64 := by
        rw [← hsShim]; simp [wp_norm, arm64_norm]
      have hx3S : (sShim.readReg64 .x3).setWidth 8 = 0#8 := by
        rw [← hsShim]; simp [wp_norm, arm64_norm]; try decide
      have hlrS : sShim.readReg64 .lr = initPcPlaced 0x009c := by
        rw [← hsShim]
        change _ = (blkPl_521).base + 156#64
        simp [wp_norm, arm64_norm]; try bv_omega
      have hfpS : sShim.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsShim]; simp [wp_norm, arm64_norm]
      have hx19S : sShim.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsShim]; simp [wp_norm, arm64_norm, hx8]
      have hvregsS : calleeSavedVRegs sShim = calleeSavedVRegs s0 := by
        rw [← hsShim]; simp [calleeSavedVRegs, wp_norm, arm64_norm]
      have htrS : sShim.trace = s0.trace := by rw [← hsShim]; simp [wp_norm, arm64_norm]
      have hfsS : sShim.fs.files = s0.fs.files := by rw [← hsShim]; simp [wp_norm, arm64_norm]
      clear hsShim
      have halS : sShim.spAligned = true := spAligned_of_frame hal0 hspS
      have hpoolS : A.pool lim st s0 = A.pool lim st sShim := (A.pool_of_vmPreserved hvmS).symm
      rw [hpoolS]
      simp only [pointsTo16_zero_eq]
      let shimArg : (IdentityShimCall × BitVec 8) × M.σ :=
        (({ self := x.stores, addrA := x.peerA, keyA := x.bundleA + 120#64 }, 0#8), st)
      change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sShim _ Q Qp oom
      refine initCallLscro hh hpanic hStore.idTrustShim (gx := shimArg)
        (F := cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          memRegion fsp 0xd0 ∗
          memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
          storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
          coinsCursorAtPlaced x.coinsP x.coins 0 ∗
          tokenInitPlacedAt ∗
          (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
          lsLogOff ∗ initSaved s0 ∗
          initArgsAtPlaced fsp x s0 ∗
          memRegion (fsp + 0x128#64) 0x490 ∗
          ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))
        hpcS hrunS halS hinvS htrS hfsS hlrS ?_ (fun _ => false_entails _) ?_
      · unfold initSaved initArgsAtPlaced
        dsimp only [shimArg]
        rw [hspS]
        simp (disch := decide) only
          [fsp, cliInitiateFrame, initLocalsSize, BitVec.add_zero, bv_sub_add_lit,
            Nat.reduceAdd, Nat.reduceSub]
        have hsp113 : (s0.sp - 96#64) - 17#64 = s0.sp - 113#64 := by bv_omega
        have hsp113' : (s0.sp - 96#64) + (0#64 - 17#64) = s0.sp - 113#64 := by bv_omega
        try simp only [hsp113, hsp113']
        have hpackB := cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
          (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
          (opkId := opkId) h1 h2 h3 hopk
        repeat rw [sepConj_assoc]
        refine pure_sepConj_intro ⟨hx0S, hx1S, hx2S, hx3S, hFitsShim⟩ ?_
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono hpackB
              (sepConj_mono (prologue_low_d0_merge_sp s0.sp)
                (sepConj_mono_left (prologue_high_5ba_merge_sp s0.sp))))))
        sep_frame
      intro sAfterShim hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
      dsimp only [shimArg]
      refine sepWPp_exists_left fun evs1 => ?_
      rw [sepConj_assoc]
      refine sepWPp_pure_elim fun ⟨hvtAS, hfutNZ, hfutAl, htrAS, hevs1⟩ => ?_
      have htrAS' : sAfterShim.trace = s0.trace := htrAS.trans htrS
      have hfsAS' : sAfterShim.fs.files = s0.fs.files := hfsAS htrAS'
      have hspAS' : sAfterShim.sp = fsp := hspAS.trans hspS
      have hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c :=
        ⟨hpcAS, hrunAS, hspAS', (cs_fp hcsAS).trans hfpS, (cs_x19 hcsAS).trans hx19S,
          hfsAS', hinvAS, (cs_vregs hcsAS).trans hvregsS, hal0⟩
      rw [hspS]
      refine sepWPp_mono_pre
        (P' := afterTrustShimMemPlaced A lim (M.stepEvents evs1 st) x stk s0 sAfterShim)
        (by unfold afterTrustShimMemPlaced; dsimp only [fsp]; sep_frame) ?_
      exact hnext sAfterShim evs1 h1 h2 h3 hevs1 hfutNZ hfutAl hctrlAS htrAS' hvtAS

/-! ## `idTrustPoll` and `sret` unpacking (`0x009c → 0x00b8`) -/

set_option maxHeartbeats 1600000 in
/-- Budget-threaded `idTrustPoll` invocation and 48-byte `sret` unpacking (`0x009c → 0x00b8`). -/
theorem stage1_trust_to_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {eEnvs : ExistingStoreCalleesEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st1 : M.σ} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hFitsPoll : FitsEnv M lim st1
      (eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0))))
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hs0 : AtInitEntryPlaced x s0)
    (hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterPoll : State) (evs2 : List AllocEvent)
      (opkId2 : BitVec 32) (tb : Bool) (w_tb o2 o3 o4 o5 : BitVec 64),
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 (sAfterShim.readReg64 .x0)) evs2 →
      (∀ p, x.bundle.opk = some p → opkId2 = p.1) →
      InInitiatePlaced s0 sAfterPoll 0x00b8 →
      sAfterPoll.trace = s0.trace →
      BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8) →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterPoll
        (afterTrustPollMemPlaced A lim (M.stepEvents evs2 st1) x stk s0 sAfterPoll
          (sAfterShim.readReg64 .x0) opkId2 w_tb o2 o3 o4 o5) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMemPlaced A lim st1 x stk s0 sAfterShim) Q Qp oom := by
  have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAS : sAfterShim.pc = (blkPl_521).base + 156#64 := hctrlAS.pc
  have hrunAS := hctrlAS.run; have hspAS' := hctrlAS.sp
  have hfpAS := hctrlAS.fp; have hx19AS := hctrlAS.x19; have hfsAS' := hctrlAS.files0
  have hinvAS := hctrlAS.inv; have hvregsAS := hctrlAS.vregs
  have halAS := spAligned_of_frame hal0 hspAS'
  unfold afterTrustShimMemPlaced; dsimp only
  dsimp only [trustPollGhostOf] at hFitsPoll hnext
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAS' hFitsPoll hnext ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAS'] using halAS
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId2 => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨_, _, _, hopk2⟩ => ?_
  rw [poll_frame_5ba_split fsp 48 (by decide)]
  repeat rw [sepConj_assoc]
  refine sepWPp_exists_pos3 fun f0 => ?_
  refine sepWPp_exists_pos4 fun f1 => ?_
  let futPtr := sAfterShim.readReg64 .x0
  have hx1AS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym := hvtAS
  refine sepWPp_with_rodata (rodata_idTrustFut_poll_placed' hinvAS) ?_
  generalize hpollA : lsmpl.base 566 = pollAddr
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
    have hlrP : sPoll.readReg64 .lr = initPcPlaced 0x00b8 := by
      rw [← hsPoll]
      change _ = (blkPl_521).base + 184#64
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
    have hpoolP : A.pool lim st1 sAfterShim = A.pool lim st1 sPoll :=
      (A.pool_of_vmPreserved hvmP).symm
    rw [hpoolP]
    try rw [hspAS']
    try rw [hx1AS]
    let pollGhost : IdPollGhost :=
      { call := { fut := futPtr, out := fsp + 0x1600#64,
                  call := { addr := x.peer, addrA := x.peerA,
                            key := x.bundle.idKey, keyA := x.bundleA + 120#64 } }
        self := x.stores
        peers := StoresGhost.opened.identity.peers }
    have hFitsPollP : FitsEnv M lim st1 (eEnvs.idTrustPoll sPoll.fs.files pollGhost) := by
      rw [hfsP, hfs0]
      exact hFitsPoll
    have hpeersGet : ∀ bs,
        StoresGhost.opened.identity.peers.get cliIo.rd sPoll.fs.files x.peer.val.name = .ok bs →
        IdFileWf bs := by
      intro bs hbs
      rw [hfsP, hfs0] at hbs
      obtain ⟨bs0, hbs0, hwf0⟩ := hinitOk.idGet
      rw [hbs0] at hbs
      cases hbs
      exact hwf0
    change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sPoll _ Q Qp oom
    refine initCallLscro hh hpanic hStore.idTrustPoll (gx := ((pollGhost, 0#8), st1))
      (F := A.live futPtr 32 8 ∗
        dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        dirAt A.repAlloc (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A.repAlloc (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A.repAlloc (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A.repAlloc (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A.repAlloc (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        tokenInitPlacedAt ∗
        bundleRestAt x opkId2 ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        initSaved s0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
        memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
        memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))
      hpcP hrunP halP hinvP htrP hfsP hlrP ?_ (fun _ => false_entails _) ?_
    · unfold storesAt cliBundleBody bundleRestAt lsLogOff
      dsimp only [pollGhost, futPtr, Reg.x0]
      rw [hspP]
      repeat rw [sepConj_assoc]
      refine pure_sepConj_intro
        ⟨hx0P, hx8P, hinitOk.nameLt, by
          dsimp only [StoresGhost.opened, DirGhost.new]
          have h := hinitOk.idPathLt; unfold pathOf at h
          split at h
          · rename_i heq; rw [heq]; dsimp; omega
          · simp only [List.length_append] at h; omega,
          ⟨hinitOk.idPathOk, hinitOk.idPathLt⟩, hpeersGet, hFitsPollP⟩ ?_
      rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
    intro sAfterPoll hpcAP hrunAP hspAP hcsAP hinvAP hfsAP
    dsimp only [pollGhost]
    refine sepWPp_exists_left fun evs2 => ?_
    rw [sepConj_assoc]
    refine sepWPp_exists_left fun gr => ?_
    refine sepWPp_exists_left fun p => ?_
    rw [sepConj_assoc]
    refine sepWPp_pure_elim fun ⟨⟨hgr, htrAP⟩, hp, hevs2⟩ => ?_
    have htrAP' : sAfterPoll.trace = s0.trace := htrAP.trans htrP
    have hfsAP' : sAfterPoll.fs.files = s0.fs.files := hfsAP htrAP'
    rw [hfsP, hfs0] at hgr hevs2
    obtain ⟨tb, htb1, htb2⟩ := idTrust_always_ok hinitOk hgr hp
    rw [htb1, idTrustOutAt_ok A.repAlloc 0#64]
    have houtCells :
        trustPollOutAt 0#64 (fsp + 0x1600#64) (.ok tb) ⊢
          ∃∗ w_tb : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64,
            ⌜BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8)⌝ ∗
            ((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
            ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
            ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
            ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5) := by
      unfold trustPollOutAt
      rw [show (39 : Nat) = 7 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split _ 7 _ (by decide),
        memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
        memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
        memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
        ProofLib.memRegion_eight]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o2
      have hpackTb :
          ((fsp + 5640#64) ↦₈ (if tb then 1#8 else 0#8)) ∗ memRegion (fsp + 5641#64) 7 ⊢
            ∃∗ w, ⌜BitVec.extractLsb' 0 8 w = (if tb then 1#8 else 0#8)⌝ ∗
              ((fsp + 5640#64) ↦₆₄ w) := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          byte_and_pad7_entails_word64 (fsp + 5640#64) (if tb then 1#8 else 0#8)
      refine Entails.trans (by sep_frame :
        _ ⊢ (((fsp + 5640#64) ↦₈ (if tb then 1#8 else 0#8)) ∗ memRegion (fsp + 5641#64) 7) ∗
            (((fsp + 5632#64) ↦₆₄ (0#64 - 2#64)) ∗
              ((fsp + 5648#64) ↦₆₄ o2) ∗ ((fsp + 5656#64) ↦₆₄ o3) ∗
              ((fsp + 5664#64) ↦₆₄ o4) ∗ ((fsp + 5672#64) ↦₆₄ o5))) ?_
      refine Entails.trans (sepConj_mono_left hpackTb) ?_
      rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro w_tb
      refine Entails.sepExists_right w_tb (Entails.sepExists_right o2
        (Entails.sepExists_right o3 (Entails.sepExists_right o4 (Entails.sepExists_right o5 ?_))))
      rw [sepConj_assoc]
      exact pure_sepConj_elim fun hw => pure_sepConj_intro hw (by sep_frame)
    refine sepWPp_mono_pre (sepConj_mono_left houtCells) ?_
    refine sepWPp_exists_left fun w_tb => ?_; refine sepWPp_exists_left fun o2 => ?_
    refine sepWPp_exists_left fun o3 => ?_; refine sepWPp_exists_left fun o4 => ?_
    refine sepWPp_exists_left fun o5 => ?_
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun hw_tb => ?_
    have hctrlAP : InInitiatePlaced s0 sAfterPoll 0x00b8 :=
      ⟨hpcAP, hrunAP, (hspAP.trans hspP).trans hfsp.symm, (cs_fp hcsAP).trans hfpP,
        (cs_x19 hcsAP).trans hx19P, hfsAP', hinvAP, (cs_vregs hcsAP).trans hvregsP, hal0⟩
    refine sepWPp_mono_pre
      (P' := afterTrustPollMemPlaced A lim (M.stepEvents evs2 st1) x stk s0 sAfterPoll
        futPtr opkId2 w_tb o2 o3 o4 o5)
      (by unfold afterTrustPollMemPlaced lsLogOff; dsimp only; rw [hspP, ← hfsp]; sep_frame) ?_
    exact hnext sAfterPoll evs2 opkId2 tb w_tb o2 o3 o4 o5 hevs2 hopk2 hctrlAP htrAP' hw_tb htb2)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudgetAux
