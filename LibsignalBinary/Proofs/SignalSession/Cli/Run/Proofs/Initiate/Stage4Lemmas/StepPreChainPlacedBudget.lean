/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Stage 4 Segment 1 (`[LibsignalPlacement]`, `+4260 → +4576 / +4508`)

Executes `+4260 → +4496` (`ephA` draw/clamp and `<RootKey>::create_chain`) and branches to `+4576`
(`Ok`) or `+4508` (`Err`) under `RustCliAllocBudget M`, advancing `A.pool` by `stage4PreChainEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget

open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding cells3_entails_memRegion24
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  derivePublicKeyBytesSpec createChainSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced InitLocalCalleesPlaced RunHooksPlaced
  coinsFillSpecPlacedW3
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas hiding
  dealloc_ok_at_init_placed staticDrop_ok_at_init_placed errExitMemPlaced
  panic_oom_entails_initOnPanic_placed panic_oom_only_entails_initOnPanic_placed
  stage4_err_exit_placed stage4_step_prechain_to_4496_placed
  stage4_branch_4496_ok_placed stage4_branch_4496_err_placed
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlacedBudget
  (staticDrop_ok_at_init_placed)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (derivePublicKeyBytesSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (createChainSpec createChainSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux
  (Stage4PreChainEnv fitsEnv_createChain_of_fitsEvents stage4PreChainEvents
   stage4_step_prechain_4376_to_4448_placed stage4_step_prechain_to_4376_placed)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux
  (stage4PreChainEvents Stage4PreChainEnv)

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓] private theorem pc_setMem' (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem status_setMem' (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem trace_setMem' (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem tpidr_setMem' (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPC' (s : State) (p : BitVec 64) : (s.setPC p).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setMem' (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPS' (s : State) (p : PState) : (s.setPState p).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_advPC' (s : State) : s.advancePC.sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_w64' (s : State) (i : BitVec 5) (v : BitVec 64) : (s.writeReg64 (.gpr i) v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_w32' (s : State) (i : BitVec 5) (v : BitVec 32) : (s.writeReg32 (.gpr i) v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_wReg' (s : State) (w : Width) (i : BitVec 5) (v : BitVec 64) : (s.writeReg w (.gpr i) v).sp = s.sp := by cases w <;> cases s <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setPC' (s : State) (p : BitVec 64) (r : Reg) : (s.setPC p).readReg64 r = s.readReg64 r := State.readReg64_setPC s p r
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setPS' (s : State) (p : PState) (r : Reg) : (s.setPState p).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_advPC' (s : State) (r : Reg) : s.advancePC.readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setPC' (s : State) (p : BitVec 64) (r : Reg) : (s.setPC p).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setPS' (s : State) (p : PState) (r : Reg) : (s.setPState p).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_advPC' (s : State) (r : Reg) : s.advancePC.readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem vregs_setMem' (s : State) (m : Memory) : calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

open Lean Meta Elab Tactic in
local elab "s4_set_state " id:ident : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let args := ty.getAppArgs
  let sE := args[2]!
  let g1 ← g.define id.getId (mkConst ``Arm64.State) sE
  let (fv, g2) ← g1.intro1P
  g2.withContext do
    let ty2 := (← instantiateMVars (← g2.getType)).consumeMData
    let args2 := ty2.getAppArgs
    let pAbs ← kabstract args2[3]! sE
    let args2' := args2.set! 3 (pAbs.instantiate1 (mkFVar fv))
    let g3 ← g2.replaceTargetDefEq (mkAppN ty2.getAppFn args2')
    replaceMainGoal [g3]

set_option maxHeartbeats 1600000 in
private theorem chk_noSvc0_521 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_521.text = true := rfl

local macro "s4_step_sync " mmpl:ident gh:ident w:ident hinv:term:max mid:term:max : tactic =>
  `(tactic| (
    apply sepWPp_step_to_lscro $hinv (mid := $mid)
    try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_521).rebase (blkPl_521).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (cliGhostExterns $gh (cliExternsPlaced $mmpl $w))))
      blkLib_eq_521 (hchk := chk_noSvc0_521) (mid := $mid)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    clear _hnsp
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  ))

/-! ## Sub-Segment `+4448 → +4496` (`StaticSecret::drop` and `<RootKey>::create_chain`) -/

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 3200000 in
theorem stage4_step_prechain_from_4448_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    (rk0Key ck0Key pq0Key : RootKey)
    (ephClamped : List.Vector (BitVec 8) 32)
    {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCreateChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)))
    (hFits : FitsEvents M lim st (stage4PreChainEvents W.C x.bundle.spk ephClamped))
    {s4 : State}
    (hctrl4 : InInitiatePlaced s0 s4 4448)
    (htr4 : s4.trace = s0.trace)
    (hx20_4 : s4.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_4 : s4.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22_4 : s4.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx23_4 : s4.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2496#64)
    (hx25_4 : s4.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W)
      (initPcPlaced 4496) s4
      (coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
        ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
        memRegion (fsp + 2352#64) 100 ∗
        ((fsp + 2496#64) ↦ₛ (W.C.pubKey ephClamped).toList) ∗
        memRegion (fsp + 2528#64) 32 ∗
        ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 5632#64) 32 ∗
        memRegion (fsp + 5664#64) 40 ∗
        A.pool lim st s4 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢
          coinsCursorAtPlaced x.coinsP x.coins 192 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (W.C.pubKey ephClamped).toList) ∗
          ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
          memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64)
            (rootCreateChain W.C rk0Key x.bundle.spk ⟨ephClamped⟩) ∗
          A.pool lim (M.stepEvents (stage4PreChainEvents W.C x.bundle.spk ephClamped) st) sf ∗
          stackAt fsp (stk - cliInitiateFrame) ∗
          Frame))
      Qp oom := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (st_s : State), st_s.sp = fsp → st_s.spAligned = true :=
    fun st_s hst => fsp_aligned_of_s0 hstk hspk hst hctrl4.spAligned
  have hrk_ne : fsp + 2224#64 ≠ 0#64 := fsp_add_ne_zero hstk hspk 2224 (by decide)
  have hFits_cc :=
    fitsEnv_createChain_of_fitsEvents W.C (fsp + 2224#64) rk0Key (fsp + 0x408#64) x.bundle.spk
      (fsp + 2528#64) ephClamped (fsp + 5632#64) hFits
  have hs4_sp' : s4.sp = fsp := hctrl4.sp
  have hs4_fp : s4.readReg64 .fp = fsp + 7312#64 := hctrl4.fp.trans hfp_fsp.val
  have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl4.x19
  have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20_4
  have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21_4
  have hs4_x22 : s4.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22_4
  have hs4_x23 : s4.readReg64 (.gpr 23#5) = fsp + 2496#64 := hx23_4
  have hs4_x25 : s4.readReg64 (.gpr 25#5) = fsp + 5632#64 := hx25_4
  have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hctrl4.vregs
  have hs4_tr : s4.trace = s0.trace := htr4
  have hs4_files : s4.fs.files = s0.fs.files := hctrl4.files0
  have hs4_run : s4.status = .Running := hctrl4.run
  have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
  clear hx20_4 hx21_4 hx22_4 hx23_4 hx25_4
  clear_value fsp
  have hs4_pc' : s4.pc = (blkPl_521).base + 4448#64 := hctrl4.pc
  have hstdrop := staticDrop_ok_at_init_placed hh
  obtain ⟨sk0, sk1, sk2, sk3, _, hsk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ephClamped)
  have hsk_4064 : ((fsp + 4064#64) ↦ₛ ephClamped.toList) =
      ((fsp + 4064#64) ↦₆₄ sk0) ∗ ((fsp + 4072#64) ↦₆₄ sk1) ∗
      ((fsp + 4080#64) ↦₆₄ sk2) ∗ ((fsp + 4088#64) ↦₆₄ sk3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 4064#64)
  have hsk_2528 : ((fsp + 2528#64) ↦ₛ ephClamped.toList) =
      ((fsp + 2528#64) ↦₆₄ sk0) ∗ ((fsp + 2536#64) ↦₆₄ sk1) ∗
      ((fsp + 2544#64) ↦₆₄ sk2) ∗ ((fsp + 2552#64) ↦₆₄ sk3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 2528#64)
  have hm72_split :
      memRegion (fsp + 5632#64) 72 =
        memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 :=
    ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 32) (k := 40)
      (b' := fsp + 5664#64) rfl (by bv_omega) (by decide)
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.pc = initPcPlaced 4496 ∧ sf.status = .Running ∧
    sf.sp = fsp ∧ sf.readReg64 .fp = s0.sp - 0x60#64 ∧
    sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
    sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
    sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
    (Pf ⊢
      coinsCursorAtPlaced x.coinsP x.coins 192 ∗
      ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
      memRegion (fsp + 2352#64) 100 ∗
      ((fsp + 2496#64) ↦ₛ (W.C.pubKey ephClamped).toList) ∗
      ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
      memRegion (fsp + 4064#64) 32 ∗
      createChainResultAt (fsp + 5632#64)
        (rootCreateChain W.C rk0Key x.bundle.spk ⟨ephClamped⟩) ∗
      A.pool lim (M.stepEvents (stage4PreChainEvents W.C x.bundle.spk ephClamped) st) sf ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      Frame))
  ·
    conv => arg 4; rw [hsk_4064, cells4_eq_memRegion32 (fsp + 2528#64)]
    s4_elim_exists u2528_0; s4_elim_exists u2528_1; s4_elim_exists u2528_2; s4_elim_exists u2528_3
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    s4_step_sync mmpl gh W hctrl4.inv (lsρ lsStaticSecretDropSym)
    intro hs5_inv
    have h4064_sk := cells4_entails_memRegion32' (fsp + 4064#64) sk0 sk1 sk2 sk3
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4064_sk
    s4_fold_pre h4064_sk
    s4_rw_pre hsk_2528.symm
    s4_set_state sc5
    refine sepWPp_call_wpp_split_lscro hstdrop (fsp + 4064#64)
      (T := memRegion (fsp + 4064#64) 32)
      (F := ?_)
      hs5_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [withVmPreserved, zeroizeSecretSpec]
      exact Entails.pure_right (by wp_norm_goal) (Entails.refl _)
    intro s6 hs6_pc hs6_run hs6_sp hs6_cs hs6_inv
    dsimp (config := { zeta := false }) only [withVmPreserved, zeroizeSecretSpec]
    conv => arg 4; rw [sepConj_assoc]
    apply SepWPp.pure_elim
    intro hvm6
    conv => arg 4; rw [sepConj_assoc]
    apply SepWPp.pure_elim
    intro hs6_tr_eq
    have hpool6 : A.pool lim st sc5 = A.pool lim st s6 :=
      (A.pool_transport lim st sc5 s6 hvm6).symm
    conv => arg 4; rw [hpool6]
    clear hpool6 hvm6 sc5
    have hs5_sp_eq := lscro_sp_eq hs5_inv fsp (by wp_norm_goal)
    have hs6_sp' : s6.sp = fsp := hs6_sp.trans hs5_sp_eq
    have hs6_align : s6.spAligned = true := hfsp_align s6 hs6_sp'
    have hs6_fp : s6.readReg64 .fp = fsp + 7312#64 :=
      (hs6_cs.gpr ⟨29, by decide⟩).trans (by wp_norm_goal)
    have hs6_x19 : s6.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs6_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs6_x20 : s6.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs6_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs6_x21 : s6.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs6_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs6_x22 : s6.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs6_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs6_x23 : s6.readReg64 (.gpr 23#5) = fsp + 2496#64 :=
      (hs6_cs.gpr ⟨23, by decide⟩).trans (by wp_norm_goal)
    have hs6_x25 : s6.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs6_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs6_vr : calleeSavedVRegs s6 = calleeSavedVRegs s0 :=
      hs6_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr)
    have hs6_tr : s6.trace = s0.trace := hs6_tr_eq.trans (by wp_norm_goal)
    have hs6_pc' : s6.pc = (blkPl_521).base + 4472#64 := by
      rw [hs6_pc]; wp_norm_goal
    have hz32 : ((fsp + 4064#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (fsp + 4064#64) 32 := by
      have hlen32 : (List.replicate 32 0#8).length = 32 := by decide
      exact hlen32 ▸ pointsToBytes_entails_memRegion (fsp + 4064#64) (List.replicate 32 0#8)
    s4_fold_pre hz32
    s4_rw_pre hm72_split.symm
    conv => arg 4; rw [stackAt_fsp_split hstk hstk64 fsp Initiator.createChainStack (by decide)]
    conv => arg 4; simp only [sepConj_assoc]
    s4_step_sync mmpl gh W hs6_inv (lsmpl.base 40)
    intro hs7_inv
    s4_set_state sc7
    refine sepWPp_call_wpp_split_lscro hCreateChain
      (⟨fsp + 2224#64, rk0Key,
        fsp + 0x408#64, x.bundle.spk,
        fsp + 2528#64, ⟨ephClamped⟩,
        fsp + 5632#64⟩, st)
      (T := ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 5632#64) 72 ∗
        A.pool lim st sc7 ∗
        stackAt fsp Initiator.createChainStack)
      (F := ?_)
      hs7_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
      ?_
    · dsimp only [createChainSpec, createChainSpecWithStack, sc7]
      have hs7_sp_eq := lscro_sp_eq hs7_inv fsp (by wp_norm_goal)
      rw [hs7_sp_eq]
      exact Entails.pure_right
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, hrk_ne, hFits_cc⟩
        (Entails.of_eq (by s4_ac_rfl))
    intro s8 hs8_pc hs8_run hs8_sp hs8_cs hs8_inv
    clear sc7
    dsimp (config := { zeta := false }) only [createChainSpec, createChainSpecWithStack]
    have hs7_sp_eq := lscro_sp_eq hs7_inv fsp (by wp_norm_goal)
    conv => arg 4; rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    conv => arg 4; rw [sepConj_assoc]
    apply SepWPp.pure_elim
    rintro ⟨hs8_tr_eq, hevs⟩
    conv => arg 4; rw [hs7_sp_eq]
    have hevs_eq : evs = stage4PreChainEvents W.C x.bundle.spk ephClamped := hevs
    subst hevs_eq
    have hs8_sp' : s8.sp = fsp := hs8_sp.trans hs7_sp_eq
    have hs8_fp : s8.readReg64 .fp = s0.sp - 0x60#64 :=
      (hs8_cs.gpr ⟨29, by decide⟩).trans (by rw [hfp_fsp.val]; wp_norm_goal)
    have hs8_x19 : s8.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs8_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs8_x20 : s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs8_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs8_x21 : s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs8_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs8_x22 : s8.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs8_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs8_x25 : s8.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs8_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs8_vr : calleeSavedVRegs s8 = calleeSavedVRegs s0 :=
      hs8_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs6_vr)
    have hs8_tr : s8.trace = s0.trace := hs8_tr_eq.trans (by wp_norm_goal)
    have hs8_pc_init : s8.pc = initPcPlaced 4496 := by
      dsimp only [initPcPlaced, initEntryPlaced]; rw [hs8_pc]; wp_norm_goal; rfl
    apply SepWPp.of_sepWP_ret
    apply SepWP.done hs8_pc_init hs8_run
    refine ⟨hs8_pc_init, hs8_run, hs8_sp', hs8_fp, hs8_x19, hs8_x20, hs8_x21, hs8_x22, hs8_x25,
      hs8_vr, hs8_inv, hs8_tr, ?_⟩
    have hstk_back := (stackAt_fsp_split hstk hstk64 fsp Initiator.createChainStack (by decide)).symm
    s4_rw_ent hstk_back
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps
      ⟨hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hx22f, hx25f, hvrf, hinvf, htrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq (traceFsSound_initPlaced mmpl gh W) hsteps
        (htrf.trans hs4_tr.symm)).trans hs4_files
    exact ⟨htrf, ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl4.spAligned⟩,
      hx20f, hx21f, hx22f, hx25f, hentf⟩

/-! ## Composed Segment `+4260 → +4496` -/

theorem stage4_step_prechain_to_4496_placed_of_callees [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hDerivePubKey : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey)))
    (hCreateChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (createChainSpec M A lim W.C)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hFits : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    {s : State}
    (hctrl : InInitiatePlaced s0 s 4260)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32)
    (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (initProgPlaced mmpl gh W)
      (initPcPlaced 4496) s
      (coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗
        memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗
        memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢
          coinsCursorAtPlaced x.coinsP x.coins 192 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (W.C.pubKey (Ratchet.clampScalar ephVec)).toList) ∗
          ((fsp + 2528#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64)
            (rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey))
              x.bundle.spk ⟨Ratchet.clampScalar ephVec⟩) ∗
          A.pool lim
            (M.stepEvents (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar ephVec)) st)
            sf ∗
          stackAt fsp (stk - cliInitiateFrame) ∗
          Frame))
      Qp oom := by
  have : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  intro fsp ephVec
  refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
    (stage4_step_prechain_to_4376_placed (A := A) (lim := lim) (st := st) (Frame := Frame)
      hstk hstk64 hspk hCoins hcoinsLt hctrl htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk) ?_
  rintro s2 P2 _ _ _ ⟨htr2, hctrl2, hx20_2, hx21_2, hx22_2, hent2⟩
  refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
    (sepWPp_mono_pre hent2
      (stage4_step_prechain_4376_to_4448_placed (A := A) (lim := lim) (st := st) (Frame := Frame)
        hstk hspk hDerivePubKey hctrl2 htr2 hx20_2 hx21_2 hx22_2)) ?_
  rintro s4 P4 _ _ _ ⟨htr4, hctrl4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hent4⟩
  exact sepWPp_mono_pre hent4
    (stage4_step_prechain_from_4448_placed (A := A) (lim := lim) (st := st) (Frame := Frame)
      hstk hstk64 hspk
      (bytesToKey32 (ofU8 dk.rootKey))
      (bytesToKey32 (ofU8 dk.chainKey))
      (bytesToKey32 (ofU8 dk.pqrKey))
      (Ratchet.clampScalar ephVec)
      hh hCreateChain hFits hctrl4 htr4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4)

theorem stage4_step_prechain_to_4496_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hFits : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    {s : State}
    (hctrl : InInitiatePlaced s0 s 4260)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32)
    (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (initProgPlaced mmpl gh W)
      (initPcPlaced 4496) s
      (coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗
        memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗
        memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢
          coinsCursorAtPlaced x.coinsP x.coins 192 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (W.C.pubKey (Ratchet.clampScalar ephVec)).toList) ∗
          ((fsp + 2528#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64)
            (rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey))
              x.bundle.spk ⟨Ratchet.clampScalar ephVec⟩) ∗
          A.pool lim
            (M.stepEvents (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar ephVec)) st)
            sf ∗
          stackAt fsp (stk - cliInitiateFrame) ∗
          Frame))
      Qp oom :=
  stage4_step_prechain_to_4496_placed_of_callees hstk hstk64 hspk hh hCoins
    hLocal.derivePubKeyBytes hLocal.rootKeyCreateChain hcoinsLt hFits
    hctrl htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk

/-! ## Branch Dispatch at `+4496` (`Ok → +4576`, `Err → +4508`) -/

set_option maxHeartbeats 800000 in
theorem stage4_branch_4496_ok_vm_placed [LibsignalPlacement]
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    {s0 s : State} {rk1 : RootKey} {ck1 : ChainKey} {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : cliInitiateNeed B ≤ stk)
    (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiatePlaced s0 s 4496)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx25 : s.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4576) s
      (((fsp + 5632#64) ↦₃₂ 0#32) ∗
        ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
        ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗
        Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4576 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢
          ((fsp + 5632#64) ↦₃₂ 0#32) ∗
          ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
          ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗
          Frame))
      Qp oom := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hx22 : s.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have hx25 : s.readReg64 (.gpr 25#5) = fsp + 5632#64 := hx25
  clear_value fsp
  have hpc0 : s.pc = (blkPl_521).base + 4496#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  apply sepWPp_step_to_lscro hctrl.inv (mid := (blkPl_521).base + 4576#64)
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_521).rebase (blkPl_521).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    blkLib_eq_521 (hchk := chk_noSvc0_521) (mid := (blkPl_521).base + 4576#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ :=
    _hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm])
  clear _hnsp
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv'
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by dsimp only [initPcPlaced, initEntryPlaced]; wp_norm_goal; rfl) (by wp_norm_lhs)
  refine ⟨hvm,
    by simp only [arm64_norm]; exact htr,
    ⟨by dsimp only [initPcPlaced, initEntryPlaced]; wp_norm_goal; rfl,
     by wp_norm_lhs,
     by simp only [arm64_norm]; exact hfsp_def.val ▸ hsp0,
     by simp only [arm64_norm]; exact hctrl.fp,
     by simp only [arm64_norm]; exact hctrl.x19,
     by simp only [arm64_norm]; exact hctrl.files0,
     hinv',
     by simp only [calleeSavedVRegs, arm64_norm]; exact hctrl.vregs,
     hctrl.spAligned⟩,
    by simp only [arm64_norm]; exact hx20,
    by simp only [arm64_norm]; exact hx21,
    by simp only [arm64_norm]; exact hx22,
    by simp only [arm64_norm]; exact hx25,
    Entails.of_eq (by s4_ac_rfl)⟩

theorem stage4_branch_4496_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    {s0 s : State} {rk1 : RootKey} {ck1 : ChainKey} {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : cliInitiateNeed B ≤ stk)
    (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiatePlaced s0 s 4496)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx25 : s.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4576) s
      (((fsp + 5632#64) ↦₃₂ 0#32) ∗
        ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
        ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗
        A.pool lim st s ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4576 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢
          ((fsp + 5632#64) ↦₃₂ 0#32) ∗
          ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
          ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗
          A.pool lim st sf ∗
          Frame))
      Qp oom := by
  intro fsp
  apply sepWPp_steps_post
    (stage4_branch_4496_ok_vm_placed (rk1 := rk1) (ck1 := ck1)
      (Frame := A.pool lim st s ∗ Frame) hstk hspk hctrl htr hx20 hx21 hx22 hx25)
  rintro sf Pf _ ⟨hvm, htrf, hctrlf, hx20f, hx21f, hx22f, hx25f, hentf⟩
  refine ⟨htrf, hctrlf, hx20f, hx21f, hx22f, hx25f, Entails.trans hentf ?_⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.of_eq (by s4_ac_rfl)

set_option maxHeartbeats 800000 in
theorem stage4_branch_4496_err_vm_placed [LibsignalPlacement]
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    {s0 s : State} {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : cliInitiateNeed B ≤ stk)
    (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiatePlaced s0 s 4496)
    (htr : s.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4508) s
      (((fsp + 5632#64) ↦₃₂ 1#32) ∗
        memRegion (fsp + 5636#64) 4 ∗
        ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
        memRegion (fsp + 5648#64) 56 ∗
        Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4508 ∧
        (Pf ⊢
          ((fsp + 5632#64) ↦₃₂ 1#32) ∗
          memRegion (fsp + 5636#64) 4 ∗
          ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
          memRegion (fsp + 5648#64) 40 ∗
          memRegion (fsp + 5688#64) 16 ∗
          Frame))
      Qp oom := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  clear_value fsp
  have hpc0 : s.pc = (blkPl_521).base + 4496#64 := hctrl.pc
  have hrun0 : s.status = .Running := hctrl.run
  apply sepWPp_step_to_lscro hctrl.inv (mid := (blkPl_521).base + 4508#64)
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_521).rebase (blkPl_521).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    blkLib_eq_521 (hchk := chk_noSvc0_521) (mid := (blkPl_521).base + 4508#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm : VmPreserved s _ :=
    _hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm])
  clear _hnsp
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv'
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by dsimp only [initPcPlaced, initEntryPlaced]; wp_norm_goal; rfl) (by wp_norm_lhs)
  have hm56 : memRegion (fsp + 5648#64) 56 =
      memRegion (fsp + 5648#64) 40 ∗ memRegion (fsp + 5688#64) 16 :=
    ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 40) (k := 16)
      (b' := fsp + 5688#64) rfl (by bv_omega) (by decide)
  refine ⟨hvm,
    by simp only [arm64_norm]; exact htr,
    ⟨by dsimp only [initPcPlaced, initEntryPlaced]; wp_norm_goal; rfl,
     by wp_norm_lhs,
     by simp only [arm64_norm]; exact hfsp_def.val ▸ hsp0,
     by simp only [arm64_norm]; exact hctrl.fp,
     by simp only [arm64_norm]; exact hctrl.x19,
     by simp only [arm64_norm]; exact hctrl.files0,
     hinv',
     by simp only [calleeSavedVRegs, arm64_norm]; exact hctrl.vregs,
     hctrl.spAligned⟩,
    ?_⟩
  rw [hm56]
  exact Entails.of_eq (by s4_ac_rfl)

theorem stage4_branch_4496_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    {s0 s : State} {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : cliInitiateNeed B ≤ stk)
    (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiatePlaced s0 s 4496)
    (htr : s.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4508) s
      (((fsp + 5632#64) ↦₃₂ 1#32) ∗
        memRegion (fsp + 5636#64) 4 ∗
        ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
        memRegion (fsp + 5648#64) 56 ∗
        A.pool lim st s ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4508 ∧
        (Pf ⊢
          ((fsp + 5632#64) ↦₃₂ 1#32) ∗
          memRegion (fsp + 5636#64) 4 ∗
          ((fsp + 5640#64) ↦₆₄ speWord 10) ∗
          memRegion (fsp + 5648#64) 40 ∗
          memRegion (fsp + 5688#64) 16 ∗
          A.pool lim st sf ∗
          Frame))
      Qp oom := by
  intro fsp
  apply sepWPp_steps_post
    (stage4_branch_4496_err_vm_placed (Frame := A.pool lim st s ∗ Frame)
      hstk hspk hctrl htr)
  rintro sf Pf _ ⟨hvm, htrf, hctrlf, hentf⟩
  refine ⟨htrf, hctrlf, Entails.trans hentf ?_⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.of_eq (by s4_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget

end
