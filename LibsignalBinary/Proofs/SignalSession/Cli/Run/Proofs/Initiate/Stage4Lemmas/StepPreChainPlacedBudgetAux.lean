/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.CellsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChain
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Heap.IfaceBudget
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
# Budget-Threaded Stage 4 Segment 1 Helpers (`[LibsignalPlacement]`, `+4260 → +4448`)

Defines `stage4PreChainEvents` and steps `initProgPlaced W` from `+4260` across
`signal_session_coins_fill`, X25519 scalar clamping, and `derive_public_key_bytes` to `+4448`
while transporting `A.pool` via `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux

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
  InitExitPostPlaced InitPanicPostPlaced RunHooksPlaced coinsFillSpecPlacedW3
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas hiding
  dealloc_ok_at_init_placed staticDrop_ok_at_init_placed errExitMemPlaced
  panic_oom_entails_initOnPanic_placed panic_oom_only_entails_initOnPanic_placed
  stage4_err_exit_placed
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (derivePublicKeyBytesBudgetSpec derivePublicKeyBytesSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (CreateChainEnv createChainEvents)

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
attribute [local simp, local arm64_norm, local wp_norm]
  Keys.clamp_byte0_norm Keys.clamp_byte0_norm32
  Keys.clamp_byte31_bfxil_norm Keys.clamp_byte31_bfxil_norm'

@[local arm64_norm ↓, local wp_norm ↓] private theorem pc_setMem' (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem status_setMem' (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem trace_setMem' (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem tpidr_setMem' (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem tpidr_wV128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem tpidr_wV64' (s : State) (i : BitVec 5) (v : BitVec 64) : (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem tpidr_wV32' (s : State) (i : BitVec 5) (v : BitVec 32) : (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPC' (s : State) (p : BitVec 64) : (s.setPC p).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setMem' (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPS' (s : State) (p : PState) : (s.setPState p).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_advPC' (s : State) : s.advancePC.sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_w64' (s : State) (i : BitVec 5) (v : BitVec 64) : (s.writeReg64 (.gpr i) v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_w32' (s : State) (i : BitVec 5) (v : BitVec 32) : (s.writeReg32 (.gpr i) v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_wReg' (s : State) (w : Width) (i : BitVec 5) (v : BitVec 64) : (s.writeReg w (.gpr i) v).sp = s.sp := by cases w <;> cases s <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_wV128' (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_wV64' (s : State) (i : BitVec 5) (v : BitVec 64) : (s.writeVReg64 i v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_wV32' (s : State) (i : BitVec 5) (v : BitVec 32) : (s.writeVReg32 i v).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setPC' (s : State) (p : BitVec 64) (r : Reg) : (s.setPC p).readReg64 r = s.readReg64 r := State.readReg64_setPC s p r
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_setPS' (s : State) (p : PState) (r : Reg) : (s.setPState p).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_advPC' (s : State) (r : Reg) : s.advancePC.readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_wV128' (s : State) (i : BitVec 5) (v : BitVec 128) (r : Reg) : (s.writeVReg128 i v).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_wV64' (s : State) (i : BitVec 5) (v : BitVec 64) (r : Reg) : (s.writeVReg64 i v).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r64_wV32' (s : State) (i : BitVec 5) (v : BitVec 32) (r : Reg) : (s.writeVReg32 i v).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setPC' (s : State) (p : BitVec 64) (r : Reg) : (s.setPC p).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_setPS' (s : State) (p : PState) (r : Reg) : (s.setPState p).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_advPC' (s : State) (r : Reg) : s.advancePC.readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_wV128' (s : State) (i : BitVec 5) (v : BitVec 128) (r : Reg) : (s.writeVReg128 i v).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_wV64' (s : State) (i : BitVec 5) (v : BitVec 64) (r : Reg) : (s.writeVReg64 i v).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem r32_wV32' (s : State) (i : BitVec 5) (v : BitVec 32) (r : Reg) : (s.writeVReg32 i v).readReg32 r = s.readReg32 r := by cases r <;> rfl
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

local macro "s4_step_sync " mmpl:ident gh:ident w:ident hinv:term:max mid:term:max : tactic =>
  `(tactic| (
    apply sepWPp_step_to_lscro $hinv (mid := $mid)
    try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_521).rebase (blkPl_521).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (cliGhostExterns $gh (cliExternsPlaced $mmpl $w))))
      blkLib_eq_521 (mid := $mid)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    clear _hnsp
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  ))

/-! ## Pre-Chain Event Sequence -/

/-- Allocator events emitted by `<RootKey>::create_chain` (`+4260 → +4496`):
`rustAllocEvents 32 1 ++ rustDeallocEvents 32 1` on `some _`, and `[]` on `none`. -/
def stage4PreChainEvents (C : Crypto) (spk : PublicKey)
    (ephClamped : List.Vector (BitVec 8) 32) : List AllocEvent :=
  match calculateAgreement C.X spk ⟨ephClamped⟩ with
  | some _ => rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
  | none => []

def Stage4PreChainEnv (C : Crypto) (spk : PublicKey)
    (ephClamped : List.Vector (BitVec 8) 32) (evs : List AllocEvent) : Prop :=
  evs = stage4PreChainEvents C spk ephClamped

theorem createChainEvents_stage4_eq (C : Crypto) (rkA : BitVec 64) (rk : RootKey)
    (theirA : BitVec 64) (spk : PublicKey) (ourA : BitVec 64)
    (ephClamped : List.Vector (BitVec 8) 32) (ret : BitVec 64) :
    createChainEvents C ⟨rkA, rk, theirA, spk, ourA, ⟨ephClamped⟩, ret⟩ =
      stage4PreChainEvents C spk ephClamped :=
  rfl

theorem fitsEnv_createChain_of_fitsEvents {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ}
    (C : Crypto) (rkA : BitVec 64) (rk : RootKey)
    (theirA : BitVec 64) (spk : PublicKey) (ourA : BitVec 64)
    (ephClamped : List.Vector (BitVec 8) 32) (ret : BitVec 64)
    (hFits : FitsEvents M lim st (stage4PreChainEvents C spk ephClamped)) :
    FitsEnv M lim st
      (CreateChainEnv C ⟨rkA, rk, theirA, spk, ourA, ⟨ephClamped⟩, ret⟩) := by
  rintro _ rfl
  exact hFits

/-! ## Sub-Segments `+4260 → +4376` and `+4376 → +4448` -/

private theorem prechain_4260_mem_unpack_placed (fsp : BitVec 64) (Rest : SepProp) :
    memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
    memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
    memRegion (fsp + 5632#64) 32 ∗ Rest =
    ∃∗ u2192_0 : BitVec 64, ∃∗ u2192_1 : BitVec 64, ∃∗ u2192_2 : BitVec 64,
    ∃∗ u2224_0 : BitVec 64, ∃∗ u2224_1 : BitVec 64, ∃∗ u2224_2 : BitVec 64, ∃∗ u2224_3 : BitVec 64,
    ∃∗ u2256_0 : BitVec 64, ∃∗ u2256_1 : BitVec 64, ∃∗ u2256_2 : BitVec 64, ∃∗ u2256_3 : BitVec 64,
    ∃∗ u2288 : BitVec 32,
    ∃∗ u2304_0 : BitVec 64, ∃∗ u2304_1 : BitVec 64, ∃∗ u2304_2 : BitVec 64, ∃∗ u2304_3 : BitVec 64,
    ∃∗ u5632_0 : BitVec 64, ∃∗ u5632_1 : BitVec 64, ∃∗ u5632_2 : BitVec 64, ∃∗ u5632_3 : BitVec 64,
      ((fsp + 2192#64) ↦₆₄ u2192_0) ∗ ((fsp + 2200#64) ↦₆₄ u2192_1) ∗ ((fsp + 2208#64) ↦₆₄ u2192_2) ∗
      ((fsp + 2224#64) ↦₆₄ u2224_0) ∗ ((fsp + 2232#64) ↦₆₄ u2224_1) ∗
      ((fsp + 2240#64) ↦₆₄ u2224_2) ∗ ((fsp + 2248#64) ↦₆₄ u2224_3) ∗
      ((fsp + 2256#64) ↦₆₄ u2256_0) ∗ ((fsp + 2264#64) ↦₆₄ u2256_1) ∗
      ((fsp + 2272#64) ↦₆₄ u2256_2) ∗ ((fsp + 2280#64) ↦₆₄ u2256_3) ∗ ((fsp + 2288#64) ↦₃₂ u2288) ∗
      ((fsp + 2304#64) ↦₆₄ u2304_0) ∗ ((fsp + 2312#64) ↦₆₄ u2304_1) ∗
      ((fsp + 2320#64) ↦₆₄ u2304_2) ∗ ((fsp + 2328#64) ↦₆₄ u2304_3) ∗
      ((fsp + 5632#64) ↦₆₄ u5632_0) ∗ ((fsp + 5640#64) ↦₆₄ u5632_1) ∗
      ((fsp + 5648#64) ↦₆₄ u5632_2) ∗ ((fsp + 5656#64) ↦₆₄ u5632_3) ∗ Rest := by
  rw [cells3_eq_memRegion24 (fsp + 2192#64), cells4_eq_memRegion32 (fsp + 2224#64),
      cells4_4_eq_memRegion36 (fsp + 2256#64), cells4_eq_memRegion32 (fsp + 2304#64),
      cells4_eq_memRegion32 (fsp + 5632#64)]
  s4_exists_eq

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
theorem stage4_step_prechain_4260_to_cf_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop} {oom : State → SepProp} {s : State}
    (hctrl : InInitiatePlaced s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (lsmpl.base 618) s
      (memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        memRegion (fsp + 5632#64) 32 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        sf.pc = lsmpl.base 618 ∧
        sf.status = .Running ∧ sf.sp = fsp ∧ sf.readReg64 .lr = initPcPlaced 4376 ∧
        sf.readReg64 .x0 = fsp + 5632#64 ∧ sf.readReg64 .x1 = 32#64 ∧
        sf.readReg64 .fp = s0.sp - 0x60#64 ∧ sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧ sf.fs.files = s0.fs.files ∧
        LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        (Pf ⊢ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 5632#64) 32 ∗
          A.pool lim st sf ∗ Frame))
      Qp oom := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have hfp0 : s.readReg64 .fp = fsp + 7312#64 := hctrl.fp.trans hfp_fsp.val
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hx22_0 : s.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  have hrun0 : s.status = .Running := hctrl.run
  have hx19_0 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl.x19
  have hvr0 : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  set rk0Key : RootKey := bytesToKey32 (ofU8 dk.rootKey)
  set ck0Key : RootKey := bytesToKey32 (ofU8 dk.chainKey)
  set pq0Key : RootKey := bytesToKey32 (ofU8 dk.pqrKey)
  have hrk_key_eq : keyToBytes32 rk0Key = ofU8 dk.rootKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.rootKey) hrk_bv
  have hpq_key_eq : keyToBytes32 pq0Key = ofU8 dk.pqrKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.pqrKey) hpq_bv
  have hck_key_eq : keyToBytes32 ck0Key = ofU8 dk.chainKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.chainKey) hck_bv
  clear hx22 hfsp_def
  clear_value fsp rk0Key ck0Key pq0Key
  obtain ⟨rk0, rk1w, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hrk_bv
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ := exists_unpack64_of_length_32 hpq_bv
  obtain ⟨ck0w, ck1w, ck2w, ck3w, _, hck_cells⟩ := exists_unpack64_of_length_32 hck_bv
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.trace = s0.trace ∧
    sf.pc = lsmpl.base 618 ∧
    sf.status = .Running ∧ sf.sp = fsp ∧ sf.readReg64 .lr = initPcPlaced 4376 ∧
    sf.readReg64 .x0 = fsp + 5632#64 ∧ sf.readReg64 .x1 = 32#64 ∧
    sf.readReg64 .fp = s0.sp - 0x60#64 ∧ sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
    LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    (Pf ⊢ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗ ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗ ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
      memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 5632#64) 32 ∗
      A.pool lim st sf ∗ Frame))
  · refine sepWPp_mono_pre
      (Entails.of_eq (prechain_4260_mem_unpack_placed fsp
        (((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗
          A.pool lim st s ∗ Frame))) ?_
    refine SepWPp.exists_elim fun u2192_0 => SepWPp.exists_elim fun u2192_1 =>
      SepWPp.exists_elim fun u2192_2 =>
      SepWPp.exists_elim fun u2224_0 => SepWPp.exists_elim fun u2224_1 =>
      SepWPp.exists_elim fun u2224_2 => SepWPp.exists_elim fun u2224_3 =>
      SepWPp.exists_elim fun u2256_0 => SepWPp.exists_elim fun u2256_1 =>
      SepWPp.exists_elim fun u2256_2 => SepWPp.exists_elim fun u2256_3 =>
      SepWPp.exists_elim fun u2288 =>
      SepWPp.exists_elim fun u2304_0 => SepWPp.exists_elim fun u2304_1 =>
      SepWPp.exists_elim fun u2304_2 => SepWPp.exists_elim fun u2304_3 =>
      SepWPp.exists_elim fun u5632_0 => SepWPp.exists_elim fun u5632_1 =>
      SepWPp.exists_elim fun u5632_2 => SepWPp.exists_elim fun u5632_3 => ?_
    conv => arg 4; rw [hhk,
      hkSlot100_unpack (fsp + 2352#64) (ofU8 dk.rootKey) (ofU8 dk.pqrKey) (ofU8 dk.chainKey)
        hrk_cells hpq_cells hck_cells hrk_bv hpq_bv hck_bv]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hpc0 : s.pc = (blkPl_521).base + 4260#64 := hctrl.pc
    s4_step_sync mmpl gh W hctrl.inv (lsmpl.base 618)
    intro hs1_inv
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have h2192_f :=
      CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas.cells3_entails_memRegion24
        (fsp + 2192#64) pq1 pq2 pq3
    have h2352_f := hkSlot100_cells_entails_memRegion100 (fsp + 2352#64)
      rk0 rk1w rk2 rk3 pq0 pq1 pq2 pq3 ck0w ck1w ck2w ck3w
    have h5632_f := cells4_entails_memRegion32' (fsp + 5632#64) 0#64 0#64 0#64 0#64
    have hrk_2224 : ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) =
        ((fsp + 2224#64) ↦₆₄ rk0) ∗ ((fsp + 2232#64) ↦₆₄ rk1w) ∗
        ((fsp + 2240#64) ↦₆₄ rk2) ∗ ((fsp + 2248#64) ↦₆₄ rk3) := by
      rw [hrk_key_eq, hrk_cells (fsp + 2224#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hck_2256 : ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) =
        ((fsp + 2256#64) ↦₆₄ ck0w) ∗ ((fsp + 2264#64) ↦₆₄ ck1w) ∗
        ((fsp + 2272#64) ↦₆₄ ck2w) ∗ ((fsp + 2280#64) ↦₆₄ ck3w) := by
      rw [hck_key_eq, hck_cells (fsp + 2256#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hpq_2304 : ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) =
        ((fsp + 2304#64) ↦₆₄ pq0) ∗ ((fsp + 2312#64) ↦₆₄ pq1) ∗
        ((fsp + 2320#64) ↦₆₄ pq2) ∗ ((fsp + 2328#64) ↦₆₄ pq3) := by
      rw [hpq_key_eq, hpq_cells (fsp + 2304#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2192_f h2352_f h5632_f
    refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_lhs,
      by wp_norm_goal, by dsimp only [initPcPlaced, initEntryPlaced]; wp_norm_goal; rfl,
      by wp_norm_goal, by wp_norm_goal, by rw [hfp_fsp.val]; wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      hs1_inv, by simp only [calleeSavedVRegs, arm64_norm]; exact hvr0, ?_⟩
    rw [hrk_2224, hck_2256, hpq_2304]
    s4_fold_ent h2192_f; s4_fold_ent h2352_f; s4_fold_ent h5632_f
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps
      ⟨htrf, hpcf, hrunf, hspf, hlrf, hx0f, hx1f, hfpf, hx19f, hx20f, hx21f, hx22f, hinvf, hvrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq (traceFsSound_initPlaced mmpl gh W) hsteps
        (htrf.trans htr.symm)).trans hctrl.files0
    exact ⟨htrf, hpcf, hrunf, hspf, hlrf, hx0f, hx1f, hfpf, hx19f, hx20f, hx21f, hx22f,
      hfilesf, hinvf, hvrf, hentf⟩

theorem stage4_call_coins_fill_to_4376_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 s1 : State} (hspk : stk ≤ s0.sp.toNat)
    {Frame : SepProp} {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 618)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hlr1 : s1.readReg64 .lr = initPcPlaced 4376)
    (hx0_1 : s1.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64)
    (hx1_1 : s1.readReg64 .x1 = 32#64) (hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64)
    (hx19_1 : s1.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hx20_1 : s1.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_1 : s1.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22_1 : s1.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hfiles1 : s1.fs.files = s0.fs.files)
    (hinv1 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hvr1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hspAligned0 : s0.spAligned = true) (htr1 : s1.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4376) s1
      (coinsCursorAtPlaced x.coinsP x.coins 160 ∗ memRegion (fsp + 5632#64) 32 ∗
        A.pool lim st s1 ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ InInitiatePlaced s0 sf 4376 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        (Pf ⊢ coinsCursorAtPlaced x.coinsP x.coins 192 ∗
          ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
          A.pool lim st sf ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp oom := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp1' : s1.sp = fsp := hsp1
  have hx0_1' : s1.readReg64 .x0 = fsp + 5632#64 := hx0_1
  have hx20_1' : s1.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20_1
  have hx21_1' : s1.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21_1
  have hx22_1' : s1.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22_1
  have halign1 : s1.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp1' hspAligned0
  clear hx0_1 hx20_1 hx21_1 hx22_1 hsp1
  clear_value fsp
  have hcf : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (coinsFillSpecPlacedW3 (stk - cliInitiateFrame))) :=
    subroutine_ok_mono (hCoins (coinsFill_stk_placed_le hstk) (stk_sub_le_63 hstk64))
      (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [withLsRoCl, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  refine sepWPp_call_wpp_split_lscro hcf ⟨fsp + 5632#64, 32, x.coinsP, x.coins, 160⟩
    (T := coinsCursorAtPlaced x.coinsP x.coins 160 ∗
      memRegion (fsp + 5632#64) 32 ∗ stackAt fsp (stk - cliInitiateFrame))
    (F := A.pool lim st s1 ∗ Frame) hinv1 hpc1 hrun1 halign1 hlr1 (by s4_split_frame) ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
  · dsimp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [hsp1', sepConj_comm _ (⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝)]
    exact Entails.pure_right hinv1
      (Entails.pure_right ⟨hx0_1', hx1_1, hcoinsLt, by decide⟩
        (Entails.of_eq (by simp only [sepConj_assoc])))
  intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_inv
  dsimp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  conv => arg 4; rw [hsp1', show (160 : Nat) + 32 = 192 from rfl]
  s4_pure_elim
  rintro ⟨hs2_tr_eq, hs2_fs_eq, hvm2⟩
  have hpool2 : A.pool lim st s1 = A.pool lim st s2 :=
    (A.pool_transport lim st s1 s2 hvm2).symm
  s4_rw_pre hpool2
  have hs2_sp' : s2.sp = fsp := hs2_sp.trans hsp1'
  have hs2_fp : s2.readReg64 .fp = s0.sp - 0x60#64 := (hs2_cs.gpr ⟨29, by decide⟩).trans hfp1
  have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := (hs2_cs.gpr ⟨19, by decide⟩).trans hx19_1
  have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 := (hs2_cs.gpr ⟨20, by decide⟩).trans hx20_1'
  have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 := (hs2_cs.gpr ⟨21, by decide⟩).trans hx21_1'
  have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 := (hs2_cs.gpr ⟨22, by decide⟩).trans hx22_1'
  have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvr1
  have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans htr1
  have hs2_files : s2.fs.files = s0.fs.files := by rw [hs2_fs_eq]; exact hfiles1
  have hctrl2 : InInitiatePlaced s0 s2 4376 :=
    ⟨hs2_pc, hs2_run, hfsp_def.val ▸ hs2_sp', hs2_fp, hs2_x19, hs2_files,
      hs2_inv, hs2_vr, hspAligned0⟩
  apply SepWPp.of_sepWP_ret
  apply SepWP.done hs2_pc hs2_run
  exact ⟨hs2_tr, hctrl2, hs2_x20, hs2_x21, hs2_x22, Entails.of_eq (by s4_ac_rfl)⟩

theorem stage4_step_prechain_to_4376_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63) {s : State}
    (hctrl : InInitiatePlaced s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (initPcPlaced 4376) s
      (coinsCursorAtPlaced x.coinsP x.coins 160 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗ A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ InInitiatePlaced s0 sf 4376 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        (Pf ⊢ coinsCursorAtPlaced x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 2496#64) 32 ∗
          memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
          ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
          memRegion (fsp + 5664#64) 40 ∗ A.pool lim st sf ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp oom := by
  intro fsp
  have hfsp_eq : Hide (s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp) := ⟨rfl⟩
  clear_value fsp
  have hm72_split : memRegion (fsp + 5632#64) 72 =
      memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 :=
    ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 32) (k := 40)
      (b' := fsp + 5664#64) rfl (by bv_omega) (by decide)
  let RestCf : SepProp :=
    coinsCursorAtPlaced x.coinsP x.coins 160 ∗ ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2496#64) 32 ∗ memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame
  refine sepWPp_seq_files (traceFsSound_initPlaced mmpl gh W)
    (sepWPp_mono_pre
      (by dsimp only [RestCf]; rw [hm72_split, hfsp_eq.val]; exact Entails.of_eq (by s4_ac_rfl))
      (stage4_step_prechain_4260_to_cf_placed (A := A) (lim := lim) (st := st) (Frame := RestCf)
        hstk hspk hctrl htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk)) ?_
  rintro s1 P1 _ _ _
    ⟨htr1, hpc1, hrun1, hsp1, hlr1, hx0_1, hx1_1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1,
      hfiles1, hinv1, hvr1, hent1⟩
  let FrameCf : SepProp :=
    ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
      memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 2496#64) 32 ∗
      memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗ Frame
  have hent1_cf :
      P1 ⊢ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) 32 ∗
        A.pool lim st s1 ∗
        stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ∗
        FrameCf := by
    refine Entails.trans hent1 ?_
    dsimp only [RestCf, FrameCf]
    rw [hfsp_eq.val]
    exact Entails.of_eq (by s4_ac_rfl)
  apply sepWPp_steps_post
    (sepWPp_mono_pre hent1_cf
      (stage4_call_coins_fill_to_4376_placed (A := A) (lim := lim) (st := st) (Frame := FrameCf)
        hstk hstk64 hspk hCoins hcoinsLt hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hfp1 hx19_1
        hx20_1 hx21_1 hx22_1 hfiles1 hinv1 hvr1 hctrl.spAligned htr1))
  intro sf Pf _ ⟨htrf, hctrlf, hx20f, hx21f, hx22f, hentf⟩
  rw [hfsp_eq.val] at hx20f hx21f hx22f hentf
  refine ⟨htrf, hctrlf, hx20f, hx21f, hx22f, Entails.trans hentf ?_⟩
  dsimp only [FrameCf]
  exact Entails.of_eq (by s4_ac_rfl)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem stage4_step_prechain_4376_to_4448_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey}
    {Frame : SepProp}
    {Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hDerivePubKey : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey)))
    {s2 : State}
    (hctrl2 : InInitiatePlaced s0 s2 4376)
    (htr2 : s2.trace = s0.trace)
    (hx20 : s2.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s2.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s2.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (initProgPlaced mmpl gh W)
      (initPcPlaced 4448) s2
      (coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
        ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
        memRegion (fsp + 2352#64) 100 ∗
        memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗
        memRegion (fsp + 4064#64) 32 ∗
        ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
        memRegion (fsp + 5664#64) 40 ∗
        A.pool lim st s2 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        InInitiatePlaced s0 sf 4448 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 23#5) = fsp + 2496#64 ∧
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
          memRegion (fsp + 2528#64) 32 ∗
          ((fsp + 4064#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 5632#64) 32 ∗
          memRegion (fsp + 5664#64) 40 ∗
          A.pool lim st sf ∗
          stackAt fsp (stk - cliInitiateFrame) ∗
          Frame))
      Qp oom := by
  intro fsp ephVec
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (st_s : State), st_s.sp = fsp → st_s.spAligned = true :=
    fun st_s hst => fsp_aligned_of_s0 hstk hspk hst hctrl2.spAligned
  have hs2_sp' : s2.sp = fsp := hctrl2.sp
  have hs2_fp : s2.readReg64 .fp = fsp + 7312#64 := hctrl2.fp.trans hfp_fsp.val
  have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl2.x19
  have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hctrl2.vregs
  have hs2_files : s2.fs.files = s0.fs.files := hctrl2.files0
  have heph_eq : Hide (((padCoins x.coins).toList.drop 160).take 32 = ephVec.toList) :=
    ⟨rfl⟩
  set ephClamped : List.Vector (BitVec 8) 32 := Ratchet.clampScalar ephVec
  set rk0Key : RootKey := bytesToKey32 (ofU8 dk.rootKey)
  set ck0Key : RootKey := bytesToKey32 (ofU8 dk.chainKey)
  set pq0Key : RootKey := bytesToKey32 (ofU8 dk.pqrKey)
  have hephClamped_def : Hide (ephClamped = Ratchet.clampScalar ephVec) := ⟨rfl⟩
  have hrk0Key_def : Hide (rk0Key = bytesToKey32 (ofU8 dk.rootKey)) := ⟨rfl⟩
  have hck0Key_def : Hide (ck0Key = bytesToKey32 (ofU8 dk.chainKey)) := ⟨rfl⟩
  have hpq0Key_def : Hide (pq0Key = bytesToKey32 (ofU8 dk.pqrKey)) := ⟨rfl⟩
  clear hx20 hx21 hx22
  clear_value fsp ephVec ephClamped rk0Key ck0Key pq0Key
  obtain ⟨sk0, sk1, sk2, sk3, _, hsk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ephClamped)
  have hs2_pc' : s2.pc = (blkPl_521).base + 4376#64 := hctrl2.pc
  have hs2_run : s2.status = .Running := hctrl2.run
  have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.pc = initPcPlaced 4448 ∧ sf.status = .Running ∧
    sf.sp = fsp ∧ sf.readReg64 .fp = s0.sp - 0x60#64 ∧
    sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
    sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
    sf.readReg64 (.gpr 23#5) = fsp + 2496#64 ∧
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
      memRegion (fsp + 2528#64) 32 ∗
      ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
      memRegion (fsp + 5632#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗
      A.pool lim st sf ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      Frame))
  ·
    conv => arg 4; rw [heph_eq.val, pointsTo_vec32_split_ends (fsp + 5632#64) ephVec]
    conv => arg 4; simp only [Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    s4_step_sync mmpl gh W hctrl2.inv ((blkPl_521).base + 4428#64)
    intro hs2a_inv
    have hclamp_fold :
        ((fsp + 5632#64) ↦₈ (ephVec.get ⟨0, by decide⟩ &&& 0xf8#8)) ∗
        ((fsp + 5633#64) ↦ₛ (ephVec.toList.drop 1).take 30) ∗
        ((fsp + 5663#64) ↦₈ ((ephVec.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8)) =
          ((fsp + 5632#64) ↦ₛ ephClamped.toList) := by
      rw [hephClamped_def.val]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        pointsTo_vec32_clamp_fold (fsp + 5632#64) ephVec
    have hsk_5632 : ((fsp + 5632#64) ↦ₛ ephClamped.toList) =
        ((fsp + 5632#64) ↦₆₄ sk0) ∗ ((fsp + 5640#64) ↦₆₄ sk1) ∗
        ((fsp + 5648#64) ↦₆₄ sk2) ∗ ((fsp + 5656#64) ↦₆₄ sk3) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 5632#64)
    have hsk_4064 : ((fsp + 4064#64) ↦ₛ ephClamped.toList) =
        ((fsp + 4064#64) ↦₆₄ sk0) ∗ ((fsp + 4072#64) ↦₆₄ sk1) ∗
        ((fsp + 4080#64) ↦₆₄ sk2) ∗ ((fsp + 4088#64) ↦₆₄ sk3) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 4064#64)
    s4_rw_pre hclamp_fold
    conv => arg 4; rw [hsk_5632, cells4_eq_memRegion32 (fsp + 4064#64)]
    s4_elim_exists u4064_0; s4_elim_exists u4064_1; s4_elim_exists u4064_2; s4_elim_exists u4064_3
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    s4_step_sync mmpl gh W hs2a_inv (lsmpl.base 200)
    intro hs3_inv
    have h5632_sk := cells4_entails_memRegion32' (fsp + 5632#64) sk0 sk1 sk2 sk3
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h5632_sk
    s4_fold_pre h5632_sk
    s4_rw_pre hsk_4064.symm
    s4_set_state sc3
    refine sepWPp_call_wpp_split_lscro hDerivePubKey
      ⟨fsp + 4064#64, ephClamped, fsp + 2496#64⟩
      (T := ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 2496#64) 32)
      (F := ?_)
      hs3_inv
      (by wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [derivePublicKeyBytesSpec, derivePublicKeyBytesBudgetSpec]
      exact Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal⟩ (Entails.of_eq (by s4_ac_rfl))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs hs4_inv
    dsimp only [derivePublicKeyBytesSpec, derivePublicKeyBytesBudgetSpec]
    s4_pure_elim
    rintro ⟨hs4_tr_eq, hvm4⟩
    have hpool4 : A.pool lim st sc3 = A.pool lim st s4 :=
      (A.pool_transport lim st sc3 s4 hvm4).symm
    s4_rw_pre hpool4
    clear hpool4 hvm4 sc3
    have hs3_sp_eq := lscro_sp_eq hs3_inv fsp (by wp_norm_goal)
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
    have hs4_fp : s4.readReg64 .fp = s0.sp - 0x60#64 :=
      (hs4_cs.gpr ⟨29, by decide⟩).trans (by rw [hfp_fsp.val]; wp_norm_goal)
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs4_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs4_x22 : s4.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs4_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs4_x23 : s4.readReg64 (.gpr 23#5) = fsp + 2496#64 :=
      (hs4_cs.gpr ⟨23, by decide⟩).trans (by wp_norm_goal)
    have hs4_x25 : s4.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs4_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
      hs4_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs2_vr)
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans (by wp_norm_goal)
    have hs4_pc_init : s4.pc = initPcPlaced 4448 := by
      dsimp only [initPcPlaced, initEntryPlaced]; rw [hs4_pc]; wp_norm_goal; rfl
    apply SepWPp.of_sepWP_ret
    apply SepWP.done hs4_pc_init hs4_run
    exact ⟨hs4_pc_init, hs4_run, hs4_sp', hs4_fp, hs4_x19, hs4_x20, hs4_x21, hs4_x22,
      hs4_x23, hs4_x25, hs4_vr, hs4_inv, hs4_tr, Entails.of_eq (by s4_ac_rfl)⟩
  · intro sf Pf hsteps
      ⟨hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hx22f, hx23f, hx25f, hvrf, hinvf, htrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq (traceFsSound_initPlaced mmpl gh W) hsteps
        (htrf.trans htr2.symm)).trans hs2_files
    exact ⟨htrf, ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl2.spAligned⟩,
      hx20f, hx21f, hx22f, hx23f, hx25f, hentf⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudgetAux

end
