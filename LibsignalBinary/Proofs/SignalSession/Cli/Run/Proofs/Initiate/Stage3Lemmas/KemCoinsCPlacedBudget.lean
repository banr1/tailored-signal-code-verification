/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsCPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 KEM Seed Unroll Part C (`[LibsignalPlacement]`, `+0x0dec → +0x0ee8`)

Advances `+0x0dec → +0x0ee8` across unrolled 4-byte coin draws `22..31` (scratch slots `22..24` and
callee-saved GPR draws `25..31`) under `RustCliAllocBudget M` (`0` heap events).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InInitiatePlaced cliCoinsFillStack cliCoinsFillStackPlaced coinsCursorAtPlaced initProgPlaced
   stage3KeySlotsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (coinWord dhLenWord dhPrefix dhRemAt sepWPp_conseq_oom)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsCPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
  (coinsFill_cli_placed_ok s3_coins_fill4_placed_at s3_draw_to_slot_placed_at)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
  coinWord padCoins stage3KeySlotsAt dhPrefix dhRemAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## Unrolled Draw-to-Slot and Draw-to-Register Helpers -/

theorem s3_draw_to_slot_pool_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      s.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      s.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((s.sp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt s.sp cfStk ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cfStk ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
            sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cfStk ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → VmPreserved s sm → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cfStk ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  refine s3_draw_to_slot_placed_at cfStk hh hCall hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot
    (A.pool lim st s ∗ F) hctrl htr hx20 hx21 hpanic hstep
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm; dsimp only; intro hctrl' hvm htr' hx20' hx21'
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hvm htr' hx20' hx21')

/-- Combined block+call step for coin draw `i ∈ [25, 31]` loading `w_{i-1}` into a GPR. -/
theorem s3_draw_to_reg_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cfStk ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cfStk ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cfStk ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → VmPreserved s s' → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cfStk ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call_vm_placed hh (lsmpl.base 618) k_out
    (Φ := fun sm => sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in := hctrl.pc
    rw [hfsp]
    exact hstep F halign hpc hctrl.run
  · intro sm hvm_m hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hΨ⟩
    rw [← hfsp] at hx0m ⊢
    refine s3_coins_fill4_placed_at cfStk hh hCall hcoinsLt i hi F
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' hvm' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext sm s' hctrl' (hvm_m.trans hvm') (htr'.trans (htrm.trans htr)) hcs' hΨ

theorem s3_draw_to_reg_pool_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cfStk ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cfStk ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cfStk ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → VmPreserved s s' → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (A.pool lim st s' ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cfStk ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  refine s3_draw_to_reg_placed_at cfStk hh hCall hcoinsLt i hi_prev hi k_in k_out Ψ
    (A.pool lim st s ∗ F) hctrl htr hpanic hstep
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm s'; dsimp only; intro hctrl' hvm htr' hcs' hΨ
  have hpool : A.pool lim st s = A.pool lim st s' := (A.pool_transport lim st s s' hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm s' hctrl' hvm htr' hcs' hΨ)

theorem s3_draw_to_reg_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → VmPreserved s s' → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_reg_placed_at cliCoinsFillStack hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt i hi_prev hi k_in k_out Ψ F hctrl htr hpanic hstep hpre hnext

theorem s3_draw_to_reg_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (A.pool lim st s' ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_reg_pool_placed_at cliCoinsFillStack hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt i hi_prev hi k_in k_out Ψ st F hctrl htr hpanic hstep hpre
    fun sm s' hctrl' _ htr' hcs' hΨ => hnext sm s' hctrl' htr' hcs' hΨ

theorem s3_draw_to_reg_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStackPlaced ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStackPlaced ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → VmPreserved s s' → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_reg_placed_at cliCoinsFillStackPlaced hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt i hi_prev hi k_in k_out Ψ F hctrl htr hpanic hstep hpre hnext

theorem s3_draw_to_reg_hooks_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStackPlaced ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStackPlaced ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 s' k_out → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s'
        (A.pool lim st s' ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_reg_pool_placed_at cliCoinsFillStackPlaced hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt i hi_prev hi k_in k_out Ψ st F hctrl htr hpanic hstep hpre
    fun sm s' hctrl' _ htr' hcs' hΨ => hnext sm s' hctrl' htr' hcs' hΨ

/-! ## KEM Seed Unroll Part C (`+0x0dec → +0x0ee8`, Draws `22..31`) -/

set_option maxHeartbeats 1600000 in
/-- Stack-parameterized Stage 3 KEM seed unroll Part C (`+0x0dec → +0x0ee8`, draws `22..31`). -/
theorem kem_coins_c_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 se 0xee8 → VmPreserved sd se → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st se ∗ stackAt fsp cfStk ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cfStk) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
          ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
          ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
          ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
          ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
          ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
          ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
          ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 120 ∗
        A.pool lim st sd ∗ stackAt fsp cfStk ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cfStk) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗
        ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine s3_draw_to_slot_pool_placed_at cfStk hh hCall hcoinsLt 22 (by decide) (by decide)
    0xdec 0xe08 0x10#64 z21 st _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_23 hctrl_23 hvm23 htr23 hx20_23 hx21_23 => ?_
  refine s3_draw_to_slot_pool_placed_at cfStk hh hCall hcoinsLt 23 (by decide) (by decide)
    0xe08 0xe24 0x0c#64 z22 st _ hctrl_23 htr23 hx20_23 hx21_23 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_24 hctrl_24 hvm24 htr24 hx20_24 hx21_24 => ?_
  refine s3_draw_to_slot_pool_placed_at cfStk hh hCall hcoinsLt 24 (by decide) (by decide)
    0xe24 0xe40 0x08#64 z23 st _ hctrl_24 htr24 hx20_24 hx21_24 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_25 hctrl_25 hvm25 htr25 hx20_25 hx21_25 => ?_
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 25 (by decide) (by decide) 0xe40 0xe58
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64)
    st _ hctrl_25 htr25 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_25 hx21_25 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_25 hx21_25
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_25, arm64_norm, wp_norm], by simp only [hx21_25, arm64_norm, wp_norm],
             by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm25 s_26 hctrl_26 hvm26 htr26 hcs26 ⟨hx20m25, hx21m25, hx25m25⟩ => ?_
  have hx20_26 := hcs26.2.1.trans hx20m25; have hx21_26 := hcs26.2.2.1.trans hx21m25
  have hx25_26 := hcs26.2.2.2.2.2.2.1.trans hx25m25
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 26 (by decide) (by decide) 0xe58 0xe70
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64)
    st _ hctrl_26 htr26 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_26 hx21_26 hx25_26 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_26 hx21_26 hx25_26
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_26, arm64_norm, wp_norm], by simp only [hx21_26, arm64_norm, wp_norm],
             by simp only [hx25_26, arm64_norm, wp_norm], by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm26 s_27 hctrl_27 hvm27 htr27 hcs27 ⟨hx20m26, hx21m26, hx25m26, hx22m26⟩ => ?_
  have hx20_27 := hcs27.2.1.trans hx20m26; have hx21_27 := hcs27.2.2.1.trans hx21m26
  have hx25_27 := hcs27.2.2.2.2.2.2.1.trans hx25m26; have hx22_27 := hcs27.2.2.2.1.trans hx22m26
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 27 (by decide) (by decide) 0xe70 0xe88
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64)
    st _ hctrl_27 htr27 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_27 hx21_27 hx25_27 hx22_27 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_27 hx21_27 hx25_27 hx22_27
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_27, arm64_norm, wp_norm], by simp only [hx21_27, arm64_norm, wp_norm],
             by simp only [hx25_27, arm64_norm, wp_norm], by simp only [hx22_27, arm64_norm, wp_norm],
             by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm27 s_28 hctrl_28 hvm28 htr28 hcs28 ⟨hx20m27, hx21m27, hx25m27, hx22m27, hx26m27⟩ => ?_
  have hx20_28 := hcs28.2.1.trans hx20m27; have hx21_28 := hcs28.2.2.1.trans hx21m27
  have hx25_28 := hcs28.2.2.2.2.2.2.1.trans hx25m27; have hx22_28 := hcs28.2.2.2.1.trans hx22m27
  have hx26_28 := hcs28.2.2.2.2.2.2.2.1.trans hx26m27
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 28 (by decide) (by decide) 0xe88 0xea0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64)
    st _ hctrl_28 htr28 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_28 hx21_28 hx25_28 hx22_28 hx26_28 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_28 hx21_28 hx25_28 hx22_28 hx26_28
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_28, arm64_norm, wp_norm], by simp only [hx21_28, arm64_norm, wp_norm],
             by simp only [hx25_28, arm64_norm, wp_norm], by simp only [hx22_28, arm64_norm, wp_norm],
             by simp only [hx26_28, arm64_norm, wp_norm], by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm28 s_29 hctrl_29 hvm29 htr29 hcs29 ⟨hx20m28, hx21m28, hx25m28, hx22m28, hx26m28, hx23m28⟩ => ?_
  have hx20_29 := hcs29.2.1.trans hx20m28; have hx21_29 := hcs29.2.2.1.trans hx21m28
  have hx25_29 := hcs29.2.2.2.2.2.2.1.trans hx25m28; have hx22_29 := hcs29.2.2.2.1.trans hx22m28
  have hx26_29 := hcs29.2.2.2.2.2.2.2.1.trans hx26m28; have hx23_29 := hcs29.2.2.2.2.1.trans hx23m28
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 29 (by decide) (by decide) 0xea0 0xeb8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64)
    st _ hctrl_29 htr29 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_29, arm64_norm, wp_norm], by simp only [hx21_29, arm64_norm, wp_norm],
             by simp only [hx25_29, arm64_norm, wp_norm], by simp only [hx22_29, arm64_norm, wp_norm],
             by simp only [hx26_29, arm64_norm, wp_norm], by simp only [hx23_29, arm64_norm, wp_norm],
             by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm29 s_30 hctrl_30 hvm30 htr30 hcs30 ⟨hx20m29, hx21m29, hx25m29, hx22m29, hx26m29, hx23m29, hx27m29⟩ => ?_
  have hx20_30 := hcs30.2.1.trans hx20m29; have hx21_30 := hcs30.2.2.1.trans hx21m29
  have hx25_30 := hcs30.2.2.2.2.2.2.1.trans hx25m29; have hx22_30 := hcs30.2.2.2.1.trans hx22m29
  have hx26_30 := hcs30.2.2.2.2.2.2.2.1.trans hx26m29; have hx23_30 := hcs30.2.2.2.2.1.trans hx23m29
  have hx27_30 := hcs30.2.2.2.2.2.2.2.2.1.trans hx27m29
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 30 (by decide) (by decide) 0xeb8 0xed0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64)
    st _ hctrl_30 htr30 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_30, arm64_norm, wp_norm], by simp only [hx21_30, arm64_norm, wp_norm],
             by simp only [hx25_30, arm64_norm, wp_norm], by simp only [hx22_30, arm64_norm, wp_norm],
             by simp only [hx26_30, arm64_norm, wp_norm], by simp only [hx23_30, arm64_norm, wp_norm],
             by simp only [hx27_30, arm64_norm, wp_norm], by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm30 s_31 hctrl_31 hvm31 htr31 hcs31 ⟨hx20m30, hx21m30, hx25m30, hx22m30, hx26m30, hx23m30, hx27m30, hx28m30⟩ => ?_
  have hx20_31 := hcs31.2.1.trans hx20m30; have hx21_31 := hcs31.2.2.1.trans hx21m30
  have hx25_31 := hcs31.2.2.2.2.2.2.1.trans hx25m30; have hx22_31 := hcs31.2.2.2.1.trans hx22m30
  have hx26_31 := hcs31.2.2.2.2.2.2.2.1.trans hx26m30; have hx23_31 := hcs31.2.2.2.2.1.trans hx23m30
  have hx27_31 := hcs31.2.2.2.2.2.2.2.2.1.trans hx27m30
  have hx28_31 := hcs31.2.2.2.2.2.2.2.2.2.1.trans hx28m30
  refine s3_draw_to_reg_pool_placed_at cfStk hh hCall hcoinsLt 31 (by decide) (by decide) 0xed0 0xee8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64)
    st _ hctrl_31 htr31 hpanic
    (by intro G halign hpc hrun
        try dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31 ⊢
        try simp only [arm64_norm, wp_norm] at hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31
        by_vm_steps (
          wp_steps
          exact s3_done_call_vm (by wp_norm_lhs)
            (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
            ⟨by wp_norm_goal, by wp_norm_goal,
             by simp only [hx20_31, arm64_norm, wp_norm], by simp only [hx21_31, arm64_norm, wp_norm],
             by simp only [hx25_31, arm64_norm, wp_norm], by simp only [hx22_31, arm64_norm, wp_norm],
             by simp only [hx26_31, arm64_norm, wp_norm], by simp only [hx23_31, arm64_norm, wp_norm],
             by simp only [hx27_31, arm64_norm, wp_norm], by simp only [hx28_31, arm64_norm, wp_norm],
             by wp_norm_goal⟩
            (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
            (hlr := by (try wp_norm_goal); try (clear * -; bv_omega))))
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm31 se hctrl_e hvm_e htr_e hcs_e ⟨hx20m31, hx21m31, hx25m31, hx22m31, hx26m31, hx23m31, hx27m31, hx28m31, hx24m31⟩ => ?_
  have hvm_all : VmPreserved sd se :=
    hvm23.trans (hvm24.trans (hvm25.trans (hvm26.trans (hvm27.trans (hvm28.trans
      (hvm29.trans (hvm30.trans (hvm31.trans hvm_e))))))))
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext se hctrl_e hvm_all htr_e
      (hcs_e.2.1.trans hx20m31) (hcs_e.2.2.1.trans hx21m31)
      (hcs_e.2.2.2.2.2.2.1.trans hx25m31) (hcs_e.2.2.2.1.trans hx22m31)
      (hcs_e.2.2.2.2.2.2.2.1.trans hx26m31) (hcs_e.2.2.2.2.1.trans hx23m31)
      (hcs_e.2.2.2.2.2.2.2.2.1.trans hx27m31)
      (hcs_e.2.2.2.2.2.2.2.2.2.1.trans hx28m31)
      (hcs_e.2.2.2.2.2.1.trans hx24m31))

theorem kem_coins_c_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st se ∗ stackAt fsp cliCoinsFillStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
          ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
          ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
          ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
          ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
          ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
          ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
          ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 120 ∗
        A.pool lim st sd ∗ stackAt fsp cliCoinsFillStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗
        ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_coins_c_placed_ok_at cliCoinsFillStack hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt hpanic hctrl htr hx20 hx21
    fun se hctrl_e _ => hnext se hctrl_e

theorem kem_coins_c_placed_placedStack_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st se ∗ stackAt fsp cliCoinsFillStackPlaced ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
          ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
          ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
          ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
          ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
          ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
          ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
          ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 120 ∗
        A.pool lim st sd ∗ stackAt fsp cliCoinsFillStackPlaced ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗
        ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_coins_c_placed_ok_at cliCoinsFillStackPlaced hh
    (hCoins (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt hpanic hctrl htr hx20 hx21
    fun se hctrl_e _ => hnext se hctrl_e

theorem kem_coins_c_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 st : M.σ} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st se ∗ stackAt fsp cliCoinsFillStackPlaced ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
          ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
          ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
          ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
          ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
          ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
          ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
          ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 120 ∗
        A.pool lim st sd ∗ stackAt fsp cliCoinsFillStackPlaced ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗
        ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_coins_c_placed_ok_at cliCoinsFillStackPlaced hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt hpanic hctrl htr hx20 hx21
    fun se hctrl_e _ => hnext se hctrl_e

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsCPlacedBudget
