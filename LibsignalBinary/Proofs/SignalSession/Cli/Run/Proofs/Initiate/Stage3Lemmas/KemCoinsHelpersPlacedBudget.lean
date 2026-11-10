/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 KEM Seed Unroll Helpers (`[LibsignalPlacement]`)

4-byte `signal_session_coins_fill` (Block `618`) call combinators and combined block+call draw
helpers preserving `VmPreserved` and `A.pool` across `KemCoinsA/B/CPlacedBudget`.
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
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E (initiateTapeLen)
open CryptoVerification.E2E.Pqxdh.ResponderCore (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (memcpyName)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (CoinsFillGhost InInitiatePlaced cliCoinsFillStack cliCoinsFillStackPlaced coinsCursorAtPlaced initPcPlaced initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas (coinDraw4_eq_pointsTo32 coinWord sepWPp_conseq_oom sepWPp_pure_elim_oom)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3 signal_session_coins_fill_placed_ok_at_init)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_to_call_vm_placed s3_done_call_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (s3_call_placed)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-! ## Block `618` (`signal_session_coins_fill`) Discharge -/

/-- Discharges Block `618` (`coinsFillSpecPlacedW3`) directly from `RunHooksPlaced`. -/
theorem coinsFill_cli_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {cStk : Nat} (hstk : cliCoinsFillStackPlaced ≤ cStk) (hstk64 : cStk ≤ 2 ^ 63) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)) := by
  refine subroutine_ok_mono
    (signal_session_coins_fill_placed_ok_at_init mmpl gh W hh.allocFs hstk hstk64)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsRoCl, withLsCodeRoLoaded] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-! ## 4-Byte `signal_session_coins_fill` Draw Helpers -/

/-- Stack-parameterized 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draw helper (`i < 32`). -/
theorem s3_coins_fill4_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cfStk ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      VmPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cfStk ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  let g : CoinsFillGhost := ⟨fsp + 0x1600#64, 4, x.coinsP, x.coins, 32 + 4 * i⟩
  have hpre' : P ⊢ (coinsFillSpecPlacedW3 cfStk).pre g s ∗ F := by
    refine Entails.trans hpre ?_
    dsimp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded, g]
    simp only [sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, hcoinsLt, by unfold initiateTapeLen; omega⟩ ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ 0#32))) ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (Entails.pure_right hctrl.inv (Entails.refl _)))))
    exact Entails.of_eq (by dsimp only [fsp])
  refine s3_call_placed hh hCall g F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [coinsFillSpecPlacedW3, withLsCodeRoLoaded, g, sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨htrm, _, hvm⟩ => ?_
    rw [show (32 + 4 * i) + 4 = 32 + 4 * (i + 1) from by omega,
        coinDraw4_eq_pointsTo32 (fsp + 0x1600#64) (padCoins x.coins) i hi]
    exact sepWPp_conseq_oom
      (Entails.of_eq (by dsimp only [fsp]))
      (hnext sm (hof htrm) hcsm hvm htrm)

theorem s3_coins_fill4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      VmPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_coins_fill4_placed_at cliCoinsFillStack hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt i hi F hctrl htr hpc hlr hx0 hx1 hpanic hpre hnext

theorem s3_coins_fill4_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStack ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  refine s3_coins_fill4_placed hh @hCoins hcoinsLt i hi (A.pool lim st s ∗ F)
    hctrl htr hpc hlr hx0 hx1 hpanic
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm hctrl' hcsm hvm htrm
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hcsm htrm)

theorem s3_coins_fill4_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm →
      VmPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStackPlaced ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_coins_fill4_placed_at cliCoinsFillStackPlaced hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt i hi F hctrl htr hpc hlr hx0 hx1 hpanic hpre hnext

theorem s3_coins_fill4_hooks_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      A.pool lim st s ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStackPlaced ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  refine s3_coins_fill4_hooks_placed hh hcoinsLt i hi (A.pool lim st s ∗ F)
    hctrl htr hpc hlr hx0 hx1 hpanic
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm hctrl' hcsm hvm htrm
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' hcsm htrm)

/-! ## Combined Block + Call Draw Helpers -/

/-- Stack-parameterized combined block+call draw helper (`i ∈ [1, 24]`) storing `w_{i-1}` at `slotOff`. -/
theorem s3_draw_to_slot_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (cfStk : Nat)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
      (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cfStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
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
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cfStk ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → VmPreserved s sm → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cfStk ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call_vm_placed hh (lsmpl.base 618) k_out
    (Φ := fun sm =>
      sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in := hctrl.pc
    rw [hfsp]
    exact hstep F halign hpc hctrl.run (by rwa [← hfsp]) (by rwa [← hfsp])
  · intro sm hvm_m hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hx20m, hx21m⟩
    rw [← hfsp] at hx0m hx20m hx21m ⊢
    refine s3_coins_fill4_placed_at cfStk hh hCall hcoinsLt i hi
      (((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' hvm' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext s' hctrl' (hvm_m.trans hvm') (htr'.trans (htrm.trans htr))
      (hcs'.2.1.trans hx20m) (hcs'.2.2.1.trans hx21m)

theorem s3_draw_to_slot_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
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
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
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
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → VmPreserved s sm → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_slot_placed_at cliCoinsFillStack hh
    (hCoins (le_refl cliCoinsFillStack) (by decide))
    hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot F
    hctrl htr hx20 hx21 hpanic hstep hpre hnext

theorem s3_draw_to_slot_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
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
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
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
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot
    (A.pool lim st s ∗ F) hctrl htr hx20 hx21 hpanic hstep
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm; dsimp only; intro hctrl' hvm htr' hx20' hx21'
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' htr' hx20' hx21')

theorem s3_draw_to_slot_hooks_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
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
          stackAt s.sp cliCoinsFillStackPlaced ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStackPlaced ∗ G) ∧
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
        coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → VmPreserved s sm → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom :=
  s3_draw_to_slot_placed_at cliCoinsFillStackPlaced hh
    (coinsFill_cli_placed_ok hh (le_refl cliCoinsFillStackPlaced) (by decide))
    hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot F
    hctrl htr hx20 hx21 hpanic hstep hpre hnext

theorem s3_draw_to_slot_hooks_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {x : InitGhost} {st0 : M.σ} {stk : Nat}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
          stackAt s.sp cliCoinsFillStackPlaced ∗ G)
        (fun sm Pm =>
          VmPreserved s sm ∧
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStackPlaced ∗ G) ∧
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
          stackAt fsp cliCoinsFillStackPlaced ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiatePlaced s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (A.pool lim st sm ∗ coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStackPlaced ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp oom := by
  dsimp only at hpre hnext
  refine s3_draw_to_slot_hooks_placed hh hcoinsLt i hi_prev hi k_in k_out slotOff oldSlot
    (A.pool lim st s ∗ F) hctrl htr hx20 hx21 hpanic hstep
    (Entails.trans hpre (Entails.of_eq (by sep_ac_rfl))) ?_
  intro sm; dsimp only; intro hctrl' hvm htr' hx20' hx21'
  have hpool : A.pool lim st s = A.pool lim st sm := (A.pool_transport lim st s sm hvm).symm
  exact sepWPp_conseq_oom
    (Entails.of_eq (by rw [hpool]; sep_ac_rfl))
    (hnext sm hctrl' htr' hx20' hx21')

/-! ## Entry Basic-Block Steppers (`+0x0b6c → +0x0ba0`) -/

theorem s3_step_b6c_b8c_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {s : State}
    (pqspkPtr z70 : BitVec 64) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0xb6c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 0x408#64) :
    SepWP (initProgPlaced mmpl gh W) (lsρ memcpyName) s
      (((s.sp + 0x70#64) ↦₆₄ z70) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x70#64) ↦₆₄ (s.sp + 0x408#64)) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
          ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 0xb8c ∧
        (sm.readReg64 .x0 = s.sp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
          sm.readReg64 .x2 = 1568#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
  try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
  by_vm_steps (
    wp_steps
    exact s3_done_call_vm (by wp_norm_lhs)
      (by (try simp only [hx22, arm64_norm, wp_norm]); sep_frame)
      ⟨by wp_norm_goal, by simp only [arm64_norm, wp_norm], by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
      (hpc := by wp_norm_goal)
      (hlr := by wp_norm_goal))

theorem s3_step_b8c_ba0_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {s : State}
    (z1600 : BitVec 32) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 0xb8c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64) :
    SepWP (initProgPlaced mmpl gh W) (lsmpl.base 618) s
      (((s.sp + 0x1600#64) ↦₃₂ z1600) ∗ G)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (blkPl_521).base + BitVec.ofNat 64 0xba0 ∧
        (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
  try simp only [arm64_norm, wp_norm] at hx20 hx21
  by_vm_steps (
    wp_steps
    exact s3_done_call_vm (by wp_norm_lhs)
      (by sep_frame)
      ⟨by wp_norm_goal, by wp_norm_goal,
       by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩
      (hpc := by wp_norm_goal)
      (hlr := by wp_norm_goal))

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
