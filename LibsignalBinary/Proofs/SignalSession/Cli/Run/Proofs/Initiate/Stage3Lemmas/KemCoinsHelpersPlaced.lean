/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 3 KEM Seed Unroll Helpers (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` 4-byte `signal_session_coins_fill` draw helpers shared across
`KemCoinsAPlaced`, `KemCoinsBPlaced`, and `KemCoinsCPlaced`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

/-- Reusable 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draw helper for step `i < 32`. -/
theorem s3_coins_fill4_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 618)
    (hlr : s.readReg64 .lr = initPcPlaced k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiatePlaced s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  let g : CoinsFillGhost := ⟨fsp + 0x1600#64, 4, x.coinsP, x.coins, 32 + 4 * i⟩
  have hcall := hCoins (le_refl cliCoinsFillStack) (by decide)
  have hpre' : P ⊢ (coinsFillSpecPlacedW3 cliCoinsFillStack).pre g s ∗ F := by
    refine Entails.trans hpre ?_
    dsimp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, g]
    simp only [sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, hcoinsLt, by unfold initiateTapeLen; omega⟩ ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ 0#32))) ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (Entails.pure_right hctrl.inv (Entails.refl _)))))
    exact Entails.of_eq (by dsimp only [fsp]; try ac_rfl)
  refine s3_call_placed hh hcall g F hctrl htr hpc hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [coinsFillSpecPlacedW3, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, g, sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨htrm, _⟩ => ?_
    rw [show (32 + 4 * i) + 4 = 32 + 4 * (i + 1) from by omega,
        coinDraw4_eq_pointsTo32 (fsp + 0x1600#64) (padCoins x.coins) i hi]
    exact sepWPp_conseq_oom
      (Entails.of_eq (by dsimp only [fsp]))
      (hnext sm (hof htrm) hcsm htrm)
/-- Combined block+call step for unrolled coin draw `i ∈ [1, 24]` storing `w_{i-1}` at `slotOff`. -/
theorem s3_draw_to_slot_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s k_in) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
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
      InInitiatePlaced s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        (coinsCursorAtPlaced x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call_placed hh (lsmpl.base 618) k_out
    (Φ := fun sm =>
      sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : s.pc = (blkPl_521).base + BitVec.ofNat 64 k_in := hctrl.pc
    rw [hfsp]
    exact hstep F halign hpc hctrl.run (by rwa [← hfsp]) (by rwa [← hfsp])
  · intro sm hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hx20m, hx21m⟩
    rw [← hfsp] at hx0m hx20m hx21m ⊢
    refine s3_coins_fill4_placed hh @hCoins hcoinsLt i hi
      (((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext s' hctrl' (htr'.trans (htrm.trans htr))
      (hcs'.2.1.trans hx20m) (hcs'.2.2.1.trans hx21m)

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
  wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by (try simp only [hx22, arm64_norm, wp_norm]); sep_frame)
    ⟨by wp_norm_goal, by simp only [arm64_norm, wp_norm], by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

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
  wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by sep_frame)
    ⟨by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
