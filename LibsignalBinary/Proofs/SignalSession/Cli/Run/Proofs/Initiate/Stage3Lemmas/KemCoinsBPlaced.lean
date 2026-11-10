/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 3 KEM Seed Unroll Part B (`[LibsignalPlacement]`, `+0x0c48 → +0x0dec`: Coin Draws `7..21`)

Relocatable `[LibsignalPlacement]` proof of unrolled 4-byte coin draws `7..21`.
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

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced
  coinWord padCoins stage3KeySlotsAt dhPrefix dhRemAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

set_option maxHeartbeats 1200000 in
theorem kem_coins_b_placed_ok [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {S : RunSem} {x : InitGhost} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sc : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 sc 0xc48) (htr : sc.trace = s0.trace)
    (hx20 : sc.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sc.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ sd : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiatePlaced s0 sd 0xdec → sd.trace = s0.trace →
      sd.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sd.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sd
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 120 ∗
          A.pool ∗ stackAt fsp cliCoinsFillStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - cliCoinsFillStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 8 ∗
          ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
          ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
          ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
          ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
          ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
          ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
          ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗
          ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
          ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗
          ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
          ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗
          ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
          ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗
          ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
          ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗
          ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
          ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗
          ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
          ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗
          ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
          ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗
          ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗
          ((fsp + 0x08#64) ↦₃₂ z23) ∗
          memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sc
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 60 ∗
        A.pool ∗ stackAt fsp cliCoinsFillStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) ∗
        A.live secretsPtr 192 1 ∗
        (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗
        memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗
        ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗
        ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗
        ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ z6) ∗ ((fsp + 0x48#64) ↦₃₂ z7) ∗
        ((fsp + 0x44#64) ↦₃₂ z8) ∗ ((fsp + 0x40#64) ↦₃₂ z9) ∗
        ((fsp + 0x3c#64) ↦₃₂ z10) ∗ ((fsp + 0x38#64) ↦₃₂ z11) ∗
        ((fsp + 0x34#64) ↦₃₂ z12) ∗ ((fsp + 0x30#64) ↦₃₂ z13) ∗
        ((fsp + 0x2c#64) ↦₃₂ z14) ∗ ((fsp + 0x28#64) ↦₃₂ z15) ∗
        ((fsp + 0x24#64) ↦₃₂ z16) ∗ ((fsp + 0x20#64) ↦₃₂ z17) ∗
        ((fsp + 0x1c#64) ↦₃₂ z18) ∗ ((fsp + 0x18#64) ↦₃₂ z19) ∗
        ((fsp + 0x14#64) ↦₃₂ z20) ∗ ((fsp + 0x10#64) ↦₃₂ z21) ∗
        ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 6 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 7 (by decide) (by decide)
    0xc48 0xc64 0x4c#64 z6 _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_8 hctrl_8 htr8 hx20_8 hx21_8 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 8 (by decide) (by decide)
    0xc64 0xc80 0x48#64 z7 _ hctrl_8 htr8 hx20_8 hx21_8 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_9 hctrl_9 htr9 hx20_9 hx21_9 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 9 (by decide) (by decide)
    0xc80 0xc9c 0x44#64 z8 _ hctrl_9 htr9 hx20_9 hx21_9 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_10 hctrl_10 htr10 hx20_10 hx21_10 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 10 (by decide) (by decide)
    0xc9c 0xcb8 0x40#64 z9 _ hctrl_10 htr10 hx20_10 hx21_10 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_11 hctrl_11 htr11 hx20_11 hx21_11 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 11 (by decide) (by decide)
    0xcb8 0xcd4 0x3c#64 z10 _ hctrl_11 htr11 hx20_11 hx21_11 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_12 hctrl_12 htr12 hx20_12 hx21_12 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 12 (by decide) (by decide)
    0xcd4 0xcf0 0x38#64 z11 _ hctrl_12 htr12 hx20_12 hx21_12 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_13 hctrl_13 htr13 hx20_13 hx21_13 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 13 (by decide) (by decide)
    0xcf0 0xd0c 0x34#64 z12 _ hctrl_13 htr13 hx20_13 hx21_13 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_14 hctrl_14 htr14 hx20_14 hx21_14 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 14 (by decide) (by decide)
    0xd0c 0xd28 0x30#64 z13 _ hctrl_14 htr14 hx20_14 hx21_14 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_15 hctrl_15 htr15 hx20_15 hx21_15 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 15 (by decide) (by decide)
    0xd28 0xd44 0x2c#64 z14 _ hctrl_15 htr15 hx20_15 hx21_15 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_16 hctrl_16 htr16 hx20_16 hx21_16 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 16 (by decide) (by decide)
    0xd44 0xd60 0x28#64 z15 _ hctrl_16 htr16 hx20_16 hx21_16 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_17 hctrl_17 htr17 hx20_17 hx21_17 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 17 (by decide) (by decide)
    0xd60 0xd7c 0x24#64 z16 _ hctrl_17 htr17 hx20_17 hx21_17 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_18 hctrl_18 htr18 hx20_18 hx21_18 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 18 (by decide) (by decide)
    0xd7c 0xd98 0x20#64 z17 _ hctrl_18 htr18 hx20_18 hx21_18 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_19 hctrl_19 htr19 hx20_19 hx21_19 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 19 (by decide) (by decide)
    0xd98 0xdb4 0x1c#64 z18 _ hctrl_19 htr19 hx20_19 hx21_19 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_20 hctrl_20 htr20 hx20_20 hx21_20 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 20 (by decide) (by decide)
    0xdb4 0xdd0 0x18#64 z19 _ hctrl_20 htr20 hx20_20 hx21_20 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_21 hctrl_21 htr21 hx20_21 hx21_21 => ?_
  refine s3_draw_to_slot_placed hh @hCoins hcoinsLt 21 (by decide) (by decide)
    0xdd0 0xdec 0x14#64 z20 _ hctrl_21 htr21 hx20_21 hx21_21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_22 hctrl_22 htr22 hx20_22 hx21_22 => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext s_22 hctrl_22 htr22 hx20_22 hx21_22)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
