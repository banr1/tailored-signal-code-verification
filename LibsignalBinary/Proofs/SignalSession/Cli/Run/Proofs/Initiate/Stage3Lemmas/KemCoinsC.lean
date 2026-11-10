/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 3 KEM Seed Unroll Part C (`+0x0dec → +0x0ee8`: Coin Draws `22..31`)

Completes unrolled 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draws `22..24` into scratch
slots `[fsp + 0x10 .. fsp + 0x08]` and draws `25..31` keeping `w_24..w_30` in `w25, w22, w26, w23,
w27, w28, w24` and `w_31` in `[fsp + 0x1600]`, advancing `coinsCursorAt` from `120` to `160`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefix coinsCursorAt coinWord
  padCoins stage3KeySlotsAt dhPrefix dhRemAt
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem s3_draw_to_reg {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {S : RunSem} {x : InitGhost} {stk : Nat} {s0 s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (F : SepProp)
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)))
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName +
          bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
        s
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm => sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiate img W s0 s' k_out → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProg img W) (s0.readReg64 .lr) s'
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call hh
    (initEntry img W +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    k_out
    (Φ := fun sm => sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp]
    exact hstep F halign hpc hctrl.run
  · intro sm hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hΨ⟩
    rw [← hfsp] at hx0m ⊢
    refine s3_coins_fill4 hh hCoins hcoinsLt i hi F
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext sm s' hctrl' (htr'.trans (htrm.trans htr)) hcs' hΨ

set_option maxHeartbeats 1200000 in
theorem kem_coins_c_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {S : RunSem} {x : InitGhost} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiate img W s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiate img W s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) se
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp cliCoinsFillStack ∗
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
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProg img W) (s0.readReg64 .lr) sd
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 120 ∗
        A.pool ∗ stackAt fsp cliCoinsFillStack ∗
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
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine s3_draw_to_slot hh hCoins hcoinsLt 22 (by decide) (by decide)
    0xdec 0xe08 0x10#64 z21 _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xdec 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_23 hctrl_23 htr23 hx20_23 hx21_23 => ?_
  refine s3_draw_to_slot hh hCoins hcoinsLt 23 (by decide) (by decide)
    0xe08 0xe24 0x0c#64 z22 _ hctrl_23 htr23 hx20_23 hx21_23 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe08 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_24 hctrl_24 htr24 hx20_24 hx21_24 => ?_
  refine s3_draw_to_slot hh hCoins hcoinsLt 24 (by decide) (by decide)
    0xe24 0xe40 0x08#64 z23 _ hctrl_24 htr24 hx20_24 hx21_24 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe24 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_25 hctrl_25 htr25 hx20_25 hx21_25 => ?_
  refine s3_draw_to_reg hh hCoins hcoinsLt 25 (by decide) (by decide) 0xe40 0xe58
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64)
    _ hctrl_25 htr25 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_25 hx21_25
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe40 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_25 hx21_25 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_25 hx21_25
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_25, arm64_norm, wp_norm], by simp only [hx21_25, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm25 s_26 hctrl_26 htr26 hcs26 ⟨hx20m25, hx21m25, hx25m25⟩ => ?_
  have hx20_26 := hcs26.2.1.trans hx20m25; have hx21_26 := hcs26.2.2.1.trans hx21m25
  have hx25_26 := hcs26.2.2.2.2.2.2.1.trans hx25m25
  refine s3_draw_to_reg hh hCoins hcoinsLt 26 (by decide) (by decide) 0xe58 0xe70
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64)
    _ hctrl_26 htr26 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_26 hx21_26 hx25_26
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe58 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_26 hx21_26 hx25_26 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_26 hx21_26 hx25_26
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_26, arm64_norm, wp_norm], by simp only [hx21_26, arm64_norm, wp_norm],
           by simp only [hx25_26, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm26 s_27 hctrl_27 htr27 hcs27 ⟨hx20m26, hx21m26, hx25m26, hx22m26⟩ => ?_
  have hx20_27 := hcs27.2.1.trans hx20m26; have hx21_27 := hcs27.2.2.1.trans hx21m26
  have hx25_27 := hcs27.2.2.2.2.2.2.1.trans hx25m26; have hx22_27 := hcs27.2.2.2.1.trans hx22m26
  refine s3_draw_to_reg hh hCoins hcoinsLt 27 (by decide) (by decide) 0xe70 0xe88
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64)
    _ hctrl_27 htr27 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_27 hx21_27 hx25_27 hx22_27
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe70 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_27 hx21_27 hx25_27 hx22_27 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_27 hx21_27 hx25_27 hx22_27
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_27, arm64_norm, wp_norm], by simp only [hx21_27, arm64_norm, wp_norm],
           by simp only [hx25_27, arm64_norm, wp_norm], by simp only [hx22_27, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm27 s_28 hctrl_28 htr28 hcs28 ⟨hx20m27, hx21m27, hx25m27, hx22m27, hx26m27⟩ => ?_
  have hx20_28 := hcs28.2.1.trans hx20m27; have hx21_28 := hcs28.2.2.1.trans hx21m27
  have hx25_28 := hcs28.2.2.2.2.2.2.1.trans hx25m27; have hx22_28 := hcs28.2.2.2.1.trans hx22m27
  have hx26_28 := hcs28.2.2.2.2.2.2.2.1.trans hx26m27
  refine s3_draw_to_reg hh hCoins hcoinsLt 28 (by decide) (by decide) 0xe88 0xea0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64)
    _ hctrl_28 htr28 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_28 hx21_28 hx25_28 hx22_28 hx26_28
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe88 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_28 hx21_28 hx25_28 hx22_28 hx26_28 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_28 hx21_28 hx25_28 hx22_28 hx26_28
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_28, arm64_norm, wp_norm], by simp only [hx21_28, arm64_norm, wp_norm],
           by simp only [hx25_28, arm64_norm, wp_norm], by simp only [hx22_28, arm64_norm, wp_norm],
           by simp only [hx26_28, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm28 s_29 hctrl_29 htr29 hcs29 ⟨hx20m28, hx21m28, hx25m28, hx22m28, hx26m28, hx23m28⟩ => ?_
  have hx20_29 := hcs29.2.1.trans hx20m28; have hx21_29 := hcs29.2.2.1.trans hx21m28
  have hx25_29 := hcs29.2.2.2.2.2.2.1.trans hx25m28; have hx22_29 := hcs29.2.2.2.1.trans hx22m28
  have hx26_29 := hcs29.2.2.2.2.2.2.2.1.trans hx26m28; have hx23_29 := hcs29.2.2.2.2.1.trans hx23m28
  refine s3_draw_to_reg hh hCoins hcoinsLt 29 (by decide) (by decide) 0xea0 0xeb8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64)
    _ hctrl_29 htr29 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xea0 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_29, arm64_norm, wp_norm], by simp only [hx21_29, arm64_norm, wp_norm],
           by simp only [hx25_29, arm64_norm, wp_norm], by simp only [hx22_29, arm64_norm, wp_norm],
           by simp only [hx26_29, arm64_norm, wp_norm], by simp only [hx23_29, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm29 s_30 hctrl_30 htr30 hcs30 ⟨hx20m29, hx21m29, hx25m29, hx22m29, hx26m29, hx23m29, hx27m29⟩ => ?_
  have hx20_30 := hcs30.2.1.trans hx20m29; have hx21_30 := hcs30.2.2.1.trans hx21m29
  have hx25_30 := hcs30.2.2.2.2.2.2.1.trans hx25m29; have hx22_30 := hcs30.2.2.2.1.trans hx22m29
  have hx26_30 := hcs30.2.2.2.2.2.2.2.1.trans hx26m29; have hx23_30 := hcs30.2.2.2.2.1.trans hx23m29
  have hx27_30 := hcs30.2.2.2.2.2.2.2.2.1.trans hx27m29
  refine s3_draw_to_reg hh hCoins hcoinsLt 30 (by decide) (by decide) 0xeb8 0xed0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64)
    _ hctrl_30 htr30 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xeb8 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_30, arm64_norm, wp_norm], by simp only [hx21_30, arm64_norm, wp_norm],
           by simp only [hx25_30, arm64_norm, wp_norm], by simp only [hx22_30, arm64_norm, wp_norm],
           by simp only [hx26_30, arm64_norm, wp_norm], by simp only [hx23_30, arm64_norm, wp_norm],
           by simp only [hx27_30, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm30 s_31 hctrl_31 htr31 hcs31 ⟨hx20m30, hx21m30, hx25m30, hx22m30, hx26m30, hx23m30, hx27m30, hx28m30⟩ => ?_
  have hx20_31 := hcs31.2.1.trans hx20m30; have hx21_31 := hcs31.2.2.1.trans hx21m30
  have hx25_31 := hcs31.2.2.2.2.2.2.1.trans hx25m30; have hx22_31 := hcs31.2.2.2.1.trans hx22m30
  have hx26_31 := hcs31.2.2.2.2.2.2.2.1.trans hx26m30; have hx23_31 := hcs31.2.2.2.2.1.trans hx23m30
  have hx27_31 := hcs31.2.2.2.2.2.2.2.2.1.trans hx27m30
  have hx28_31 := hcs31.2.2.2.2.2.2.2.2.2.1.trans hx28m30
  refine s3_draw_to_reg hh hCoins hcoinsLt 31 (by decide) (by decide) 0xed0 0xee8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64)
    _ hctrl_31 htr31 hpanic
    (by intro G halign hpc hrun
        clear * - G halign hpc hrun hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xed0 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_31, arm64_norm, wp_norm], by simp only [hx21_31, arm64_norm, wp_norm],
           by simp only [hx25_31, arm64_norm, wp_norm], by simp only [hx22_31, arm64_norm, wp_norm],
           by simp only [hx26_31, arm64_norm, wp_norm], by simp only [hx23_31, arm64_norm, wp_norm],
           by simp only [hx27_31, arm64_norm, wp_norm], by simp only [hx28_31, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm31 se hctrl_e htr_e hcs_e ⟨hx20m31, hx21m31, hx25m31, hx22m31, hx26m31, hx23m31, hx27m31, hx28m31, hx24m31⟩ => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext se hctrl_e htr_e
      (hcs_e.2.1.trans hx20m31) (hcs_e.2.2.1.trans hx21m31)
      (hcs_e.2.2.2.2.2.2.1.trans hx25m31) (hcs_e.2.2.2.1.trans hx22m31)
      (hcs_e.2.2.2.2.2.2.2.1.trans hx26m31) (hcs_e.2.2.2.2.1.trans hx23m31)
      (hcs_e.2.2.2.2.2.2.2.2.1.trans hx27m31)
      (hcs_e.2.2.2.2.2.2.2.2.2.1.trans hx28m31)
      (hcs_e.2.2.2.2.2.1.trans hx24m31))

/-! ## `CliExternsOk` Generalization (`kem_coins_c_ok_ext`) -/

set_option Elab.async false

private theorem s3c_draw_to_reg {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {stk : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32) (k_in k_out : Nat)
    (Ψ : State → Prop) (F : SepProp)
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 k_in →
      s.status = .Running →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)))
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName +
          bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
        s
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm => sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm s' : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiateExt img ext s0 s' k_out → s'.trace = s0.trace →
      CalleeSavedPreserved sm s' → Ψ sm →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s'
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' Ext.s3_block_to_call hOk
    (initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    k_out
    (Φ := fun sm => sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧ Ψ sm)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp]
    exact hstep F halign hpc hctrl.run
  · intro sm hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hΨ⟩
    rw [← hfsp] at hx0m ⊢
    refine Ext.s3_coins_fill4 hOk hCoins hcoinsLt i hi F
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext sm s' hctrl' (htr'.trans (htrm.trans htr)) hcs' hΨ

private theorem kem_coins_c1_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {R_inv : SepProp} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ s25 : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 s25 0xe40 → s25.trace = s0.trace →
      s25.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s25.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s25
        (coinsCursorAt img x.coinsP x.coins 132 ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
          ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗
          ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 24 (by decide)) ∗ R_inv)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sd
      (coinsCursorAt img x.coinsP x.coins 120 ∗
        stackAt fsp cliCoinsFillStack ∗
        ((fsp + 0x10#64) ↦₃₂ z21) ∗ ((fsp + 0x0c#64) ↦₃₂ z22) ∗ ((fsp + 0x08#64) ↦₃₂ z23) ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗ R_inv)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 22 (by decide) (by decide)
    0xdec 0xe08 0x10#64 z21 _ hctrl htr hx20 hx21 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xdec 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_23 hctrl_23 htr23 hx20_23 hx21_23 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 23 (by decide) (by decide)
    0xe08 0xe24 0x0c#64 z22 _ hctrl_23 htr23 hx20_23 hx21_23 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe08 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_24 hctrl_24 htr24 hx20_24 hx21_24 => ?_
  refine Ext.s3_draw_to_slot hOk hCoins hcoinsLt 24 (by decide) (by decide)
    0xe24 0xe40 0x08#64 z23 _ hctrl_24 htr24 hx20_24 hx21_24 hpanic
    (by intro G halign hpc hrun hx20' hx21'
        clear * - G halign hpc hrun hx20' hx21'
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe24 28
        try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20' hx21'
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20', arm64_norm, wp_norm], by simp only [hx21', arm64_norm, wp_norm]⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun s_25 hctrl_25 htr25 hx20_25 hx21_25 => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext s_25 hctrl_25 htr25 hx20_25 hx21_25)

private theorem kem_coins_c2_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost}
    {stk : Nat} {s0 s25 : State} {R_inv : SepProp} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 s25 0xe40) (htr : s25.trace = s0.trace)
    (hx20 : s25.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s25.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ s29 : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 s29 0xea0 → s29.trace = s0.trace →
      s29.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      s29.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      s29.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      s29.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      s29.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      s29.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s29
        (coinsCursorAt img x.coinsP x.coins 148 ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 28 (by decide)) ∗ R_inv)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s25
      (coinsCursorAt img x.coinsP x.coins 132 ∗
        stackAt fsp cliCoinsFillStack ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 24 (by decide)) ∗ R_inv)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 25 (by decide) (by decide) 0xe40 0xe58
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64)
    _ hctrl htr hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl.sp
        clear * - G halign hpc hrun hx20 hx21 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe40 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 hfsp ⊢
        rw [← hfsp] at hx20 hx21 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20 hx21
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm25 s_26 hctrl_26 htr26 hcs26 ⟨hx20m25, hx21m25, hx25m25⟩ => ?_
  have hx20_26 := hcs26.2.1.trans hx20m25; have hx21_26 := hcs26.2.2.1.trans hx21m25
  have hx25_26 := hcs26.2.2.2.2.2.2.1.trans hx25m25
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 26 (by decide) (by decide) 0xe58 0xe70
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64)
    _ hctrl_26 htr26 hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl_26.sp
        clear * - G halign hpc hrun hx20_26 hx21_26 hx25_26 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe58 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_26 hx21_26 hx25_26 hfsp ⊢
        rw [← hfsp] at hx20_26 hx21_26 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_26 hx21_26 hx25_26
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_26, arm64_norm, wp_norm], by simp only [hx21_26, arm64_norm, wp_norm],
           by simp only [hx25_26, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm26 s_27 hctrl_27 htr27 hcs27 ⟨hx20m26, hx21m26, hx25m26, hx22m26⟩ => ?_
  have hx20_27 := hcs27.2.1.trans hx20m26; have hx21_27 := hcs27.2.2.1.trans hx21m26
  have hx25_27 := hcs27.2.2.2.2.2.2.1.trans hx25m26; have hx22_27 := hcs27.2.2.2.1.trans hx22m26
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 27 (by decide) (by decide) 0xe70 0xe88
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64)
    _ hctrl_27 htr27 hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl_27.sp
        clear * - G halign hpc hrun hx20_27 hx21_27 hx25_27 hx22_27 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe70 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_27 hx21_27 hx25_27 hx22_27 hfsp ⊢
        rw [← hfsp] at hx20_27 hx21_27 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_27 hx21_27 hx25_27 hx22_27
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_27, arm64_norm, wp_norm], by simp only [hx21_27, arm64_norm, wp_norm],
           by simp only [hx25_27, arm64_norm, wp_norm], by simp only [hx22_27, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm27 s_28 hctrl_28 htr28 hcs28 ⟨hx20m27, hx21m27, hx25m27, hx22m27, hx26m27⟩ => ?_
  have hx20_28 := hcs28.2.1.trans hx20m27; have hx21_28 := hcs28.2.2.1.trans hx21m27
  have hx25_28 := hcs28.2.2.2.2.2.2.1.trans hx25m27; have hx22_28 := hcs28.2.2.2.1.trans hx22m27
  have hx26_28 := hcs28.2.2.2.2.2.2.2.1.trans hx26m27
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 28 (by decide) (by decide) 0xe88 0xea0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64)
    _ hctrl_28 htr28 hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl_28.sp
        clear * - G halign hpc hrun hx20_28 hx21_28 hx25_28 hx22_28 hx26_28 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xe88 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_28 hx21_28 hx25_28 hx22_28 hx26_28 hfsp ⊢
        rw [← hfsp] at hx20_28 hx21_28 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_28 hx21_28 hx25_28 hx22_28 hx26_28
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_28, arm64_norm, wp_norm], by simp only [hx21_28, arm64_norm, wp_norm],
           by simp only [hx25_28, arm64_norm, wp_norm], by simp only [hx22_28, arm64_norm, wp_norm],
           by simp only [hx26_28, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm28 s_29 hctrl_29 htr29 hcs29 ⟨hx20m28, hx21m28, hx25m28, hx22m28, hx26m28, hx23m28⟩ => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext s_29 hctrl_29 htr29
      (hcs29.2.1.trans hx20m28) (hcs29.2.2.1.trans hx21m28)
      (hcs29.2.2.2.2.2.2.1.trans hx25m28) (hcs29.2.2.2.1.trans hx22m28)
      (hcs29.2.2.2.2.2.2.2.1.trans hx26m28) (hcs29.2.2.2.2.1.trans hx23m28))

private theorem kem_coins_c3_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost}
    {stk : Nat} {s0 s29 : State} {R_inv : SepProp} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 s29 0xea0) (htr : s29.trace = s0.trace)
    (hx20 : s29.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s29.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : s29.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : s29.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : s29.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : s29.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) se
        (coinsCursorAt img x.coinsP x.coins 160 ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗ R_inv)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s29
      (coinsCursorAt img x.coinsP x.coins 148 ∗
        stackAt fsp cliCoinsFillStack ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 28 (by decide)) ∗ R_inv)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 29 (by decide) (by decide) 0xea0 0xeb8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64)
    _ hctrl htr hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl.sp
        clear * - G halign hpc hrun hx20 hx21 hx25 hx22 hx26 hx23 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xea0 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20 hx21 hx25 hx22 hx26 hx23 hfsp ⊢
        rw [← hfsp] at hx20 hx21 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20 hx21 hx25 hx22 hx26 hx23
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm],
           by simp only [hx25, arm64_norm, wp_norm], by simp only [hx22, arm64_norm, wp_norm],
           by simp only [hx26, arm64_norm, wp_norm], by simp only [hx23, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm29 s_30 hctrl_30 htr30 hcs30 ⟨hx20m29, hx21m29, hx25m29, hx22m29, hx26m29, hx23m29, hx27m29⟩ => ?_
  have hx20_30 := hcs30.2.1.trans hx20m29; have hx21_30 := hcs30.2.2.1.trans hx21m29
  have hx25_30 := hcs30.2.2.2.2.2.2.1.trans hx25m29; have hx22_30 := hcs30.2.2.2.1.trans hx22m29
  have hx26_30 := hcs30.2.2.2.2.2.2.2.1.trans hx26m29; have hx23_30 := hcs30.2.2.2.2.1.trans hx23m29
  have hx27_30 := hcs30.2.2.2.2.2.2.2.2.1.trans hx27m29
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 30 (by decide) (by decide) 0xeb8 0xed0
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64)
    _ hctrl_30 htr30 hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl_30.sp
        clear * - G halign hpc hrun hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xeb8 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30 hfsp ⊢
        rw [← hfsp] at hx20_30 hx21_30 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_30 hx21_30 hx25_30 hx22_30 hx26_30 hx23_30 hx27_30
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_30, arm64_norm, wp_norm], by simp only [hx21_30, arm64_norm, wp_norm],
           by simp only [hx25_30, arm64_norm, wp_norm], by simp only [hx22_30, arm64_norm, wp_norm],
           by simp only [hx26_30, arm64_norm, wp_norm], by simp only [hx23_30, arm64_norm, wp_norm],
           by simp only [hx27_30, arm64_norm, wp_norm], by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm30 s_31 hctrl_31 htr31 hcs31 ⟨hx20m30, hx21m30, hx25m30, hx22m30, hx26m30, hx23m30, hx27m30, hx28m30⟩ => ?_
  have hx20_31 := hcs31.2.1.trans hx20m30; have hx21_31 := hcs31.2.2.1.trans hx21m30
  have hx25_31 := hcs31.2.2.2.2.2.2.1.trans hx25m30; have hx22_31 := hcs31.2.2.2.1.trans hx22m30
  have hx26_31 := hcs31.2.2.2.2.2.2.2.1.trans hx26m30; have hx23_31 := hcs31.2.2.2.2.1.trans hx23m30
  have hx27_31 := hcs31.2.2.2.2.2.2.2.2.1.trans hx27m30
  have hx28_31 := hcs31.2.2.2.2.2.2.2.2.2.1.trans hx28m30
  refine s3c_draw_to_reg hOk hCoins hcoinsLt 31 (by decide) (by decide) 0xed0 0xee8
    (fun sm => sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
      sm.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 ∧
      sm.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64)
    _ hctrl_31 htr31 hpanic
    (by intro G halign hpc hrun
        have hfsp := hctrl_31.sp
        clear * - G halign hpc hrun hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31 hfsp
        code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
          cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xed0 24
        try dsimp only [fsp, t, BitVec.ofNat_eq_ofNat] at hpc hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31 hfsp ⊢
        rw [← hfsp] at hx20_31 hx21_31 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
        try simp only [arm64_norm, wp_norm] at hx20_31 hx21_31 hx25_31 hx22_31 hx26_31 hx23_31 hx27_31 hx28_31
        examples_hide_fetches; wp_steps
        exact s3_done_call (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)) (by wp_norm_lhs)
          (Entails.of_eq (by simp only [arm64_norm, wp_norm]))
          ⟨by wp_norm_goal, by wp_norm_goal,
           by simp only [hx20_31, arm64_norm, wp_norm], by simp only [hx21_31, arm64_norm, wp_norm],
           by simp only [hx25_31, arm64_norm, wp_norm], by simp only [hx22_31, arm64_norm, wp_norm],
           by simp only [hx26_31, arm64_norm, wp_norm], by simp only [hx23_31, arm64_norm, wp_norm],
           by simp only [hx27_31, arm64_norm, wp_norm], by simp only [hx28_31, arm64_norm, wp_norm],
           by wp_norm_goal⟩)
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    fun sm31 se hctrl_e htr_e hcs_e ⟨hx20m31, hx21m31, hx25m31, hx22m31, hx26m31, hx23m31, hx27m31, hx28m31, hx24m31⟩ => ?_
  exact sepWPp_conseq_oom
    (by (try dsimp only [fsp, t]); simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]; sep_frame)
    (hnext se hctrl_e htr_e
      (hcs_e.2.1.trans hx20m31) (hcs_e.2.2.1.trans hx21m31)
      (hcs_e.2.2.2.2.2.2.1.trans hx25m31) (hcs_e.2.2.2.1.trans hx22m31)
      (hcs_e.2.2.2.2.2.2.2.1.trans hx26m31) (hcs_e.2.2.2.2.1.trans hx23m31)
      (hcs_e.2.2.2.2.2.2.2.2.1.trans hx27m31)
      (hcs_e.2.2.2.2.2.2.2.2.2.1.trans hx28m31)
      (hcs_e.2.2.2.2.2.1.trans hx24m31))

/-- Contract-parameterized Stage 3 KEM seed unroll part C (`+0x0dec → +0x0ee8`: coin draws `22..31`)
under `CliExternsOk P0 A ext`. -/
theorem kem_coins_c_ok_ext {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {x : InitGhost} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {z21 z22 z23 : BitVec 32}
    {stk : Nat} {s0 sd : State} {Q Qp : State → SepProp → Prop}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiateExt img ext s0 sd 0xdec) (htr : sd.trace = s0.trace)
    (hx20 : sd.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : sd.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hnext : ∀ se : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      InInitiateExt img ext s0 se 0xee8 → se.trace = s0.trace →
      se.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      se.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      se.readReg64 (.gpr 25#5) = (coinWord t 24 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 22#5) = (coinWord t 25 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 26#5) = (coinWord t 26 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 23#5) = (coinWord t 27 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 27#5) = (coinWord t 28 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 28#5) = (coinWord t 29 (by decide)).setWidth 64 →
      se.readReg64 (.gpr 24#5) = (coinWord t 30 (by decide)).setWidth 64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) se
        (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 160 ∗
          A.pool ∗ stackAt fsp cliCoinsFillStack ∗
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
          stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
          memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp (initOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sd
      (S3InvPrefix A img x s0 ∗ coinsCursorAt img x.coinsP x.coins 120 ∗
        A.pool ∗ stackAt fsp cliCoinsFillStack ∗
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
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗
        ((fsp + 0x1600#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp (initOom s0) := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  refine sepWPp_conseq_oom (by (try dsimp only [fsp, t]); sep_frame)
    (kem_coins_c1_ext (z21 := z21) (z22 := z22) (z23 := z23)
      hOk hCoins hcoinsLt hpanic hctrl htr hx20 hx21
      fun s25 hctrl25 htr25 hx20_25 hx21_25 => ?_)
  refine sepWPp_conseq_oom (by (try dsimp only [fsp, t]); sep_frame)
    (kem_coins_c2_ext hOk hCoins hcoinsLt hpanic hctrl25 htr25 hx20_25 hx21_25
      fun s29 hctrl29 htr29 hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29 => ?_)
  refine sepWPp_conseq_oom (by (try dsimp only [fsp, t]); sep_frame)
    (kem_coins_c3_ext hOk hCoins hcoinsLt hpanic hctrl29 htr29
      hx20_29 hx21_29 hx25_29 hx22_29 hx26_29 hx23_29
      fun se hctrl_e htr_e hx20_e hx21_e hx25_e hx22_e hx26_e hx23_e hx27_e hx28_e hx24_e => ?_)
  exact sepWPp_conseq_oom (by (try dsimp only [fsp, t]); sep_frame)
    (hnext se hctrl_e htr_e hx20_e hx21_e hx25_e hx22_e hx26_e hx23_e hx27_e hx28_e hx24_e)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
