/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Stage 4 (`[LibsignalPlacement]`): Sending Ratchet Chain, SPQR Init, and `SessionState` Construction

Top-level Stage 4 (`+0x10a4 → +0x1484` and `create_chain` error exit) theorems under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  InitExitPostPlaced InitPanicPostPlaced InitLocalCalleesPlaced RunHooksPlaced
  coinsFillSpecPlacedW3 stage2MemPlaced stage3MemPlaced stage4MemPlaced stage5MemPlaced
  initiate_stage4_placed_ok
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas hiding
  errExitMemPlaced initiate_stage4_placed_ok_impl
  panic_oom_entails_initOnPanic_placed panic_oom_only_entails_initOnPanic_placed
  stage4_branch_4496_err_placed stage4_branch_4496_ok_placed
  stage4_err_exit_placed stage4_step_prechain_to_4496_placed
  stage4_step_session_placed stage4_step_spqr_placed
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage4MemPlaced stage5MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget
  (stage4PreChainEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
  (stage4StepSessionEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlacedBudget
  (stage4ErrTotalEvents stage4OkTotalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlacedBudget
  (stage4ErrTotalEvents stage4OkTotalEvents)

/-- Budget-threaded Stage 4 (`+0x10a4 → +0x1484` and `create_chain` error exit). -/
theorem initiate_stage4_placed_ok_impl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsPreChain : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    (hFitsSpqr : ∀ (rk1 : RootKey) (ck1 : ChainKey),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      FitsEnv M lim
        (M.stepEvents
          (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st)
        (InitStateEnv
          (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
            (bytesToKey32 (ofU8 dk.pqrKey)))))
    (hFitsSess : ∀ (rk1 : RootKey) (ck1 : ChainKey) (evsSpqr : List AllocEvent),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      FitsEvents M lim
        (M.stepEvents evsSpqr
          (M.stepEvents
            (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st))
        stage4StepSessionEvents)
    (hEnvErr :
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (stage4ErrTotalEvents W x) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
        (evsSpqr : List AllocEvent),
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
        (stage5MemPlaced A lim (M.stepEvents (stage4OkTotalEvents W x evsSpqr) st)
          x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
      (stage4MemPlaced A lim st x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
      Q Qp oom :=
  Stage4Lemmas.TopPlacedBudget.initiate_stage4_placed_ok_impl
    hh hCoins hLocal hFitsPreChain hFitsSpqr hFitsSess hEnvErr
    hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpost hnext

theorem initiate_stage4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : CryptoVerification.LibsignalSpqrV1.Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsPreChain : FitsEvents M lim st
      (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))))
    (hFitsSpqr : ∀ (rk1 : RootKey) (ck1 : ChainKey),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      FitsEnv M lim
        (M.stepEvents
          (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st)
        (InitStateEnv
          (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
            (bytesToKey32 (ofU8 dk.pqrKey)))))
    (hFitsSess : ∀ (rk1 : RootKey) (ck1 : ChainKey) (evsSpqr : List AllocEvent),
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      FitsEvents M lim
        (M.stepEvents evsSpqr
          (M.stepEvents
            (stage4PreChainEvents W.C x.bundle.spk (Ratchet.clampScalar (stage4EphVec x.coins))) st))
        stage4StepSessionEvents)
    (hEnvErr :
      rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
          ⟨Ratchet.clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (stage4ErrTotalEvents W x) st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (_hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
        (evsSpqr : List AllocEvent),
      InitStateEnv
        (CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams false .a2b
          (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
      AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
        (stage5MemPlaced A lim (M.stepEvents (stage4OkTotalEvents W x evsSpqr) st)
          x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
      (stage4MemPlaced A lim st x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
      Q Qp oom :=
  Stage4Lemmas.TopPlacedBudget.initiate_stage4_placed_ok
    hh hCoins hLocal hFitsPreChain hFitsSpqr hFitsSess hEnvErr
    hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpost _hpanic hnext

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget

end
