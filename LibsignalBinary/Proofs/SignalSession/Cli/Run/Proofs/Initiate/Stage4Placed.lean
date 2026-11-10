/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.TopPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 4 (`[LibsignalPlacement]`): Sending Ratchet Chain, SPQR Init, and `SessionState` Construction

Relocatable `[LibsignalPlacement]` proof of Stage 4 (`+0x10a4 → +0x1484` and `create_chain` error
exit).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Coins
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Stage 4 (`+0x10a4 → +0x1484` and `create_chain` error exit) under `[LibsignalPlacement]`. -/
theorem initiate_stage4_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8))),
      AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
        (stage5MemPlaced A x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
      (stage4MemPlaced A x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
      Q Qp (initOom s0) :=
  Stage4Lemmas.initiate_stage4_placed_ok_impl
    hh hCoins hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpost hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
