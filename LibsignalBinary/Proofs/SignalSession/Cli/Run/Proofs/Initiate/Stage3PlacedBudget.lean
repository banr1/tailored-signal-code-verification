/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Stage 3 (`[LibsignalPlacement]`): PQXDH `DH1..DH4`, KEM Encapsulate, and `HandshakeKeys::derive`

Top-level Stage 3 (`+0x0760 → +0x10a4` and early `Err` / OOM exits) theorems on `initProgPlaced W`
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3PlacedBudget

noncomputable section

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E
  (PreKeyBundleFields UnreachedPqxdhPrimitives initiateInput modelPrims toU8)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage3Placed AtStage4Placed cliCoinsFillStack initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (coinsFillSpecPlacedW3)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage3MemPlaced stage4MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced SubsetA4InitCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysAPlacedBudget
  (deriveKeysAAllocPrefixEvents deriveKeysAEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
  (deriveKeysEvents fitsEvents_stage3_of_okEvents stage3AfterDh1Events stage3AfterDh2Events
   stage3AfterDh3Events stage3AfterDh4Events stage3AfterKemBoxEvents stage3Dh1UnwindEvents
   stage3Dh2UnwindEvents stage3Dh3UnwindEvents stage3Dh4Opt stage3Dh4UnwindEvents stage3OkEvents
   stage3_all_a4_hooks_placed_ok stage3_all_no_coins_placed_ok
   stage3_all_okEvents_a4_hooks_placed_ok stage3_all_okEvents_evs_placed_ok
   stage3_all_okEvents_placed_ok stage3_all_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (s3CalcAgreeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhStepsCPlacedBudget
  (s3Dh4CalcAgreeEvents)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-- Budget-threaded Stage 3 (`+0x0760 → +0x10a4` and early `Err` / OOM exits) under `[LibsignalPlacement]`. -/
theorem initiate_stage3_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  stage3_all_placed_ok hh @hCoins hLocal
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4 hFitKemBox
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

/-- Single-`FitsEvents` Stage 3 theorem over `stage3OkEvents`. -/
theorem initiate_stage3_okEvents_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  stage3_all_okEvents_placed_ok hh @hCoins hLocal hFit
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

theorem initiate_stage3_no_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  stage3_all_no_coins_placed_ok hh hLocal
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4 hFitKemBox
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

theorem initiate_stage3_okEvents_no_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom := by
  obtain ⟨hFit192, hFitDh1, hFitDh2, hFitDh3, hFitDh4, hFitKemBox⟩ :=
    fitsEvents_stage3_of_okEvents hs3 hFit
  exact stage3_all_no_coins_placed_ok hh hLocal
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4 hFitKemBox
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

/-- Stage 3 theorem discharging coin-fill and DH/KEM hooks from `RunHooksPlaced` and Block `59` from `SubsetA4InitCalleesPlaced`. -/
theorem initiate_stage3_a4_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hFit192 : FitsEvents M lim st (rustAllocEvents 192 1))
    (hFitDh1 : FitsEvents M lim (M.stepEvents (rustAllocEvents 192 1) st)
      (s3CalcAgreeEvents X W (toU8 kp.privateKey.bytes.toList)
        (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh2 : FitsEvents M lim (M.stepEvents stage3AfterDh1Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.idKey.publicKey.bytes.toList)))
    (hFitDh3 : FitsEvents M lim (M.stepEvents stage3AfterDh2Events st)
      (s3CalcAgreeEvents X W (toU8 ekASk) (toU8 x.bundle.spk.bytes.toList)))
    (hFitDh4 : FitsEvents M lim (M.stepEvents stage3AfterDh3Events st)
      (s3Dh4CalcAgreeEvents X W ekASk x.bundle.opk))
    (hFitKemBox : FitsEvents M lim
      (M.stepEvents (stage3AfterDh4Events (stage3Dh4Opt X W kp be x.coins)) st)
      deriveKeysAAllocPrefixEvents)
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  stage3_all_a4_hooks_placed_ok hh ha4
    hFit192 hFitDh1 hFitDh2 hFitDh3 hFitDh4 hFitKemBox
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

theorem initiate_stage3_okEvents_a4_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hFit : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0)
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp oom :=
  stage3_all_okEvents_a4_hooks_placed_ok hh ha4 hFit
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

theorem initiate_stage3_okEvents_evs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl (coinsFillSpecPlacedW3 cStk)))
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFit : FitsEvents M lim (M.stepEvents evs_pre st0)
      (stage3OkEvents (stage3Dh4Opt X W kp be x.coins)))
    (hEnv_dh1 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh1UnwindEvents))
    (hEnv_dh2 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh2UnwindEvents))
    (hEnv_dh3 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
      InitEnv x (evs_pre ++ stage3Dh3UnwindEvents))
    (hEnv_dh4 :
      (let P := modelPrims X ⟨W.C, W.Q⟩
       let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
       SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
         false) →
      InitEnv x (evs_pre ++ stage3Dh4UnwindEvents))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (_hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim
          (M.stepEvents (evs_pre ++ stage3OkEvents (stage3Dh4Opt X W kp be x.coins)) st0)
          x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim (M.stepEvents evs_pre st0) x kp ekASk ekAPk pqspkPtr opkId stk s0 s3)
      Q Qp oom :=
  stage3_all_okEvents_evs_placed_ok hh @hCoins hLocal hFit
    hEnv_dh1 hEnv_dh2 hEnv_dh3 hEnv_dh4 hS hcoinsLt hstk hstk64 hs3 hpost hpanic hnext

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3PlacedBudget
