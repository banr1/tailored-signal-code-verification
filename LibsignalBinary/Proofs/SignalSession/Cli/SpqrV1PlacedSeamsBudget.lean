/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements

/-!
# Budget-Threaded SPQR-V1 Placed Entry-Point Seam Bundle

Packages the three relocatable `[LibsignalPlacement]` SPQR-V1 entry-block budget contracts
(Blocks 327, 329, 427) in envelope-parametric (`SpqrV1PlacedSeamsOfEnv`) and default
bounded-envelope (`SpqrV1PlacedSeams`) forms, together with cross-block caller transfer lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget

export CryptoVerification.SignalSession.Cli
  (blockLib_327_externs blockLib_329_externs
   instIsLsBlockProg_blockProgram_327 instIsLsBlockProg_blockProgram_329)

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsProg_75 lsmpl)
open CryptoVerification.CliHandshake.InitiatePlaced (instIsLsBlockProg_521 lsProg_521)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427 instIsLsBlockProg_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_rocl)
open CryptoVerification.LibsignalSpqrV1
  (MlKem Params SpqrRecvModel recvResultAtX_entails_recvResultAt recvResultExactKeyAt
   spqrV1 spqrV1Recv spqrV1Recv_eq spqrV1_eq)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall SpqrModel VecArg spqrRecvResultAt spqrRecvStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (spqrRecvRawSpec)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (subroutine_ok_cliPlaced_of_trTrap trTrapExternsPlaced)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (InitialStateMemInvPlacedOk InitialStateMemInvPlacedOkOfEnv
   spqrInitialStatePlacedInnerSpec spqrInitialStatePlacedInnerSpecOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (lsLogOff_eq_logOff_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget (SpqrSendCoinsEnv)
open LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget
  (spqrSendCoinsPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (spqrInitialStateInnerSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget (SpqrRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (spqrRecvRawSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
  (spqrRecvResultAt_atState vecArg_at_atState)

/-!
## 1. Byte-Indexed Default Envelopes Matching `InitialStateEnv`, `SpqrRecvEnv`, `SpqrSendCoinsEnv`
-/

/-- `Params`-indexed form of `InitialStateEnv F` (`(fun x => InitialStateParamsEnv F x.p) = InitialStateEnv F`
    definitionally), matching `StepSpqrPlacedBudget.spqrInitialStateInnerSpec`. -/
def InitialStateParamsEnv (_F : ShaCompress) (p : Params) (evs : List AllocEvent) : Prop :=
  match p.version with
  | .v0 => evs = []
  | .v1 => SpqrBoundedEvs 128 (4 * p.authKey.length + 4096) evs

theorem initialStateParamsEnv_nonempty (F : ShaCompress) (p : Params) :
    ∃ evs, InitialStateParamsEnv F p evs := by
  cases h : p.version <;> simp only [InitialStateParamsEnv, h]
  · exact ⟨[], rfl⟩
  · exact ⟨[], SpqrBoundedEvs.nil _ _⟩

/-- Byte-slice-indexed form of `SpqrRecvEnv`
    (`(fun st msg : VecArg => SpqrRecvBytesEnv st.bytes msg.bytes) = SpqrRecvEnv` definitionally),
    matching `DecryptPlacedBudget.spqrRecvPlacedSpecXT`. -/
def SpqrRecvBytesEnv (st msg : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * st.length + 4 * msg.length + 16384) evs

theorem spqrRecvBytesEnv_nonempty (st msg : List (BitVec 8)) :
    ∃ evs, SpqrRecvBytesEnv st msg evs :=
  ⟨[], SpqrBoundedEvs.nil 512 (4 * st.length + 4 * msg.length + 16384)⟩

/-- Byte-slice-indexed form of `SpqrSendCoinsEnv`
    (`(fun sc : SendCall => SpqrSendCoinsBytesEnv sc.st.bytes sc.rest) = SpqrSendCoinsEnv`
    definitionally), matching `RootPlacedBudget.otrEncryptV1_coins_placed_ok`. -/
def SpqrSendCoinsBytesEnv (st _rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 512 (4 * st.length + 16384) evs

theorem spqrSendCoinsBytesEnv_nonempty (st rest : List (BitVec 8)) :
    ∃ evs, SpqrSendCoinsBytesEnv st rest evs :=
  ⟨[], SpqrBoundedEvs.nil 512 (4 * st.length + 16384)⟩

/-! ## 2. Budget-Threaded Inner Entry Specifications (`Blocks 329, 427`) -/

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of `spqrRecvSpecExactKey`
    (Block `329`, `spqr::recv`), dropping `allocFailedIn` from `onPanic` while retaining genuine
    protocol panics `R.recvPanics`. -/
def spqrRecvPlacedInnerSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) where
  pre := fun ((st, msg, ret), stB) s =>
    ⌜FitsEnv M lim stB (RecvEnv st msg)⌝ ∗
      ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      lsLogOff ∗ A.pool lim stB s ∗ stackAt s.sp spqrRecvStack
  post := fun ((st, msg, ret), stB) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecvEnv st msg evs⌝ ∗
      ⌜sf.trace = s0.trace ∧ ¬ R.recvPanics st.bytes msg.bytes⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (R.recv st.bytes msg.bytes) ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs stB) sf ∗
      stackAt s0.sp spqrRecvStack
  onPanic := fun ((st, msg, _), _) s0 sf =>
    ⌜R.recvPanics st.bytes msg.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Default budget-threaded `[LibsignalPlacement]` `spqrRecvPlacedInnerSpecX` at `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerSpecXOfEnv M A lim R SpqrRecvEnv

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of
    `spqrRecvSpecExactKeyBounded` (Block `329`, `spqr::recv`) with `tokenInitPlacedAt` framed and
    `st.bytes.length < 2 ^ 32`, `msg.bytes.length < 2 ^ 40`, and `spqrRecvStack ≤ s.sp.toNat`. -/
def spqrRecvPlacedInnerSpecXTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrRecvPlacedInnerSpecXOfEnv M A lim R RecvEnv).post (x, stB) s0 sf }

/-- Default budget-threaded `[LibsignalPlacement]` `spqrRecvPlacedInnerSpecXT` at `SpqrRecvEnv`. -/
abbrev spqrRecvPlacedInnerSpecXT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (R : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  spqrRecvPlacedInnerSpecXTOfEnv M A lim R SpqrRecvEnv

/-- Envelope-parametric image-free `[LibsignalPlacement]` inner `Spec` of `spqrSendSpecT` for
    `<Coins>` (Block `427`) with `tokenInitPlacedAt` framed and
    `st.bytes.length < 2 ^ 32`, `64 ≤ rest.length`, definitionally matching the `hSend` hypothesis
    of `RootPlacedBudget.otrEncryptV1_coins_placed_ok` at `F := tokenInitPlacedAt`. -/
def spqrSendCoinsPlacedSpecTOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SendCall → List AllocEvent → Prop) :
    Spec (SendCall × M.σ) :=
  { spqrSendCoinsPlacedSpec M A lim ctl S SendEnv with
    pre := fun (x, stB) s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpec M A lim ctl S SendEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗
        (spqrSendCoinsPlacedSpec M A lim ctl S SendEnv).post (x, stB) s0 sf }

/-- Default budget-threaded `[LibsignalPlacement]` `spqrSendCoinsPlacedSpecT` at `SpqrSendCoinsEnv`. -/
abbrev spqrSendCoinsPlacedSpecT [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel) :
    Spec (SendCall × M.σ) :=
  spqrSendCoinsPlacedSpecTOfEnv M A lim ctl S SpqrSendCoinsEnv

/-! ## 3. Three-Seam Hypothesis Bundle (`SpqrV1PlacedSeamsOfEnv` / `SpqrV1PlacedSeams`) -/

/-- Envelope-parametric three-seam hypothesis bundle for the SPQR-V1 entry blocks
    (`327`, `329`, `427`) on the placed CLI hook map
    `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
structure SpqrV1PlacedSeamsOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (InitEnv : InitialStateGhost → List AllocEvent → Prop)
    (RecvEnv : VecArg → VecArg → List AllocEvent → Prop)
    (SendEnv : SendCall → List AllocEvent → Prop) : Prop where
  /-- Block `327`: `spqr::initial_state` at `lsmpl.base 327`. -/
  spqrInitialState :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStatePlacedInnerSpecOfEnv M A lim W.C.F InitEnv))
  /-- Block `329`: `spqr::recv` at `lsmpl.base 329` on
  `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
  spqrRecv :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv))
  /-- Block `427`: `spqr::send::<signal_session_ratchet::Coins>` at `lsmpl.base 427`. -/
  spqrSendCoins :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv))

/-- Default budget-threaded three-seam hypothesis bundle for SPQR-V1 (`Blocks 327, 329, 427`). -/
abbrev SpqrV1PlacedSeams [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) SpqrRecvEnv SpqrSendCoinsEnv

/-! ## 4. Cross-Block Transfer & Downstream Consumer Bridges -/

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrInitialState` to any caller block `i < 619`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrInitialState_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStatePlacedInnerSpecOfEnv M A lim W.C.F InitEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrInitialState hi (by decide) (by decide))

/-- Instantiate `BobTailV1PlacedBudget.InitialStateMemInvPlacedOkOfEnv` on Block `75` (`lsProg_75`). -/
theorem SpqrV1PlacedSeamsOfEnv.initialStateMemInv_lsProg75 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    InitialStateMemInvPlacedOkOfEnv M
      (CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A lim W.C.F InitEnv (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  hS.spqrInitialState_at_block
    (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75) (by decide)

/-- Instantiate `StepSpqrPlacedBudget.spqrInitialStateInnerSpec` on Block `521` (`lsProg_521`)
    for any `Params`-indexed envelope `InitStateEnv`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrInitialState_initProg_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (fun x => InitStateEnv x.p) RecvEnv SendEnv) :
    subroutine_ok (lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)) :=
  hS.spqrInitialState_at_block
    (callerProg := lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- Default `InitialStateParamsEnv W.C.F` instantiation of `spqrInitialStateInnerSpec` on
    Block `521` (`lsProg_521`). -/
theorem SpqrV1PlacedSeams.spqrInitialState_initProg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams M A lim mmpl gh W) :
    subroutine_ok (lsProg_521 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 327)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec A lim (InitialStateParamsEnv W.C.F) W.C.F)) :=
  SpqrV1PlacedSeamsOfEnv.spqrInitialState_initProg_ofEnv hS

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrRecv` to any caller block `i < 619` on
    `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_trTrap_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrRecv hi (by decide) (by decide))

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrRecv` to any caller block `i < 619` on
    `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv)
    {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K) RecvEnv)) := by
  have : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl i
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      i (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    ⟨rfl, hcaller.externs_eq⟩
  have htr := hS.spqrRecv_trTrap_at_block
    (callerProg := libsignalSessionLib.blockProgram lsmpl i
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) hi
  rw [hcaller.eq_blockProgram]
  exact subroutine_ok_cliPlaced_of_trTrap
    (pc := (libsignalSessionLib.blockLib i).program (libsignalSessionLib.blockPlacement lsmpl i))
    (b := (libsignalSessionLib.blockPlacement lsmpl i).base) htr

/-- Budget-threaded relocatable `spqrRecvRawSpecPlaced` (`PqRecvBudgetDefs`) with
    `tokenInitPlacedAt` framed and DEV-SPQR3 / DEV-SPQR4 preconditions
    (`st.bytes.length < 2 ^ 32`, `msg.bytes.length < 2 ^ 40`, `spqrRecvStack ≤ s.sp.toNat`),
    mirroring `SpqrRecvTrapV1Placed.spqrRecvRawSpecT`. -/
def spqrRecvRawSpecPlacedT [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) :=
  { spqrRecvRawSpecPlaced A lim S RecvEnv with
    pre := fun (x, stB) s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvRawSpecPlaced A lim S RecvEnv).pre (x, stB) s
    post := fun (x, stB) s0 sf =>
      tokenInitPlacedAt ∗ (spqrRecvRawSpecPlaced A lim S RecvEnv).post (x, stB) s0 sf }

/-- Bridge `StoreKit.withLsCodeRoLoaded lsmpl (spqrRecvPlacedInnerSpecXTOfEnv ...)` to
    `LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrRecvRawSpecPlacedT ...)`,
    mirroring `SpqrRecvTrapV1Placed.spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecT`. -/
theorem spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv F K)
          (fun st msg => RecvBytesEnv st.bytes msg.bytes)))) :
    subroutine_ok prog entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawSpecPlacedT A lim (spqrV1 F K) RecvBytesEnv)) := by
  have heq_pan :
      (spqrV1Recv F K).recvPanics = fun st msg => (spqrV1 F K).recvPanics st msg = true := by
    rw [spqrV1Recv_eq, spqrV1_eq]; rfl
  refine subroutine_ok_mono h
    (fun ((st, msg, ret), stB) Fr s0 hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced, spqrRecvRawSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState] at hpre ⊢
      rwa [lsLogOff_eq_logOff_placed])
    (fun ((st, msg, ret), stB) Fr s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced, spqrRecvRawSpec,
        RustCliAllocBudget.atState_pool, vecArg_at_atState,
        spqrRecvResultAt_atState] at hpost ⊢
      rw [heq_pan, lsLogOff_eq_logOff_placed] at hpost
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (Entails.sepExists_mono fun evs => sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (recvResultAtX_entails_recvResultAt A.repAlloc ret F K
              st.bytes msg.bytes)))))))) hpost)
    (fun ((st, msg, ret), stB) Fr s0 sf hpan => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        spqrRecvPlacedInnerSpecXTOfEnv, spqrRecvPlacedInnerSpecXOfEnv,
        spqrRecvRawSpecPlacedT, spqrRecvRawSpecPlaced] at hpan ⊢
      rwa [heq_pan] at hpan)
    (fun _ _ _ _ _ he => he)

/-- Bridge `SpqrV1PlacedSeamsOfEnv.spqrRecv` at any `cliGhostExterns gh (cliExternsPlaced mmpl W)`
    caller block `i < 619` directly to `spqrRecvRawSpecPlacedT`. -/
theorem SpqrV1PlacedSeamsOfEnv.spqrRecv_rawSpecPlacedT_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrRecvRawSpecPlacedT A lim (spqrV1 W.C.F W.Q.K) RecvBytesEnv)) :=
  spqrRecvPlacedInnerSpecXT_imp_spqrRecvRawSpecPlacedT (hS.spqrRecv_at_block hi)

/-- Transfer `SpqrV1PlacedSeamsOfEnv.spqrSendCoins` to Block `428` (`otrEncryptV1_coins_placed_ok`). -/
theorem SpqrV1PlacedSeamsOfEnv.spqrSendCoins_at_428 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hS : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitEnv RecvEnv SendEnv) :
    subroutine_ok
      ((blkPC_428).rebase (blkPl_428).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecTOfEnv M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have : IsLsBlockProg
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W))) 427
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    instIsLsBlockProg_427 (cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := (blkPC_428).rebase (blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hS.spqrSendCoins (by decide) (by decide) (by decide))

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
