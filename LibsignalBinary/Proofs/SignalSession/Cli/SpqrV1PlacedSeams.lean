/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1Placed
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridgePlaced
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements

/-!
# SPQR-V1 Placed Entry-Point Seam Bundle

Packages the three relocatable `[LibsignalPlacement]` SPQR-V1 entry-block contracts on
`cliGhostExterns gh (cliExternsPlaced mmpl W)`:
- Block 327 (`spqr::initial_state`): `spqrInitialStatePlacedInnerSpec`
- Block 329 (`spqr::recv`): `spqrRecvPlacedInnerSpecXT` on `Slots.trTrapExternsPlaced`
- Block 427 (`spqr::send::<Coins>`): `spqrSendCoinsPlacedSpecT`
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.Cli.CoinsTape

theorem blockLib_327_externs :
    (libsignalSessionLib.blockLib 327).text.externs = libsignalSessionExterns := by
  decide +kernel

theorem blockLib_329_externs :
    (libsignalSessionLib.blockLib 329).text.externs = libsignalSessionExterns := by
  decide +kernel

instance instIsLsBlockProg_blockProgram_327 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 327 H) 327 H where
  eq_blockProgram := rfl
  externs_eq := blockLib_327_externs

instance instIsLsBlockProg_blockProgram_329 [LibsignalPlacement] (H : LibsignalHooks) :
    IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 329 H) 329 H where
  eq_blockProgram := rfl
  externs_eq := blockLib_329_externs

/-- Image-free `[LibsignalPlacement]` inner `Spec` of `spqrRecvSpecExactKey` (Block `329`, `spqr::recv`)
using `FromRecordCallees.lsLogOff` in place of `logOff img`. -/
def spqrRecvPlacedInnerSpecX [LibsignalPlacement] (A : RustAlloc) (R : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace ∧ ¬ R.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
      recvResultExactKeyAt A ret (R.recv st.bytes msg.bytes) ∗
      FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun (st, msg, _) s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ R.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Image-free `[LibsignalPlacement]` inner `Spec` of `spqrRecvSpecExactKeyBounded` (Block `329`, `spqr::recv`)
with `SpqrV1.GF.Mul2U16.tokenInitPlacedAt` framed and `st.bytes.length < 2 ^ 32`,
`msg.bytes.length < 2 ^ 40`, and `spqrRecvStack ≤ s.sp.toNat`. -/
def spqrRecvPlacedInnerSpecXT [LibsignalPlacement] (A : RustAlloc) (R : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvPlacedInnerSpecX A R with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedInnerSpecX A R).pre x s
    post := fun x s0 sf =>
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedInnerSpecX A R).post x s0 sf }

/-- Image-free `[LibsignalPlacement]` inner `Spec` of `spqrSendSpecT` for `<Coins>` (Block `427`)
with `SpqrV1.GF.Mul2U16.tokenInitPlacedAt` framed and `st.bytes.length < 2 ^ 32`, `64 ≤ rest.length`. -/
def spqrSendCoinsPlacedSpecT [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) : Spec SendCall :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendCoinsPlacedSpec A ctl S with
    pre := fun x s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendCoinsPlacedSpec A ctl S).pre x s
    post := fun x s0 sf =>
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSendCoinsPlacedSpec A ctl S).post x s0 sf }

/-- Three-seam hypothesis bundle for the SPQR-V1 entry blocks (`327`, `329`, `427`) on the
placed CLI hook map `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
structure SpqrV1PlacedSeams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  /-- Block `327`: `spqr::initial_state` at `lsmpl.base 327`. -/
  spqrInitialState :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec E2E.HooksE.A0 W.C.F))
  /-- Block `329`: `spqr::recv` at `lsmpl.base 329` on
  `Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
  spqrRecv :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXT E2E.HooksE.A0 (spqrV1Recv W.C.F W.Q.K)))
  /-- Block `427`: `spqr::send::<signal_session_ratchet::Coins>` at `lsmpl.base 427`. -/
  spqrSendCoins :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)))

/-- Transfer `SpqrV1PlacedSeams.spqrInitialState` to any caller block `i < 619`. -/
theorem SpqrV1PlacedSeams.spqrInitialState_at_block [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec E2E.HooksE.A0 W.C.F)) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
    (LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrInitialState hi (by decide) (by decide))

/-- Instantiate `BobTailV1Placed.InitialStateMemInvPlacedOk` on Block `75` (`lsProg_75`). -/
theorem SpqrV1PlacedSeams.initialStateMemInv_lsProg75 [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) :
    CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) E2E.HooksE.A0 W.C.F
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  hS.spqrInitialState_at_block
    (callerProg := CryptoVerification.lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 75) (by decide)

/-- Instantiate `Initiate`'s `spqrInitialStateInnerSpec` on Block `521` (`lsProg_521`). -/
theorem SpqrV1PlacedSeams.spqrInitialState_initProg [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) :
    subroutine_ok
      (CryptoVerification.CliHandshake.InitiatePlaced.lsProg_521
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (RunProofs.Initiate.spqrInitialStateInnerSpec E2E.HooksE.A0 W.C.F)) :=
  hS.spqrInitialState_at_block
    (callerProg := CryptoVerification.CliHandshake.InitiatePlaced.lsProg_521
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- Transfer `SpqrV1PlacedSeams.spqrRecv` to any caller block `i < 619` on
`Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem SpqrV1PlacedSeams.spqrRecv_trTrap_at_block [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i
      (Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXT E2E.HooksE.A0 (spqrV1Recv W.C.F W.Q.K))) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
    (LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
      hS.spqrRecv hi (by decide) (by decide))

/-- Transfer `SpqrV1PlacedSeams.spqrRecv` to any caller block `i < 619` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem SpqrV1PlacedSeams.spqrRecv_at_block [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 329)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXT E2E.HooksE.A0 (spqrV1Recv W.C.F W.Q.K))) := by
  have : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl i
        (Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      i (Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    ⟨rfl, hcaller.externs_eq⟩
  have htr : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl i
        (Slots.trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXT E2E.HooksE.A0 (spqrV1Recv W.C.F W.Q.K))) :=
    hS.spqrRecv_trTrap_at_block hi
  rw [hcaller.eq_blockProgram]
  exact Slots.subroutine_ok_cliPlaced_of_trTrap
    (pc := (libsignalSessionLib.blockLib i).program (libsignalSessionLib.blockPlacement lsmpl i))
    (b := (libsignalSessionLib.blockPlacement lsmpl i).base) htr

/-- Transfer `SpqrV1PlacedSeams.spqrSendCoins` to Block `428` (`otrEncryptV1_coins_placed_ok`). -/
theorem SpqrV1PlacedSeams.spqrSendCoins_at_428 [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hS : SpqrV1PlacedSeams mmpl gh W) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.Placed.blkPC_428).rebase
        (CryptoVerification.CliRatchet.Placed.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) := by
  have _ := CryptoVerification.CliRatchet.SendPlaced.instIsLsBlockProg_427
    (cliGhostExterns gh (cliExternsPlaced mmpl W))
  exact LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
    (LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block
      (callerProg := (CryptoVerification.CliRatchet.Placed.blkPC_428).rebase
        (CryptoVerification.CliRatchet.Placed.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hS.spqrSendCoins (by decide) (by decide) (by decide))

end CryptoVerification.SignalSession.Cli
