/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridge
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Relocatable Coins Tape and `signal_session_coins_fill` Bridges

Relocatable `[LibsignalPlacement]` bridges between `coinsInstalledPlaced` and `coinsAtPlaced`,
together with `subroutine_ok` contracts and cross-block (`i < 619`) caller transfers for Block `618`
(`signal_session_coins_fill`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue

theorem coinsInstalledPlaced_eq_coinsAfterPlaced_zero [LibsignalPlacement]
    (p : BitVec 64) (coins : List (BitVec 8)) :
    coinsInstalledPlaced p coins = coinsAfterPlaced p coins 0 := by
  unfold coinsInstalledPlaced coinsAfterPlaced
  rw [tapeAfter2_zero_eq]

/-- With `coins.length < 2 ^ 63`, `coinsAtPlaced` equals `coinsInstalledPlaced`. -/
theorem coinsAtPlaced_eq_coinsInstalledPlaced [LibsignalPlacement]
    (p : BitVec 64) (coins : List (BitVec 8)) (hlen : coins.length < 2 ^ 63) :
    coinsAtPlaced p coins = coinsInstalledPlaced p coins := by
  unfold coinsAtPlaced tapeAt2 coinsInstalledPlaced
  rw [pure_sepConj_of_true hlen]

theorem coinsInstalledPlaced_entails_coinsAtPlaced [LibsignalPlacement]
    (p : BitVec 64) (coins : List (BitVec 8)) (hlen : coins.length < 2 ^ 63) :
    coinsInstalledPlaced p coins ⊢ coinsAtPlaced p coins :=
  Entails.of_eq (coinsAtPlaced_eq_coinsInstalledPlaced p coins hlen).symm

theorem coinsAfterPlaced_entails_anyHeap [LibsignalPlacement]
    (cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) :
    coinsAfterPlaced cur rest k ⊢ anyHeap :=
  entails_anyHeap _

private theorem cli_memcpy_region_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) memcpyName
      sessionMemcpyRegionSpec :=
  cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG

private theorem cli_memset_region_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) {A : RustAlloc} (hG : CliGhostA0Hooks A gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) memsetName
      sessionMemsetRegionSpec :=
  cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG

/-- Block `618` (`signal_session_coins_fill`) satisfies `coinsFillSpecPlaced stk` on
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliCoinsFillPlaced_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base (coinsFillSpecPlaced stk) :=
  coinsFillPlaced_ok (cli_memcpy_region_sat mmpl gh W hG) (cli_memset_region_sat mmpl gh W hG) stk hstk hstk'

theorem cliCoinsFillPlaced_ok_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base (withLsCodeLoaded lsmpl (coinsFillSpecPlaced stk)) :=
  coinsFillPlaced_ok_cl (cli_memcpy_region_sat mmpl gh W hG) (cli_memset_region_sat mmpl gh W hG) stk hstk hstk'

theorem cliCoinsFillPlaced_ok_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillSpecPlaced stk)) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (cliCoinsFillPlaced_ok mmpl gh W hG stk hstk hstk')

theorem cliCoinsFillAtPlaced_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (cur : BitVec 64) (rest : List (BitVec 8))
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base (coinsFillAtSpecPlaced stk cur rest) :=
  coinsFillAtPlaced_of_after0 (cliCoinsFillPlaced_ok mmpl gh W hG stk hstk hstk')

theorem cliCoinsFillAtPlaced_ok_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (cur : BitVec 64) (rest : List (BitVec 8))
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base (withLsCodeLoaded lsmpl (coinsFillAtSpecPlaced stk cur rest)) :=
  coinsFillAtPlaced_of_after0_cl (cliCoinsFillPlaced_ok_cl mmpl gh W hG stk hstk hstk')

theorem cliCoinsFillAtPlaced_ok_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    (cur : BitVec 64) (rest : List (BitVec 8))
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok
      ((blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_618).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (coinsFillAtSpecPlaced stk cur rest)) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (cliCoinsFillAtPlaced_ok mmpl gh W hG cur rest stk hstk hstk')

/-- Transfers `cliCoinsFillPlaced_ok_rocl` to any caller block `i < 619`. -/
theorem cliCoinsFillPlaced_rocl_at_block [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} (hG : CliGhostA0Hooks A gh)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_618).base
      (withLsRoCl lsmpl (coinsFillSpecPlaced stk)) :=
  ls_subroutine_ok_rocl_of_block
    (calleeProg := lsProg_618 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := i) (j := 618) (H := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (cliCoinsFillPlaced_ok_rocl mmpl gh W hG stk hstk hstk') hi (by decide)

end CryptoVerification.SignalSession.Cli.Slots
