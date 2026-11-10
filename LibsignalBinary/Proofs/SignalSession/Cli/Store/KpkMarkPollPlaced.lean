/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<KyberPreKeyFiles as KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}`

Proves `kpkMarkPollSpecPlaced` on Block `578` (`lsProg_578 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SpqrV1.Varint

section Placed

/-- Block `578` (`mark_kyber_pre_key_used::{closure#0}`) meets `kpkMarkPollSpecPlaced rd pathOk A stk`
given `AllocContractsXCliPlaced`, `CliPanicHooksPlaced`, `bcmp`, `decimal` (block `597`),
`Dir::get` (block `589`), `Dir::put::<String>` (block `542`), and `TraceFsSound (lsProg_578 H)`. -/
theorem kpkMarkPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {decProg getProg putProg : Program} {decBlk getBlk putBlk : Nat}
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hFs : TraceFsSound (lsProg_578 H))
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_578 H) (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A stk) := by
  have hDecimal' := ls_transfer_lscro (callerProg := lsProg_578 H) hDecimal (by decide) hDecBlk hDecUnmut
  have hGet' := ls_transfer_lscro (callerProg := lsProg_578 H) hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_578 H) hPut (by decide) hPutBlk hPutUnmut
  exact Helpers.kpkMarkPoll_placed_ok hC hP hBcmp hDecimal' hGet' hPut' hFs hstk

theorem kpkMarkPoll_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg decProg getProg putProg : Program}
    {callerBlk decBlk getBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hDecimal : subroutine_ok decProg (lsmpl.base 597) (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok getProg (lsmpl.base 589) (dirGetSpecPlaced rd pathOk A getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hFs : TraceFsSound (lsProg_578 H))
    (hstk : 0xf0 + max (max decStk getStk) (max putStk doReserveStackX) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 578)
      (kpkMarkPollSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 578)
    (kpkMarkPoll_placed_ok_of_deps hC hP hBcmp hDecimal hGet hPut hFs hstk
      hDecBlk hDecUnmut hGetBlk hGetUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll
