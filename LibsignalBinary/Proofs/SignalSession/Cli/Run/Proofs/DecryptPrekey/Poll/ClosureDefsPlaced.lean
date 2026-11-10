/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.TopLevel.SessionRecvPrekeyCommon

/-!
# Relocatable `[LibsignalPlacement]` Poll Closure Entry/Exit Layout and Outcome Helpers

Relocatable `[LibsignalPlacement]` entry/exit layout and outcome helpers for `dpSlotArgsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

abbrev coroUnusedP1AtPlaced := coroUnusedP1At

abbrev LsTokenInit [LibsignalPlacement] : SepProp :=
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt

theorem dpWords13_coins_eq_coroInit_placed [LibsignalPlacement]
    (x : DecPkGhost) (fut coins : BitVec 64) :
    dpWordsAt fut (dpSlotArgsPlaced x) ∗ ((fut + 0x68#64) ↦₆₄ coins) =
      decryptPrekeyCoroInitAt fut x.msgA x.peerA x.meA
        (x.stores + 0xf0#64) (lsρ cliSessionVtSym)
        x.stores (lsρ cliIdentityVtSym)
        (x.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (x.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (x.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) coins := by
  dsimp only [dpSlotArgsPlaced, dpWordsAt, decryptPrekeyCoroInitAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]

theorem dpFutStartAt_split_for_p1_placed [LibsignalPlacement]
    (x : DecPkGhost) (fut : BitVec 64) :
    dpFutStartAt fut (dpSlotArgsPlaced x) =
      (∃∗ b_4f2 : BitVec 8, ∃∗ u_3a0 : BitVec 64,
       ∃∗ u_398 : BitVec 64, ∃∗ b_390 : BitVec 8, ∃∗ coins : BitVec 64,
        decryptPrekeyCoroInitAt fut x.msgA x.peerA x.meA
          (x.stores + 0xf0#64) (lsρ cliSessionVtSym)
          x.stores (lsρ cliIdentityVtSym)
          (x.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
          (x.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (x.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) coins ∗
        cells (fut + 0x70#64) 14 ∗
        cells (fut + 0xe0#64) 4 ∗
        memRegion (fut + 0x100#64) 336 ∗
        cells (fut + 0x250#64) 6 ∗
        ((fut + 0x2c0#64) ↦₈ 0#8) ∗
        cells (fut + 0x2c8#64) 25 ∗
        ((fut + 0x390#64) ↦₈ b_390) ∗
        ((fut + 0x398#64) ↦₆₄ u_398) ∗
        ((fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
        cells (fut + 0x428#64) 8 ∗
        cells (fut + 0x490#64) 4 ∗
        ((fut + 0x4f2#64) ↦₈ b_4f2) ∗
        coroUnusedP1AtPlaced fut) := by
  unfold dpFutStartAt coroUnusedP1AtPlaced coroUnusedP1At
  change dpWordsAt fut (dpSlotArgsPlaced x) ∗
    (∃∗ coins : BitVec 64, (fut + 0x68#64) ↦₆₄ coins) ∗
    memRegion (fut + 0x70#64) 592 ∗
    ((fut + 0x2c0#64) ↦₈ 0#8) ∗
    memRegion (fut + 0x2c1#64) 1303 = _
  have h592 : memRegion (fut + 0x70#64) 592 =
      cells (fut + 0x70#64) 14 ∗ cells (fut + 0xe0#64) 4 ∗
      memRegion (fut + 0x100#64) 336 ∗ cells (fut + 0x250#64) 6 ∗
      memRegion (fut + 0x280#64) 64 := by
    rw [memRegion_split (fut + 0x70#64) 112 480 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64) 32 448 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64 + 32#64) 336 112 (by decide),
        memRegion_split (fut + 0x70#64 + 112#64 + 32#64 + 336#64) 48 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [ProofLib.memRegion_cells (fut + 0x70#64) 14 (by decide),
        ProofLib.memRegion_cells (fut + 0xe0#64) 4 (by decide),
        ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide)]
  have h1303 : memRegion (fut + 0x2c1#64) 1303 =
      memRegion (fut + 0x2c1#64) 7 ∗
      memRegion ((fut - 1112#64) + 1824#64) 560 ∗
      memRegion (fut + 0x4f8#64) 736 := by
    rw [memRegion_split (fut + 0x2c1#64) 7 1296 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64) 560 736 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h2c8 : fut + 0x2c8#64 = (fut - 1112#64) + 1824#64 := by bv_omega
    rw [h2c8]
  have h560 := coro_1824_560_split_for_p1 (fut - 1112#64)
  dsimp only at h560
  have hbase : (fut - 1112#64) + 1112#64 = fut := by bv_omega
  rw [hbase] at h560
  rw [h592, h1303, h560]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  refine congrArg sepExists (funext fun b_4f2 => ?_)
  refine congrArg sepExists (funext fun u_3a0 => ?_)
  refine congrArg sepExists (funext fun u_398 => ?_)
  refine congrArg sepExists (funext fun b_390 => ?_)
  refine congrArg sepExists (funext fun coins => ?_)
  rw [dpWords13_coins_eq_coroInit_placed x fut coins]
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
