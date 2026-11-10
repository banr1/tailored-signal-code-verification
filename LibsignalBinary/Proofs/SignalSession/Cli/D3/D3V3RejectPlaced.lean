/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3PollRejectAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3V3PathAKitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Version-3 Pre-Key Message (`"X3DH no longer supported"`) Slot Rejection

Defines `MsgCondV3` (`pm.messageVersion = 3` with no matching active session), proves
`decPkDef` evaluates to `some none`, and lifts poll-closure version-3 rejection on Block `518`
to `decPkSlotSpecPlaced` on Block `520` and any caller block.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.Slots
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## 1. `v3` Message Condition & Pure `decPkDef` Evaluation (`[LibsignalPlacement]`) -/

/-- Version-3 pre-key rejection condition: outer `messageVersion = 3` and no loaded active
peer session matches `pm`. -/
def MsgCondV3 (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer _me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  pm.messageVersion = 3#8 ∧
  ∀ r s, Slots.loadRec Scope F peer = .ok (some r) →
    r.currentSession = some s → ¬ SessMatchesPm s pm

/-- Any `pm` satisfying `MsgCondV3` evaluates `decPkDef` to `some none`. -/
theorem decPkDef_eq_some_none_of_v3
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (hv3 : MsgCondV3 Scope F peer me pm) :
    decPkDef X W Scope F peer me pm coins = some none :=
  decPkDef_eq_some_none_of_d3b3 X W Scope F peer me pm coins
    (pkToE?_eq_none_of_v3 hv3.1) hv3.2

/-- Any parsed `v3` message with distinct service IDs and no matching active session satisfies
`MsgCondPkToENone`. -/
theorem msgCondPkToENone_of_v3
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hparse : ∃ body : List (BitVec 8), Pksm.pksmParse body = some pm)
    (hAcct : ¬ RunProofs.SameServiceId peer me)
    (hv3 : MsgCondV3 Scope F peer me pm) :
    MsgCondPkToENone Scope F peer me pm :=
  ⟨hparse, pkToE?_eq_none_of_v3 hv3.1, hAcct, hv3.2⟩

/-! ## 2. Relocatable Poll-to-Wrapper & Slot Bridges for `v3` Reject (`[LibsignalPlacement]`) -/

/-- Lifts a relocatable `v3` poll-closure contract on Block `518` (`lsProg_518`) to
`decPkSlotSpecPlaced E2E.HooksE.A0 S stk` on Block `520` (`lsProg_520`). -/
theorem cliDecryptPrekey_v3_reject_slot_placed_of_poll [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (hpoll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S) stk')))
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (lsProg_520 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
      (lsmpl.base 520)
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed
      (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll stk' h1 h2)
      stk (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega) hstk64)

/-- Cross-block transfer of `cliDecryptPrekey_v3_reject_slot_placed_of_poll` onto any caller block
`i < 619` (such as `lsProg_579` or `cliProgPlacedSig`). -/
theorem cliDecryptPrekey_v3_reject_slot_placed_at_block_of_poll [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    [IsLsBlockProg callerProg i (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)))]
    (hpoll : ∀ stk', dpPollNeed B ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (lsProg_518 (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))))
        (lsmpl.base 518)
        (StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecState (K₀_statePlaced B S) stk')))
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 520)
      (decPkSlotSpecPlaced E2E.HooksE.A0 S stk) :=
  decPk_slot_ok_state_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_placed_at_block (callerProg := callerProg) (i := i)
      (ext := cliGhostExterns g (cliExternsPlaced mmpl W)) (K₀_statePlaced B S)
      (fun stk' h1 h2 => hpoll stk' h1 h2)
      stk (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, K₀_statePlaced,
        dpSlotPollKStatePlaced] at hstk ⊢; omega) hstk64 hi)

/-! ## 3. Spatial Split Between `closStackUnusedP1OkAt` and `v3` Stage P2 Kits -/

def v3StackRemAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8#64) 144 ∗
  memRegion (sp + 564#64) 316 ∗
  memRegion (sp + 916#64) 76 ∗
  memRegion (sp + 1016#64) 344 ∗
  memRegion (sp + 1360#64) 1344 ∗
  memRegion (sp + 2752#64) 432

theorem closStack_v3_split (sp : BitVec 64) :
    closStackUnusedP1OkAt sp ∗ memRegion (sp + 992#64) 368 =
      memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 992#64) 24 ∗
      memRegion (sp + 2704#64) 48 ∗
      v3StackRemAt sp := by
  unfold closStackUnusedP1OkAt v3StackRemAt
  rw [ProofLib.memRegion_split (sp + 564#64) 316 112 (by decide),
      ProofLib.memRegion_split (sp + 564#64 + 316#64) 36 76 (by decide),
      ProofLib.memRegion_split (sp + 992#64) 24 344 (by decide),
      ProofLib.memRegion_split (sp + 1360#64) 1344 480 (by decide),
      ProofLib.memRegion_split (sp + 1360#64 + 1344#64) 48 432 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.D3
