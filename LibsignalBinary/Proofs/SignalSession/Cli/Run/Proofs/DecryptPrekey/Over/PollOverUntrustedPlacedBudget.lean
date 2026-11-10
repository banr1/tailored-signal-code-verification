/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed D2(c) Poll Untrusted Branch and Entry Helpers

Defines budget-threaded `CliDpPollOkD2cStatePlacedAt`, `CliDpPollOkD2cStatePlacedStmt`, and
`D2cStagesPlacedStmt` on Block `518`, unpacks `dpPollSpecStateBudget` under `DecPkOkD2c`, and proves
`closure_untrusted_d2c_placed_ok` (plus `LibsignalFrozen` counterparts).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  lsLogOff withLsCodeRoLoaded LibsignalCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin hiding encodeRecord
open CryptoVerification.E2E.Record hiding Bytes
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp Bytes eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  SessionOnlyKitPlacedOkSE IdentityStoreKitPlacedOkI
  kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
  kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli hiding
  readFileSpecPlaced sessDeserializeSpecPlaced
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  CliDpPollOkD2cStatePlacedStmt D2cStagesPlacedStmt
  DpPollEntryPureD2cPlaced dpPollPre_unpack_d2c_placed
  dpPollEntrySpatialPlaced
  dpPollPost_eq_of_decPk_eq_placed dpPollOnPanic_eq_of_decPk_eq_placed
  sepWPp_pollGoal_of_decPk_eq_placed
  closure_untrusted_d2c_placed_ok
  storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c
  StageP2OverErrPlaced StageP2OverQpanCliPlacedStmt
  StageP3Prev1VRegsAtPlacedStmt StageP3Prev1VRegsA0PlacedStmt
  StageP4Prev1RawBranchPlaced StageP4Prev1BranchPlaced StageP4Prev1VRegsPlacedStmt
  cliPollStageP1_fsAt_placed dpPollPost_of_decResAt_placed
  cliFiles_eq_of_trace_eq_placed cliFsAt_of_files_eq_placed
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollKStateBudget DpPollGhostStateBudget dpPollSpecStateBudget
   dpSlotPollKStatePlaced slotFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
  (dpPollEntrySpatialPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt
   stageP1_untrusted_mangled_placed_ok
   cliPollSessBudgetEnv cliPollIdBudgetEnv
   cliPollSess_kitPlacedOkSE cliPollId_kitPlacedOkI
   cliPollStageP1_fsAt_placed dpPollPost_of_decResAt_placed
   runHooks_of_stages)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (CliStageP4Prev1Envs StageP2OverQpanCliPlacedStmt StageP4Prev1VRegsPlacedStmt
   storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget
  (StageP3Prev1VRegsPlacedStmt)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Budget-Threaded Placed D2(c) Poll Statement & Overwrite-Stage Bundle (`D2cStagesPlacedStmt`) -/

/-- Pointwise budget-threaded `[LibsignalPlacement]` D2(c) poll contract on Block `518`
(`dpPollEntryPlaced = lsmpl.base 518`) at fixed `(mmpl, gh, W, X, B, S, Scope)` and envelope
`DecPkEnv : DecPkGhost → List AllocEvent → Prop`. -/
def CliDpPollOkD2cStatePlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
    A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
  Slots.EncodeInjOn Slots.scopeKit →
  (∀ r, Scope r → Slots.scopeIn r) →
  S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

/-- Budget-threaded `[LibsignalPlacement]` D2(c) poll closure statement: `dpPollEntryPlaced`
(`lsmpl.base 518`) meets `dpPollSpecStateBudget` under `decPkDefD2c` and `DecPkOkD2c`. -/
def CliDpPollOkD2cStatePlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliDpPollOkD2cStatePlacedAt A lim ReadEnv DeserEnv (DecPkEnv W X B Scope) mmpl gh W X B S Scope

/-- Budget-threaded bundle of the three D2(c) overwrite-path stage interfaces (`StageP2Over`,
`StageP3Prev1`, `StageP4Prev1`) under `[LibsignalPlacement]`. -/
structure D2cStagesPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk) : Prop where
  stageP2Over : StageP2OverQpanCliPlacedStmt A lim P2OverErrEnv P2OverOkEnv
  stageP3Prev1 : StageP3Prev1VRegsPlacedStmt A lim tdEnv
  stageP4Prev1 : StageP4Prev1VRegsPlacedStmt A lim p4Envs

/-! ## 2. Budget-Threaded Placed Entry Unpacking & `dpPollSpecStateBudget` `RunSem` Congruence Helpers -/

/-- Budget-threaded pure invariants unpacked from
`withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget ...)` under `DecPkOkD2c`. -/
structure DpPollEntryPureD2cPlaced [LibsignalPlacement] {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  ro : LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

/-- Unpack `(withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre`
into `DpPollEntryPureD2cPlaced` and `dpPollEntrySpatialPlaced`. -/
theorem dpPollPre_unpack_d2c_placed [LibsignalPlacement]
    {W : CliHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    DpPollEntryPureD2cPlaced (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hro, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  have h2 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧
            FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗
              LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗
              preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R)))) := by
    simpa only [dpPollSpecStateBudget, dpSlotPollKStatePlaced,
      Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced, sepConj_assoc]
      using hpre0
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧
          FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
              storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗
              LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗
              preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk, hfits⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hro, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk, hfits⟩, ?_⟩
  dsimp only [dpPollEntrySpatialPlaced]
  convert h5_cx using 1
  sep_ac_rfl

theorem dpPollPost_eq_of_decPk_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g, y₁.st⟩
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁) stk')).post y₁ s0 sf =
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) stk')).post y₂ s0 sf := by
  simp only [dpPollSpecStateBudget, dpSlotPollKStatePlaced, hEq]

theorem dpPollOnPanic_eq_of_decPk_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g, y₁.st⟩
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁) stk')).onPanic y₁ s0 sf =
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) stk')).onPanic y₂ s0 sf := by
  simp only [dpPollSpecStateBudget, dpSlotPollKStatePlaced, hEq]

theorem dpPollPost_mono_of_decPk_eq_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁))
    (s0 sf : State)
    (hSub : ∀ evs, DecPkEnv₂ y₁.g evs → DecPkEnv₁ y₁.g evs)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g, y₁.st⟩
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) stk')).post y₂ s0 sf ⊢
    (withLsCodeRoLoaded lsmpl
      (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁) stk')).post y₁ s0 sf := by
  dsimp only [withLsCodeRoLoaded, dpPollSpecStateBudget, dpSlotPollKStatePlaced]
  refine sepConj_mono_left ?_
  refine Entails.sepExists_elim fun ws => Entails.trans ?_ (Entails.sepExists_intro ws)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.sepExists_elim fun evs => Entails.trans ?_ (Entails.sepExists_intro evs)
  refine Entails.sepExists_elim fun g' => Entails.trans ?_ (Entails.sepExists_intro g')
  refine Entails.sepExists_elim fun e => Entails.trans ?_ (Entails.sepExists_intro e)
  refine Entails.pure_left fun ⟨hevs, htr, hout⟩ => ?_
  have hφ : DecPkEnv₁ y₁.g evs ∧ slotTraceFT s0.fs s0.trace sf.fs sf.trace ∧
      slotOutTr (S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) g' e
        s0.trace sf.trace := ⟨hSub evs hevs, htr, hEq ▸ hout⟩
  have hEqP : (DecPkEnv₁ y₁.g evs ∧ slotTraceFT s0.fs s0.trace sf.fs sf.trace ∧
      slotOutTr (S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) g' e
        s0.trace sf.trace) = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEqP, pure_true, emp_sepConj]
  sep_frame

theorem sepWPp_pollGoal_of_decPk_eq_sub_placed [LibsignalPlacement]
    {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv₁ DecPkEnv₂ : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁))
    (s0 s1 : State) (P R : SepProp)
    (hSub : ∀ evs, DecPkEnv₂ y.g evs → DecPkEnv₁ y.g evs)
    (hEq : S₁.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      S₂.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
    (hwp :
      let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) :=
        ⟨y.out, y.fut, y.cx, y.g, y.st⟩
      SepWPp prog (s0.readReg64 .x30) s1 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (withLsCodeRoLoaded lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) stk')).post
                y₂ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (withLsCodeRoLoaded lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₂ B S₂) stk')).onPanic
                y₂ s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s1 P
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁) stk')).post
              y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv₁ B S₁) stk')).onPanic
              y s0 sf ∗ R)) := by
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨hpost, hsp, hcs⟩
    refine ⟨fun hst hmf => ?_, hsp, hcs⟩
    exact Satisfies.mono
      (sepConj_mono_left (dpPollPost_mono_of_decPk_eq_placed stk' y s0 sf hSub hEq))
      (hpost hst hmf)
  · intro sf P_f hpan hst hmf
    rw [dpPollOnPanic_eq_of_decPk_eq_placed (DecPkEnv₂ := DecPkEnv₂) stk' y s0 sf hEq]
    exact hpan hst hmf

theorem sepWPp_pollGoal_of_decPk_eq_placed [LibsignalPlacement]
    {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁))
    (s0 s1 : State) (P R : SepProp)
    (hEq : S₁.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      S₂.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
    (hwp :
      let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) :=
        ⟨y.out, y.fut, y.cx, y.g, y.st⟩
      SepWPp prog (s0.readReg64 .x30) s1 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (withLsCodeRoLoaded lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) stk')).post
                y₂ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (withLsCodeRoLoaded lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) stk')).onPanic
                y₂ s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s1 P
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁) stk')).post
              y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeRoLoaded lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁) stk')).onPanic
              y s0 sf ∗ R)) :=
  sepWPp_pollGoal_of_decPk_eq_sub_placed stk' y s0 s1 P R (fun _ h => h) hEq hwp

/-! ## 3. Budget-Threaded Placed Untrusted-Identity Branch (`trusted = .ok false`) under `DecPkOkD2c` -/

private theorem extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤
      loadCallStack (cliPollSessKitPlaced A F0 Slots.scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

private theorem hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H CryptoVerification.lsMemcpySym
      (LibsignalBinary.Heap.SpecBudget.withVmPreserved
        CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec :=
  ProofLib.HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

set_option maxHeartbeats 800000 in
/-- Statement-parameterized budget-threaded untrusted-identity branch (`trusted = .ok false`) of
`subroutine_ok_of_sepWPp_steps` for Block `518` under `[LibsignalPlacement]` and `DecPkOkD2c`. -/
theorem closure_untrusted_d2c_of_stmt_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_d2c A.repAlloc σ
    y.g.stores hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗
    cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
    cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗
    (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
    ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
    ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗
    memRegion y.out 48 ∗
    lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced, Poll.cliPreKeyStoreSpecPlaced,
      Poll.cliSignedPreKeyStoreSpecPlaced, cliKpkStoreSpecFullPlaced,
      Poll.cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := Slots.scopeKit) (encRecord := E2E.Record.encodeRecord)
    (kit := kit) (kitEnv := cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity)
    (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show LibsignalBinary.Heap.SpecBudget.withVmPreserved noAllocShimSpec =
        LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionShimBudgetSpec from rfl) ▸
      hh.codecHooks.shim)
    hh.codecHooks.alloc
    (hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F Slots.scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (cliPollSess_kitPlacedOkSE mmpl gh W hDropNz hh hRead hDeser)
    (cliPollId_kitPlacedOkI mmpl gh W hDropNz hh hRead)
    hp1_64
    (extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer)
    rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F Slots.scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0
    (cliPollStageP1_fsAt_placed hh y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS, decPkDefD2c_eq_decPkDef_of_untrusted X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins (by rw [htrusted]; decide)]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗
            cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗
            cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗
            cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
            coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗
              ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
              ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
              ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
              memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗
              memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗
              decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner] at hmf2
      refine Satisfies.mono ?_ hmf2
      dsimp only [Leftover, cliPollStoresKitsAtPlaced]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗
          Leftover ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres
          (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

/-- Closed budget-threaded untrusted-identity branch (`trusted = .ok false`) of
`subroutine_ok_of_sepWPp_steps` for Block `518` under `[LibsignalPlacement]` and `DecPkOkD2c`,
discharging Stage P1 directly via `stageP1_untrusted_mangled_placed_ok` (zero statement premises). -/
theorem closure_untrusted_d2c_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) :=
  closure_untrusted_d2c_of_stmt_placed_ok stageP1_untrusted_mangled_placed_ok
    A lim hDropNz mmpl gh W X B S Scope hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y
    hfits_p1 hevs_sub R s0 hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

/-- Convenience wrapper around `closure_untrusted_d2c_placed_ok` accepting
`ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem closure_untrusted_d2c_stagesHooks_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) :=
  closure_untrusted_d2c_placed_ok A lim hDropNz mmpl gh W X B S Scope (runHooks_of_stages hh) hRead hDeser
    hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0 hpc hrun hsp hro0 hx0 hx1 hx2
    hfiles0 hfPeer hdecOk htrusted hm_base


/-! ## `LibsignalFrozen` Counterparts -/

def CliDpPollOkD2cStateFrozenPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
    A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv) →
  Slots.EncodeInjOn Slots.scopeKit →
  (∀ r, Scope r → Slots.scopeIn r) →
  S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

def CliDpPollOkD2cStateFrozenPlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget.CliDpPollOkD2cStateFrozenPlacedAt A lim ReadEnv DeserEnv (DecPkEnv W X B Scope) mmpl gh W X B S Scope


structure D2cStagesFrozenPlacedStmt [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk) : Prop where
  stageP2Over : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux.StageP2OverQpanCliFrozenPlacedStmt A lim P2OverErrEnv P2OverOkEnv
  stageP3Prev1 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget.StageP3Prev1VRegsFrozenPlacedStmt A lim tdEnv
  stageP4Prev1 : StageP4Prev1VRegsPlacedStmt A lim p4Envs

structure DpPollEntryPureD2cFrozenPlaced [LibsignalPlacement] {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  fr : CryptoVerification.LibsignalFrozen lsmpl s0.mem
  ro : LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

theorem dpPollPre_unpack_d2c_frozen_placed [LibsignalPlacement]
    {W : CliHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget.DpPollEntryPureD2cFrozenPlaced (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hfr, hpre0⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpre
  have hro : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr.2, hfr.1⟩
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro, hpre0⟩
  obtain ⟨hp, hsp⟩ :=
    dpPollPre_unpack_d2c_placed (W := W) (Scope := Scope) hSemOk stk' y R s0 hpre_ro
  exact ⟨⟨hfr, hp.ro, hp.x0, hp.x1, hp.x2, hp.stk_le_sp, hp.files_eq, hp.coins_lt,
    hp.filesOkPeer, hp.decPkOk, hp.fits⟩, hsp⟩

theorem sepWPp_pollGoal_of_decPk_eq_frozen_placed [LibsignalPlacement]
    {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁))
    (s0 s1 : State) (P R : SepProp)
    (hEq : S₁.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      S₂.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
    (hwp :
      let y₂ : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) :=
        ⟨y.out, y.fut, y.cx, y.g, y.st⟩
      SepWPp prog (s0.readReg64 .x30) s1 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) stk')).post
                y₂ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
                (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₂) stk')).onPanic
                y₂ s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s1 P
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁) stk')).post
              y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
              (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S₁) stk')).onPanic
              y s0 sf ∗ R)) := by
  exact sepWPp_pollGoal_of_decPk_eq_placed stk' y s0 s1 P R hEq hwp

theorem closure_untrusted_d2c_of_stmt_frozen_placed_ok [LibsignalPlacement]
    (hUntrusted : StageP1UntrustedMangledPlacedStmt)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hfr0 : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  have hro0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfr0.2, hfr0.1⟩
  exact closure_untrusted_d2c_of_stmt_placed_ok hUntrusted A lim hDropNz mmpl gh W X B S Scope
    hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y hfits_p1 hevs_sub R s0
    hpc hrun hsp hro0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

theorem closure_untrusted_d2c_frozen_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hfr0 : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget.closure_untrusted_d2c_of_stmt_frozen_placed_ok stageP1_untrusted_mangled_placed_ok
    A lim hDropNz mmpl gh W X B S Scope hh hRead hDeser hinjK hsub hS stk' hneed hstk63 y
    hfits_p1 hevs_sub R s0 hpc hrun hsp hfr0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

theorem closure_untrusted_d2c_stagesHooks_frozen_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit A lim DeserEnv))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = dpPollEntryPlaced)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hfr0 : CryptoVerification.LibsignalFrozen lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗
      lsLogOff ∗
      A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  exact LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget.closure_untrusted_d2c_frozen_placed_ok A lim hDropNz mmpl gh W X B S Scope
    (runHooks_of_stages hh) hRead hDeser hinjK hsub hS stk' hneed hstk63 y
    hfits_p1 hevs_sub R s0 hpc hrun hsp hfr0 hx0 hx1 hx2 hfiles0 hfPeer hdecOk htrusted hm_base

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrustedPlacedBudget
