/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathC
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Closure
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Inst
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# D2(c) Poll Untrusted Branch and Entry Helpers (`PollOverUntrusted`)

Defines `CliDpPollOkD2cStateAt`, `CliDpPollOkD2cStateStmt`, and `D2cStagesStmt` (plus `Ext`
variants), unpacks `dpPollSpecState.inImage` under `DecPkOkD2c`, and proves
`closure_untrusted_d2c_ok` (`trusted = .ok false`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. D2(c) Poll Statement & Overwrite-Stage Bundle (`D2cStagesStmt`) -/

/-- Image-fixed D2(c) state-coupled poll contract for `cliDpPollName` under `decPkDefD2c` and
`DecPkOkD2c` (definitionally equal to `RunProofs.CliDpPollOkD2cStateAt img`). -/
def CliDpPollOkD2cStateAt (img : Obj.Image) : Prop :=
  ∀ (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile) →
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState E2E.HooksE.A0 img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
        ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img)

/-- Image-polymorphic D2(c) state-coupled poll contract for `cliDpPollName` (definitionally equal
to `RunProofs.CliDpPollOkD2cStateStmt`). -/
def CliDpPollOkD2cStateStmt : Prop :=
  ∀ {img : Obj.Image}, CliDpPollOkD2cStateAt img

/-- Bundle of the three overwrite-path (`Path C`, 1 archived previous session) stage contracts
needed on top of `stages2_inst : ClosureStages2Stmt` to close `CliDpPollOkD2cStateStmt`. -/
structure D2cStagesStmt : Prop where
  stageP2Over : StageP2OverQpanCliStmt
  stageP3Prev1 : Over.StageP3Prev1VRegsA0Stmt
  stageP4Prev1 : Over.StageP4Prev1VRegsStmt

/-- `Ext`-parameterized image-fixed D2(c) state-coupled poll contract for `cliDpPollName` under
`CliExternsOk P A ext`, `decPkDefD2c`, and `DecPkOkD2c` (definitionally equal to
`RunProofs.CliDpPollOkD2cStateAtExt img`). -/
def CliDpPollOkD2cStateAtExt (img : Obj.Image) : Prop :=
  ∀ (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliExternsOk P A ext →
    Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDefD2c X P Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKState A img B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
        ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img)

/-- Image-polymorphic `Ext`-parameterized D2(c) state-coupled poll contract for `cliDpPollName`
(definitionally equal to `RunProofs.CliDpPollOkD2cStateStmtExt`). -/
def CliDpPollOkD2cStateStmtExt : Prop :=
  ∀ {img : Obj.Image}, CliDpPollOkD2cStateAtExt img

/-- `Ext`-parameterized stage bundle consumed by `cliDpPollOk_d2c_at_ext_of_stages` /
`decPkD2cSlotOk_ext_of_stages`, decoupled from `sessDeserializeSpec` (avoiding `A0`-only pool
assumptions) and 0-stack `AllocContracts`. -/
structure D2cStagesExtStmt : Prop where
  stageP1Ok : StageP1OkXExtStmt
  stageP1Untrusted : StageP1UntrustedXExtStmt
  stageP2PathA : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    StageP2PathAQpanExtAtB img P A B (cliExternsWith ext)
  stageP3PathA : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    StageP3GenPathAExtAt img P A (cliExternsWith ext)
  stageP4PathA : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    StageP4PathAV1ExtAt img A B (cliExternsWith ext)
  stageP2PathB : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    StageP2MatchedFramedExtAt img A (cliExternsWith ext)
  stageP3PathB : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    StageP3GenPathBExtAt img P A (cliExternsWith ext)
  stageP4PathB : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    StageP4MatchedExtAt img A B (cliExternsWith ext)
  stageP2Over : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    StageP2OverQpanExtAt img P A (cliExternsWith ext)
  stageP3Prev1 : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    StageP3Prev1PathCExtAt img P A (cliExternsWith ext)
  stageP4Prev1 : ∀ {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (B : RunBudgets),
    CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
    extHookStack ≤ B.readFile →
    StageP4Prev1PathCExtAt img A B (cliExternsWith ext)

/-! ## 2. Entry Unpacking & `dpPollSpecState` `RunSem` Congruence Helpers -/

/-- Pure invariants unpacked from `dpPollSpecState.inImage` under `DecPkOkD2c`. -/
structure DpPollEntryPureD2c {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) : Prop where
  inv : ImgCallInv img s0
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkD2c ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg

theorem dpPollPre_unpack_d2c
    {img : Obj.Image} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).pre y s0 ∗ R) :
    DpPollEntryPureD2c (W := W) (Scope := Scope) img stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatial img stk' y s0 R) := by
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgs img y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              E2E.HooksE.A0.pool ∗
              preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))))) := by
    simpa only [Spec.inImage, dpPollSpecState, dpSlotPollKState, slotFrame, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hinv, h2⟩
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
              storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
              protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
              protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              E2E.HooksE.A0.pool ∗
              preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hinv, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk⟩, ?_⟩
  dsimp only [dpPollEntrySpatial]
  convert h5_cx using 1
  ac_rfl

theorem dpPollPost_eq_of_decPk_eq {img : Obj.Image} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g⟩
    ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₁) stk').inImage img).post y₁ s0 sf =
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₂) stk').inImage img).post y₂ s0 sf := by
  simp only [Spec.inImage, dpPollSpecState, dpSlotPollKState, hEq]

theorem dpPollOnPanic_eq_of_decPk_eq {img : Obj.Image} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g⟩
    ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₁) stk').inImage img).onPanic y₁ s0 sf =
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₂) stk').inImage img).onPanic y₂ s0 sf := by
  simp only [Spec.inImage, dpPollSpecState, dpSlotPollKState, hEq]

theorem sepWPp_pollGoal_of_decPk_eq
    {img : Obj.Image} {prog : Program} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₁))
    (s0 s1 : State) (P R : SepProp)
    (hEq : S₁.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      S₂.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
    (hwp :
      let y₂ : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S₂) :=
        ⟨y.out, y.fut, y.cx, y.g⟩
      SepWPp prog (s0.readReg64 .x30) s1 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₂) stk').inImage img).post
                y₂ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₂) stk').inImage img).onPanic
                y₂ s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s1 P
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₁) stk').inImage img).post
              y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S₁) stk').inImage img).onPanic
              y s0 sf ∗ R)) := by
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨hpost, hsp, hcs⟩
    refine ⟨fun hst hmf => ?_, hsp, hcs⟩
    rw [dpPollPost_eq_of_decPk_eq stk' y s0 sf hEq]
    exact hpost hst hmf
  · intro sf P_f hpan hst hmf
    rw [dpPollOnPanic_eq_of_decPk_eq stk' y s0 sf hEq]
    exact hpan hst hmf

/-- `Ext`-parameterized pure invariants unpacked from `dpPollSpecState.inImage` under `DecPkOkD2c`. -/
structure DpPollEntryPureD2cExt {P : PEParams} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) : Prop where
  inv : ImgCallInv img s0
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkD2c P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg

theorem dpPollPre_unpack_d2c_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOkD2c P Scope F peer me pm)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (R : SepProp) (s0 : State)
    (hpre : s0.mem ⊨
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).pre y s0 ∗ R) :
    DpPollEntryPureD2cExt (P := P) (A := A) (Scope := Scope) img stk' y s0 ∧
      (s0.mem ⊨ dpPollEntrySpatialExt A img stk' y s0 R) := by
  have h1 : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgs img y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A y.g.stores StoresGhost.opened ∗
              protocolAddressAt A y.g.peer y.g.peerA ∗
              protocolAddressAt A y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              A.pool ∗
              preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))))) := by
    simpa only [Spec.inImage, dpPollSpecState, dpSlotPollKState, slotFrame, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hinv, h2⟩
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗
          (dpCxAt y.cx ∗
            (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
              storesAt A y.g.stores StoresGhost.opened ∗
              protocolAddressAt A y.g.peer y.g.peerA ∗
              protocolAddressAt A y.g.me y.g.meA ∗
              coinsInstalled img y.g.coinsP y.g.coins ∗
              TokenInit img ∗
              logOff img ∗
              A.pool ∗
              preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗
              R))) := by
    convert h3 using 1
    ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hinv, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk⟩, ?_⟩
  dsimp only [dpPollEntrySpatialExt]
  convert h5_cx using 1
  ac_rfl

theorem dpPollPost_eq_of_decPk_eq_ext {A : RustAlloc} {img : Obj.Image} {B : RunBudgets}
    {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostState (dpSlotPollKState A img B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostState (dpSlotPollKState A img B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g⟩
    ((dpPollSpecState (dpSlotPollKState A img B S₁) stk').inImage img).post y₁ s0 sf =
      ((dpPollSpecState (dpSlotPollKState A img B S₂) stk').inImage img).post y₂ s0 sf := by
  simp only [Spec.inImage, dpPollSpecState, dpSlotPollKState, hEq]

theorem dpPollOnPanic_eq_of_decPk_eq_ext {A : RustAlloc} {img : Obj.Image} {B : RunBudgets}
    {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y₁ : DpPollGhostState (dpSlotPollKState A img B S₁))
    (s0 sf : State)
    (hEq : S₁.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins =
      S₂.decryptPrekey y₁.g.F y₁.g.peer.val y₁.g.me.val y₁.g.msg y₁.g.coins) :
    let y₂ : DpPollGhostState (dpSlotPollKState A img B S₂) :=
      ⟨y₁.out, y₁.fut, y₁.cx, y₁.g⟩
    ((dpPollSpecState (dpSlotPollKState A img B S₁) stk').inImage img).onPanic y₁ s0 sf =
      ((dpPollSpecState (dpSlotPollKState A img B S₂) stk').inImage img).onPanic y₂ s0 sf := by
  simp only [Spec.inImage, dpPollSpecState, dpSlotPollKState, hEq]

theorem sepWPp_pollGoal_of_decPk_eq_ext
    {A : RustAlloc} {img : Obj.Image} {prog : Program} {B : RunBudgets} {S₁ S₂ : RunSem}
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S₁))
    (s0 s1 : State) (P R : SepProp)
    (hEq : S₁.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
      S₂.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
    (hwp :
      let y₂ : DpPollGhostState (dpSlotPollKState A img B S₂) :=
        ⟨y.out, y.fut, y.cx, y.g⟩
      SepWPp prog (s0.readReg64 .x30) s1 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              ((dpPollSpecState (dpSlotPollKState A img B S₂) stk').inImage img).post
                y₂ s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              ((dpPollSpecState (dpSlotPollKState A img B S₂) stk').inImage img).onPanic
                y₂ s0 sf ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s1 P
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            ((dpPollSpecState (dpSlotPollKState A img B S₁) stk').inImage img).post
              y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            ((dpPollSpecState (dpSlotPollKState A img B S₁) stk').inImage img).onPanic
              y s0 sf ∗ R)) := by
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨hpost, hsp, hcs⟩
    refine ⟨fun hst hmf => ?_, hsp, hcs⟩
    rw [dpPollPost_eq_of_decPk_eq_ext stk' y s0 sf hEq]
    exact hpost hst hmf
  · intro sf P_f hpan hst hmf
    rw [dpPollOnPanic_eq_of_decPk_eq_ext stk' y s0 sf hEq]
    exact hpan hst hmf

/-! ## 3. Untrusted-Identity Branch (`trusted = .ok false`) under `DecPkOkD2c` -/

theorem closure_untrusted_d2c_ok
    (hUntrusted : StageP1UntrustedTrapExtStmt)
    {img : Obj.Image} (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.recordDeserializeName)
      (sessDeserializeSpec Slots.scopeKit E2E.HooksE.A0 img))
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr cliDpPollName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hinv0 : ImgCallInv img s0)
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
      dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
      memRegion y.cx 32 ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := tripleRatchetProgAtExt img.base (cliExterns W)
    let K := dpSlotPollKState E2E.HooksE.A0 img B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit E2E.HooksE.A0 img.base y.g.F pid σ
  let spkKit := cliPollSpkKit E2E.HooksE.A0 img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit E2E.HooksE.A0 img.base y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hm_vt :=
    satisfies_stageP1VtablesAt
      (cliPollSess_vtablesOk (A := E2E.HooksE.A0) himg y.g.F Slots.scopeKit y.g.peer σ)
      (cliPollId_vtablesOk (A := E2E.HooksE.A0) himg y.g.F y.g.peer σ)
      hinv0.1 hm_base
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAt_d2c img.base σ y.g.stores
    hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨ stageP1VtablesAt img kit ikit ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAt E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗
        logOff img ∗
        E2E.HooksE.A0.pool ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R) :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores))))) hm_vt
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := E2E.HooksE.A0)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1 img y.g y.fut,
      preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAt, stageP1VtablesAt] at hm_flat
  rw [sessVt_eq_cliPollSessKit E2E.HooksE.A0 img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit E2E.HooksE.A0 img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit E2E.HooksE.A0 img y.g.F pid σ,
      signedVt_eq_cliPollSpkKit E2E.HooksE.A0 img y.g.F sid σ,
      kyberVt_eq_cliPollKpkKit E2E.HooksE.A0 img y.g.F kid sid kbk σ] at hm_flat
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
    ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
    ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
    ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
    ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
    ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
    ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
    ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
    ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
    logOff img ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    E2E.HooksE.A0.pool ∗
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
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    TokenInit img
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    y.g.peer y.g.msg.identityKey
    hh.allocHooks
    hh.allocContracts
    (Slots.trapsOnly_trTrap_cli img.base W)
    (cliPollSess_kitOkSE_of_deser W himg y.g.F Slots.scopeKit y.g.peer B hDeser)
    (cliPollId_kitOkIE W himg y.g.F y.g.peer B)
    hp1_64 rfl rfl
    (fun _ (h : kit.loadRel StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : ikit.trustRel StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    (cliBase_aligned himg) hinv0
    (cliPollStageP1_fsAt hh y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _hFf, _⟩
    refine ⟨?_, hspf, calleeSavedPreserved_of_closure hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKit, cliPollIdKit, cliSessionStoreSpec,
        cliIdStoreSpecFull, cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSess_loadRel hinjK hsub hfPeer hload
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
    have hres := apiDecResultAt_untrusted_entails_decResAt E2E.HooksE.A0 y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0)
      img.base (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      stageP1VtablesAt img kit ikit ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt E2E.HooksE.A0 y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAt E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) ∗
          logOff img ∗
          E2E.HooksE.A0.pool ∗
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
      dsimp only [Leftover, stageP1VtablesAt, cliPollStoresKitsAt]
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗
          E2E.HooksE.A0.pool ∗
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
    have hpost := dpPollPost_of_decResAt B S stk' y s0 sf StoresGhost.opened
      (.error (.untrustedIdentity y.g.peer.val)) Leftover hh hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom stk' y hoom hmf

set_option maxHeartbeats 800000 in
/-- `Ext`-parameterized untrusted-identity branch (`trusted = .ok false`) of `cliDpPollName` on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` under `CliExternsOk P A ext`,
`StageP1UntrustedXExtStmt`, and `DecPkOkD2c` (using `Slots.cliSessKitOkSE_scopeKit_ext` and
`cliIdKitOkIE_ext_of_externsOk_full`, avoiding `sessDeserializeSpec` without `A.pool`). -/
theorem closure_untrusted_d2c_ext_ok
    (hUntrusted : StageP1UntrustedXExtStmt)
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : extHookStack ≤ B.readFile)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : S.decryptPrekey = decPkDefD2c X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr cliDpPollName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hinv0 : ImgCallInv img s0)
    (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx)
    (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkD2c P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗
      dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
      memRegion y.cx 32 ∗
      storesAt A y.g.stores StoresGhost.opened ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      A.pool ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      stackAt s0.sp stk' ∗
      R) :
    let prog := tripleRatchetProgAtExt img.base (cliExternsWith ext)
    let K := dpSlotPollKState A img B S
    ∃ P0 Fr : SepProp, (s0.mem ⊨ P0 ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P0
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  have hh := RunHooksExt.of_externsOk hOk img
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  let pkKit := cliPollPkKit A img.base y.g.F pid σ
  let spkKit := cliPollSpkKit A img.base y.g.F sid σ
  let kpkKit := cliPollKpkKit A img.base y.g.F kid sid kbk σ
  let sp := s0.sp - 0xcd0#64
  have hm_vt :=
    satisfies_stageP1VtablesAt
      (cliPollSess_vtablesOk (A := A) himg y.g.F Slots.scopeKit y.g.peer σ)
      (cliPollId_vtablesOk (A := A) himg y.g.F y.g.peer σ)
      hinv0.1 hm_base
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAt_d2c_ext (A := A) img.base σ
    y.g.stores hsub hfPeer hdecOk pid sid kid kbk
  have hm_stores : s0.mem ⊨ stageP1VtablesAt img kit ikit ∗
      (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgs img y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A y.g.peer y.g.peerA ∗
        protocolAddressAt A y.g.me y.g.meA ∗
        coinsInstalled img y.g.coinsP y.g.coins ∗
        TokenInit img ∗
        logOff img ∗
        A.pool ∗
        preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R) :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent_stores))))) hm_vt
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A)
    img.base y.g.F Slots.scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1 img y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAt, stageP1VtablesAt] at hm_flat
  rw [sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      signedVt_eq_cliPollSpkKit A img y.g.F sid σ,
      kyberVt_eq_cliPollKpkKit A img y.g.F kid sid kbk σ] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗
    memRegion (y.fut + 0x100#64) 336 ∗ cells (y.fut + 0x250#64) 6 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗
    ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
    ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (img.base + ikit.trustShimOff)) ∗
    ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
    ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
    ((img.base + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ∗
    ((img.base + ikit.trustFutVtOff) ↦₆₄ᵣ (img.base + ikit.trustFutDropOff)) ∗
    ((img.base + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
    ((img.base + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.trustPollOff)) ∗
    logOff img ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    A.pool ∗ stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
    ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut ∗
    closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    y.g.peer y.g.msg.identityKey hh.alloc hh.allocHooks
    (Slots.cliSessKitOkSE_scopeKit_ext (readStk := B.readFile) hOk himg
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hread)
    (cliIdKitOkIE_ext_of_externsOk_full (readStk := B.readFile) hOk himg
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hread)
    hp1_64
    (by
      have hext : extHookStack = 16384 := rfl
      have hdeser : 32768 ≤ E2E.Record.recDeserializeStack := by decide
      dsimp [kit, σ, loadCallStack, cliPollSessKit, cliSessionStoreSpec, cliKitStk,
            SessKit.loadPollNeed]
      omega)
    rfl rfl
    (fun _ (h : kit.loadRel StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : ikit.trustRel StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    (cliBase_aligned himg) hinv0
    (cliPollStageP1_fsAt_ext hh.fs y.g.F Slots.scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _hFf, _⟩
    refine ⟨?_, hspf, calleeSavedPreserved_of_closure hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKit, cliPollIdKit, cliSessionStoreSpec,
        cliIdStoreSpecFull, cliIdentityStoreSpec] using htr_evs
    have hloadRec : Slots.loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSess_loadRel (A := A) (b := img.base) (σ := σ) hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS, decPkDefD2c_eq_decPkDef_of_untrusted X P Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins (by rw [htrusted]; decide)]
      exact decPkDef_of_trust_err X P Scope y.g.F y.g.peer.val y.g.me.val
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
    have hres := apiDecResultAt_untrusted_entails_decResAt A y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAt_entails_storesAt (A := A)
      img.base (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      stageP1VtablesAt img kit ikit ∗ coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A y.g.msgG y.g.msgA y.g.msg) ∗
          logOff img ∗ A.pool ∗ Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : (cliIdStoreSpecFull A img.base cliIo.rd y.g.F cliWrOk y.g.peer
          IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile) IdKit.saveShimNeed
          (IdKit.savePollNeed B.readFile)).trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      rw [htrust_id] at hmf2
      dsimp only [Fr_inner, Leftover, stageP1VtablesAt, cliPollStoresKitsAt,
        kit, ikit, pkKit, spkKit, kpkKit, pid, sid, kid, kbk, σ,
        cliPollSessKit, cliPollIdKit, cliKitStk] at hmf2 ⊢
      refine Satisfies.mono ?_ hmf2
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗ Leftover ∗
          dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
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
    have hpost := dpPollPost_of_decResAt_ext B S stk' y s0 sf StoresGhost.opened
      (.error (.untrustedIdentity y.g.peer.val)) Leftover hh.fs hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro sf P_f hoom _hsteps hmf
    rw [← sepConj_assoc] at hmf
    exact dpPollOnPanic_of_closOom stk' y hoom hmf

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
