/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize

/-!
# Budget-Threaded Placed CLI Poll Overwrite-Path (`Path C`) Stage P4 Spatial Bridges

Extends `PollOverP4SpatialPlaced` to `RustCliAllocBudget M`, proving budget-threaded
`dpPollPost_of_slotTraceFT_placed`, `overExit_entails_dpPollPost_placed`,
`stageP3MidPathC_entails_p4_placed`, and `stageP4PathCExit_entails_exit_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget

open Arm64 Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  pathC_recPrev1Ok_of_tryDecrypt_placed cliPollPrev1StoresKitsAtPlaced_entails_storesAt
  overGenP3CallFrame_placed overGenP3S5PostFrame_placed overStackAt_poll_exit_join
  overGenP3Pre_placed overStageP3ErrPostPrevEmpty_placed overPathAP4RemAtPlaced
  dpPollPost_of_slotTraceFT_placed overExit_entails_dpPollPost_placed
  stageP3MidPathC_entails_p4_placed stageP4PathCExit_entails_exit_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev pathC_recPrev1Ok_of_tryDecrypt_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.pathC_recPrev1Ok_of_tryDecrypt_placed

abbrev cliPollPrev1StoresKitsAtPlaced_entails_storesAt :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollPrev1StoresKitsAtPlaced_entails_storesAt

abbrev overGenP3CallFrame_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3CallFrame_placed

abbrev overGenP3S5PostFrame_placed :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3S5PostFrame_placed

abbrev overStackAt_poll_exit_join :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.overStackAt_poll_exit_join

/-- Budget-threaded `overGenP3Pre_placed` over `A.atState lim st_b s` (`A.repAlloc` +
`A.pool lim st_b s`). -/
def overGenP3Pre_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st_b : M.σ) [LibsignalPlacement] (sp fp coroPtr ctxPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32)
    (rest : List (BitVec 8)) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3Pre_placed
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg s

/-- Budget-threaded `overStageP3ErrPostPrevEmpty_placed` over `A.atState lim st_b s`. -/
def overStageP3ErrPostPrevEmpty_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) : SepProp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.overStageP3ErrPostPrevEmpty_placed
    (A.atState lim st_b s) s0 s coroPtr outPtr e

/-- Budget-threaded `overPathAP4RemAtPlaced` parameterized by `A_r : RustAlloc` (`A.repAlloc` /
`A.atState lim st_b s`, independent of `.pool`) and `DpPollGhostStateBudget`. -/
def overPathAP4RemAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (A_r : RustAlloc) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (sp rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (msgVer pid kid spkId : BitVec 32)
    (preKeyMsgRem coinsPost : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr ∗
  memRegion (y.fut + 0x250#64) 48 ∗
  memRegion (y.fut + 0x2d8#64) 184 ∗
  memRegion (y.fut + 0x390#64) 1 ∗
  memRegion (y.fut + 0x398#64) 16 ∗
  memRegion (y.fut + 0x428#64) 64 ∗
  memRegion (y.fut + 0x468#64) 40 ∗
  memRegion (y.fut + 0x490#64) 32 ∗
  memRegion (y.fut + 0x4f2#64) 1 ∗
  coroPostP2UnusedAt y.fut ∗
  (sp ↦₆₄ 0#64) ∗
  genP3S5SpillRem sp ∗
  memRegion (sp + 0x930#64) 48 ∗
  ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
  ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
  spLowGapsAt sp ∗
  ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
  ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
  ((sp + 0xc8#64) ↦₆₄ y.out) ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
  memRegion (sp + 0x290#64) 16 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  sp2b0GapsAt sp ∗
  memRegion (sp + 0x394#64) 12 ∗
  ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  memRegion (sp + 0x3ad#64) 27 ∗
  memRegion (sp + 0x410#64) 296 ∗
  memRegion (sp + 0x538#64) 24 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  spHighGapsAt sp ∗
  protocolAddressAt A_r y.g.me y.g.meA ∗
  signalMessageAt A_r whisperG whisperMsgPtr y.g.msg.message ∗
  preKeyMsgRem ∗
  LsTokenInit ∗
  coinsPost ∗
  (cliPollSpkKitPlaced A_r y.g.F spkId (cliKitStk B)).storeAt
    (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
  dirAt A_r (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
    (dpClosSubStack B - stageP4CallStack
      (cliPollSessKitPlaced A_r y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced A_r y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKitPlaced A_r y.g.F pid (cliKitStk B))
      (cliPollKpkKitPlaced A_r y.g.F kid spkId y.g.msg.baseKey (cliKitStk B)))

private theorem pure_sepConj_intro_placed {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, emp_sepConj]
  exact h

/-- Budget-threaded `dpPollPost_of_slotTraceFT_placed` packaging `evs`, `DecPkEnv y.g evs`, and
`A.pool lim (M.stepEvents evs y.st) sf` into `dpPollSpecStateBudget.post`. -/
theorem dpPollPost_of_slotTraceFT_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) (B : RunBudgets) (S : RunSem)
    (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 sf : State) (evs : List AllocEvent)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) Bytes)
    (Leftover : SepProp)
    (hevs : DecPkEnv y.g evs)
    (hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt A.repAlloc y.out e ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗
      A.pool lim (M.stepEvents evs y.st) sf ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf := by
  have hdec := decResAt_entails_dpWords_resHeap A.repAlloc y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws ∗ dpResHeap A.repAlloc ws e) ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g y.st s0 sf ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗ dpResHeap A.repAlloc ws e) ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗
        (storesAt A.repAlloc y.g.stores g' ∗ dpResHeap A.repAlloc ws e ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by
    ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws ?_)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  dsimp only [K, dpSlotPollKStatePlaced]
  exact Entails.sepExists_right evs
    (Entails.sepExists_right g'
      (Entails.sepExists_right e
        (pure_sepConj_intro_placed ⟨hevs, hft, hout⟩ (Entails.refl _))))

/-- Budget-threaded `overExit_entails_dpPollPost_placed` over `TraceFsSound` and `RustCliAllocBudget M`. -/
theorem overExit_entails_dpPollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 sf : State) (evs : List AllocEvent)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) Bytes)
    (Leftover : SepProp)
    (hevs : DecPkEnv y.g evs)
    (hfs : TraceFsSound (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (hsteps : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt A.repAlloc y.out res ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗
      A.pool lim (M.stepEvents evs y.st) sf ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      memRegion sp 3280 ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf := by
  dsimp only
  have hstk_back := overStackAt_poll_exit_join s0.sp B stk' hneed hstk63
  have hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
    ⟨htr ▸ List.prefix_refl s0.trace,
     hfs.files_eq hsteps (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil,
     congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact dpPollPost_of_slotTraceFT_placed A lim DecPkEnv B S stk' y s0 sf evs g' res Leftover
    hevs hft hout

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP3MidPathC_entails_p4_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s2 s' : State)
    (rngPtr initErrsPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (enc pt : List (BitVec 8))
    (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let A_s : RustAlloc := A.atState lim st_b s'
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ
    let prev1Kit := cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ
    let ikit := cliPollIdKitPlaced A_s y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A_s y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A_s y.g.F spkId σ
    let kpkKit := cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ
    (stageP3DispatchOkMidPrev1Placed A_s s0 s2 y.fut y.out initErrsPtr
        prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
      overGenP3S5PostFrame_placed A_s sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      overScratch s2.sp) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    stageP4Prev1PrePlaced 0#64 prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevCap prevPtr ptCap ptPtr initErrsPtr
      opkId? kpkId spkId 0#8 pt enc
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      G' st' ∗
    overPathAP4RemAtPlaced A_s B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost := by
  dsimp only
  let A_s : RustAlloc := A.atState lim st_b s'
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left
          (cliPollSessKit_storeAt_entails_prev1 (A := A_s) (b := 0#64)
            (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer) (σ := cliKitStk B)
            (y.g.stores + 0xf0#64) StoresGhost.opened.sessions)))))))) ?_
  dsimp only [overGenP3S5PostFrame_placed]
  unfold stageP3DispatchOkMidPrev1Placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.overGenP3S5PostFrame_placed
    stageP3CoroFrameAt stageP3OverStackFrameAt stageP4Prev1PrePlaced stageP4Prev1RawPrePlaced
    stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hstk1 : memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack = stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 : memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      stackAt sp rootStack = stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk3 := stackAt_subStack_sub_eq sp B
    (cliPollStageP4Stack_le_subStack A_s 0#64 y.g.F Slots.scopeKit y.g.peer
      pid kpkId spkId y.g.msg.baseKey B) hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) := by
    rw [hstk1, hstk2]; exact hstk3
  have hvt_s : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced A_s y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack
        (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack
        (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs2_sp, hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq,
      overScratch_eq_sp538_spHighGaps sp, coro_2ac_20_eq_8_12 y.fut,
      coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr,
      sp_2b0_192_split sp, sp_3e0_344_eq_48_296 sp]
  apply Entails.of_eq
  have hswap_all : ∀ (Rest : SepProp),
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗ Rest =
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗ Rest := by
    intro Rest; rw [hstk_swap]
  trans ((memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack)) ∗
    (((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
      ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
      ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
      ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
      ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗
      ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
      ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗
      ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym)) ∗
      prevVecAt A_s (y.fut + 0xe0#64) prevCap prevPtr [enc] ∗
      ((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId) ∗
      memRegion (y.fut + 0x2c8#64) 16 ∗ ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x250#64) 20 ∗
      ((sp + 0x278#64) ↦₆₄ ptCap) ∗ ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A_s.pool ∗
      sessionStateAt A_s (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
      (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A_s.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0x250#64) 48 ∗ memRegion (y.fut + 0x2d8#64) 184 ∗
      memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
      memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
      memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
      coroPostP2UnusedAt y.fut ∗ (sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗
      memRegion (sp + 0x930#64) 48 ∗ ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗ spLowGapsAt sp ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((sp + 0xb8#64) ↦₃₂ msgVer) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x264#64) 12 ∗
      ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗ sp2b0GapsAt sp ∗
      memRegion (sp + 0x394#64) 12 ∗ ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x3a8#64) 4 ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      memRegion (sp + 0x3ad#64) 27 ∗ memRegion (sp + 0x410#64) 296 ∗
      memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      signalMessageAt A_s whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗ LsTokenInit ∗ coinsPost ∗
      (cliPollSpkKitPlaced A_s y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub))
  · sep_frame
  · rw [hswap_all]; sep_frame

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP4PathCExit_entails_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S)) (s0 s' : State)
    (rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp) (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32) (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt A.repAlloc y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf) (hid : g'.identity = istf) (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed) (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let A_s : RustAlloc := A.atState lim st_b s'
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ
    let ikit := cliPollIdKitPlaced A_s y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A_s y.g.F pid σ
    let kpkKit := cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ
    stageP4Prev1ExitAtPlaced 0#64 prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    overPathAP4RemAtPlaced A_s B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost ⊢
    decResAt A.repAlloc y.out res ∗ storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      lsLogOff ∗ A.pool lim st_b s' ∗ (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗ stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280 := by
  dsimp only
  let A_s : RustAlloc := A.atState lim st_b s'
  unfold stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hvt_s : (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced A_s y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
      stackAt sp (stageP4CallStack
        (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
        (cliPollPkKitPlaced A_s y.g.F pid σ)
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4Stack_le_subStack A_s 0#64 y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B) hsp_sub).symm
  have hstores :
      (cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKitPlaced A_s y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt A.repAlloc y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollPrev1StoresKitsAtPlaced_entails_storesAt (A := A_s) y.g.F y.g.peer pid spkId kpkId
      y.g.msg.baseKey σ y.g.stores g'
  have hcopy_join :=
    (coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr).symm
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hstack := stageP4Exit_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA
    0xfffffffffffffffe#64 ptCap ptPtr (BitVec.ofNat 64 pt.length) 0#64 initErrsPtr 0#64 msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      outSlot ∗
      ((cliPollSessPrev1KitPlaced A_s y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced A_s y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced A_s y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) pstf ∗
        (cliPollSpkKitPlaced A_s y.g.F spkId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) kstf ∗
        dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st_b s' ∗
      (LsTokenInit ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
          ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗ ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
          ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗ ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
          ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗ ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
          ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗ ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym))) ∗
          coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr) ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
          (dpClosSubStack B - stageP4CallStack
            (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
            (cliPollPkKitPlaced A_s y.g.F pid σ)
            (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced A_s y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A_s y.g.F y.g.peer σ)
          (cliPollPkKitPlaced A_s y.g.F pid σ)
          (cliPollKpkKitPlaced A_s y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗
      ((sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x264#64) 12 ∗
        ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp + 0x278#64) ↦₆₄ ptCap) ∗
        ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ sp2b0GapsAt sp ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (sp + 0x3ad#64) 27 ∗
        ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by
      have hpa : protocolAddressAt A_s = protocolAddressAt A.repAlloc := rfl
      have hsm : signalMessageAt A_s = signalMessageAt A.repAlloc := rfl
      rw [hpa, hsm, RustCliAllocBudget.atState_pool]
      sep_frame)) ?_
  rw [hcopy_join, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  have hcoro_fold :
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        memRegion (y.fut + 0x2c8#64) 200 ∗ memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗ memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗ memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗ coroPostP2UnusedAt y.fut) ⊢
      dpFutDoneAt y.fut := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  have hstack_fold := Entails.trans (sepConj_mono_left hsp0) hstack
  exact Entails.trans
    (sepConj_mono hout (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hcoro_fold (sepConj_mono_right hstack_fold))))))))))
    (Entails.of_eq (by dsimp only [lsLogOff]; sep_frame))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
