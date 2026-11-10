/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Entry and Error-Exit Folds

Generalizes `pathAInnerFramePlaced`, `kyberPtr ≠ 0` extraction bridges,
`stageP2_entry_unpack_pathA_placed`, and `p2ErrFrame_fold_pathA_placed` to `RustCliAllocBudget M`
over `A.repAlloc` and `A.atState lim st s`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError PreKeySignalMessage SessionRecord)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p1LoadedRecordAt p2CoroScratchTailAt p2MsgFieldsAt)
open CryptoVerification.E2E (PEParams PreKeyMessageFields)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal PreKeyMsgGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SignalMessageGhost optBoxU8At protocolAddressAt speAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ dpFutDoneAt pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit PathAEntryWords cliIdInv_opened_peer cliIdOwnInv_opened cliKitStk cliKpkInvFull_opened cliPkInv_opened cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAt cliPollStoresKitsAt_entails_storesAt cliSessInv_opened_scopeKit cliSpkInv_opened closStackUnusedP1OkAt coroCopyAt_eq_head3_tail11 coroCopyTail11At coroUnusedP1At coro_unused_split_p2v1 dpClosSubStack mkPathAHdr p2MsgFields_reassemble_slices_ext p2_coro_err_fold p2_stack_err_fold pathAMsgRemInnerAtExt pathAMsgRemInnerAt_dup_kyberPtr_ext preKeyMsgAt_eq_base_idKey_sep preKeyMsgAt_unpack_pathA_ext preKeyMsgRemBaseIdKeyAt preKeyMsgRemBaseIdKeyAt_eq_ver_sep preKeyMsgRemMatchedAt processPrekeyInnerInitAt_eq_330_388_rem23 processPrekeyInnerRem23At signalMessageRestVerAt sp550P2V1RemAt spMidGapsAt stack_unused_split_p2v1 stageP2PostP1At storesAt_entails_cliPollStoresKitsAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)

abbrev stageP2PreAtPlaced :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2PreAtPlaced

abbrev p2ErrFrameAtPlaced :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2ErrFrameAtPlaced

/-- Placed spatial frame preserved untouched across `stageP2_v1_kits` on Path A, parameterized
by representation allocator `A_r : RustAlloc` and budget-threaded poll ghost `y`. -/
def pathAInnerFramePlaced {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced A_r y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
  dirAt A_r (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 0x280#64) 24 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗ memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x782#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x279#64) 39 ∗
  memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗
  signalMessageRestVerAt A_r y.g.msgG.msg y.g.msgA i ∗
  pathAMsgRemInnerAtExt A_r y.g.msgG y.g.msgA m i ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  tokenInitPlacedAt

abbrev pathAInnerFramePlacedExt := @pathAInnerFramePlaced

/-! ## 1. Representation-Invariance Bridges (`A.atState lim st s` ↔ `A.repAlloc`) -/

theorem signalMessageRestVerAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : SignalMessageGhost) (a : BitVec 64) (i : SignalMessage) :
    signalMessageRestVerAt (A.atState lim st s) g a i =
      signalMessageRestVerAt A.repAlloc g a i := by
  dsimp only [signalMessageRestVerAt, optBoxU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
  cases i.addresses <;> rfl

theorem preKeyMsgAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : PreKeyMsgGhost) (a : BitVec 64) (pm : PreKeySignalMessage) :
    preKeyMsgAt (A.atState lim st s) g a pm = preKeyMsgAt A.repAlloc g a pm := by
  dsimp only [preKeyMsgAt, CryptoVerification.LibsignalTripleRatchetRepr.signalMessageAt,
    CryptoVerification.LibsignalTripleRatchetRepr.optBoxU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
  cases pm.message.addresses <;> cases pm.kyberPayload <;> rfl

theorem preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : PreKeyMsgGhost) (a : BitVec 64) (pm : PreKeySignalMessage) :
    preKeyMsgRemBaseIdKeyAt (A.atState lim st s) g a pm =
      preKeyMsgRemBaseIdKeyAt A.repAlloc g a pm := by
  rw [preKeyMsgRemBaseIdKeyAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  dsimp only [preKeyMsgRemMatchedAt, LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
  cases pm.kyberPayload <;> rfl

theorem pathAInnerFramePlaced_atState_eq_repAlloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (st : M.σ) (s : State)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced (A.atState lim st s) y m i rngPtr sp =
      pathAInnerFramePlaced A.repAlloc y m i rngPtr sp := by
  unfold pathAInnerFramePlaced
  rw [signalMessageRestVerAt_atState_eq_repAlloc A lim st s y.g.msgG.msg y.g.msgA i]
  rfl

theorem speOwnedAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (k : CryptoVerification.SignalSession.Cli.RunDrop.SpeOwned) :
    CryptoVerification.SignalSession.Cli.RunDrop.speOwnedAt (A.atState lim st s) a k = CryptoVerification.SignalSession.Cli.RunDrop.speOwnedAt A.repAlloc a k := by
  cases k with
  | proto fnName e =>
    dsimp only [CryptoVerification.SignalSession.Cli.RunDrop.speOwnedAt, speAt, LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]
    cases e with
    | invalidMessage t rsn => cases rsn <;> rfl
    | _ => rfl
  | sessionNotFound addr op => rfl
  | untrustedIdentity addr => rfl
  | badKemKeyType => rfl
  | badKemKeyLength => rfl
  | plain i h => rfl
  | withString i h => rfl

theorem decResAt_err_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (out : BitVec 64) (err : ApiError AddrVal Unit) :
    decResAt (A.atState lim st s) out (.error err) = decResAt A.repAlloc out (.error err) := by
  dsimp only [decResAt]
  exact congrArg sepExists (funext fun k => speOwnedAt_atState_eq_repAlloc A lim st s out k)

/-! ## 2. `kyberPtr ≠ 0` Pure-Fact Duplication Helpers -/

private theorem dup_pure_sepConj_right {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left {φ : Prop} {P Q : SepProp}
    (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFramePlaced`. -/
theorem pathAInnerFrame_dup_kyberPtr_placed {M : AllocCostModel} {A_b : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced A_r y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFramePlaced A_r y m i rngPtr sp := by
  unfold pathAInnerFramePlaced
  repeat (first
    | exact dup_pure_sepConj_left (pathAMsgRemInnerAt_dup_kyberPtr_ext A_r y.g.msgG y.g.msgA m i)
    | refine dup_pure_sepConj_right ?_)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` to the front of
`stageP2PreAtPlaced A_s... (pathAInnerFramePlaced A_r...)`. -/
theorem stageP2PreAt_dup_kyberPtr_placed {M : AllocCostModel} {A_b : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    {A_s A_r : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A_s 0#64}
    {kpkKit : KyberPreKeyStoreSpec A_s 0#64}
    {pkKit : PreKeyStoreSpec A_s 0#64}
    {ikit : IdentityStoreSpec A_s 0#64}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState) :
    stageP2PreAtPlaced A_s spkKit kpkKit pkKit ikit
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced A_s spkKit kpkKit pkKit ikit
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) := by
  unfold stageP2PreAtPlaced CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2PreAtPlaced
  repeat (first
    | exact pathAInnerFrame_dup_kyberPtr_placed A_r y m i rngPtr sp
    | exact dup_pure_sepConj_left (pathAInnerFrame_dup_kyberPtr_placed A_r y m i rngPtr sp)
    | refine dup_pure_sepConj_right ?_)

/-! ## 3. Placed Path A Entry Spatial Unpack (`+0x0868`) -/

/-- `RustAlloc`-polymorphic Stage P2 Path A entry spatial unpack into `stageP2PreAtPlaced A_s`. -/
theorem stageP2_entry_unpack_pathA_placed_ext {W : PEParams}
    {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_p1 Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement]
    (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdecOk : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → CryptoVerification.SignalSession.Cli.Slots.scopeIn r') :
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope_p1 A_s y.fut none ∗
    preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗
    protocolAddressAt A_s y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt A_s y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    tokenInitPlacedAt ∗
    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜∀ id : BitVec 32, m.opkId = some id → w.opkWord = id⌝ ∗
        stageP2PreAtPlaced A_s
          (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFramePlaced A_s y m i rngPtr sp) := by
  rw [hmsg]
  dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : CryptoVerification.E2E.Pqxdh.ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) =
      CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A_s y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt A_s y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ A_s.pool ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      tokenInitPlacedAt ∗ CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_ext A_s y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  have hdecOk' : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdecOk
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A_s) 0#64
    (cliKitStk B) y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdecOk')
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdecOk' opkWord)
    (cliSpkInv_opened hdecOk' m.spkId)
    (cliKpkInvFull_opened hdecOk' m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
    (Entails.pure_right hopkWord ?_)
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, stageP2PreAtPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2PreAtPlaced,
      pathAInnerFramePlaced]
    rw [hdrEq]
    sep_ac_rfl)

/-- Budget-threaded placed entry spatial unpack from `StageP2PathACliPlacedStmt`'s precondition
into `stageP2PreAtPlaced (A.atState lim st_b s1)` and `pathAInnerFramePlaced A.repAlloc`. -/
theorem stageP2_entry_unpack_pathA_placed {W : PEParams}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_p1 Scope : SessionRecord (List (BitVec 8)) → Prop}
    {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdecOk : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → CryptoVerification.SignalSession.Cli.Slots.scopeIn r') :
    let A_s : RustAlloc := A.atState lim st_b s1
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope_p1 A.repAlloc y.fut none ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    LsTokenInit ∗
    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜∀ id : BitVec 32, m.opkId = some id → w.opkWord = id⌝ ∗
        stageP2PreAtPlaced A_s
          (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) := by
  dsimp only
  have hp1 : p1LoadedRecordAt Scope_p1 A.repAlloc y.fut none =
      p1LoadedRecordAt Scope_p1 (A.atState lim st_b s1) y.fut none := rfl
  have hpm_eq : preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg =
      preKeyMsgAt (A.atState lim st_b s1) y.g.msgG y.g.msgA y.g.msg :=
    (preKeyMsgAt_atState_eq_repAlloc A lim st_b s1 y.g.msgG y.g.msgA y.g.msg).symm
  have hinner := pathAInnerFramePlaced_atState_eq_repAlloc st_b s1 y m i rngPtr sp
  rw [hp1, hpm_eq]
  refine Entails.trans
    (stageP2_entry_unpack_pathA_placed_ext (A.atState lim st_b s1)
      y m i s0 sp fp rngPtr v_a8 v_b8 v_d0 hmsg hfp hdecOk hFok hScope) ?_
  refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
  rw [hinner]
  exact Entails.refl _

/-! ## 4. Placed Stage P2 Error-Exit Spatial Fold -/

set_option maxHeartbeats 800000 in
/-- `RustAlloc`-polymorphic Stage P2 error-exit spatial fold. -/
theorem p2ErrFrame_fold_pathA_placed_ext {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt A_s y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced A_s s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A_s y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt A_s y.out (.error err) ∗
      storesAt A_s y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      A_s.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  rw [hmsg]
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
  have hmsgFold :
      p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A_s y.g.msgG y.g.msgA m i ⊢
      preKeyMsgAt A_s y.g.msgG y.g.msgA (pmOfE m i) := by
    refine Entails.trans (p2MsgFields_reassemble_slices_ext A_s y.g.msgG y.g.msgA m i w.opkWord hopk) ?_
    rw [preKeyMsgAt_eq_base_idKey_sep]
    exact Entails.of_eq (by sep_ac_rfl)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := p2_stack_err_fold sp fp s0 hfp
  have hany : coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt ∗ anyHeap ⊢ anyHeap :=
    entails_anyHeap _
  dsimp only [p2ErrFrameAtPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2ErrFrameAtPlaced,
    pathAInnerFramePlaced]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0xe0#64) 368 ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      memRegion (y.fut + 0x298#64) 20 ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗
      memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x80#64) 88 ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
      memRegion (sp + 0x3b0#64) 48 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      spMidGapsAt sp ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    decResAt A_s y.out (.error err) ∗
    cliPollStoresKitsAt A_s 0#64 y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer
      w.opkWord m.spkId m.kpkId (pmOfE m i).baseKey (cliKitStk B) y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A_s y.g.msgG y.g.msgA m i) ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗
    protocolAddressAt A_s y.g.me y.g.meA ∗
    CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
    A_s.pool ∗
    stackAt sp (dpClosSubStack B) ∗
    (coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt ∗ anyHeap)
    by exact Entails.of_eq (by dsimp only [cliPollStoresKitsAt]; sep_ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right
    (sepConj_mono hstores (sepConj_mono hmsgFold
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hany)))))))))

/-- Budget-threaded Stage P2 error-exit spatial fold into `StageP2PathAErrPlaced`'s postcondition
when `decResAt` is expressed at `A.repAlloc`. -/
theorem p2ErrFrame_fold_pathA_placed_rep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {stf : M.σ} {sf : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    let A_s : RustAlloc := A.atState lim stf sf
    (decResAt A.repAlloc y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced A_s s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      A.pool lim stf sf ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  dsimp only
  have hdec := decResAt_err_atState_eq_repAlloc A lim stf sf y.out err
  have hinner := pathAInnerFramePlaced_atState_eq_repAlloc stf sf y m i rngPtr sp
  have hpm := preKeyMsgAt_atState_eq_repAlloc A lim stf sf y.g.msgG y.g.msgA y.g.msg
  rw [← hdec, ← hinner]
  refine Entails.trans
    (p2ErrFrame_fold_pathA_placed_ext (A.atState lim stf sf) y m i w s0 sp fp rngPtr err
      hmsg hfp hopk) ?_
  rw [hdec, hpm]
  exact Entails.refl _

/-- Budget-threaded Stage P2 error-exit spatial fold into `StageP2PathAErrPlaced`'s postcondition
when `decResAt` on the LHS is at `A.atState lim stf sf`. -/
theorem p2ErrFrame_fold_pathA_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {stf : M.σ} {sf : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    let A_s : RustAlloc := A.atState lim stf sf
    (decResAt A_s y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced A_s s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      A.pool lim stf sf ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  dsimp only
  rw [decResAt_err_atState_eq_repAlloc A lim stf sf y.out err]
  exact p2ErrFrame_fold_pathA_placed_rep y m i w s0 sp fp rngPtr err hmsg hfp hopk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
