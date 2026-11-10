/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Path B Stage P2 Spatial Entry Unpack

Generalizes `matchedInnerFramePlaced` and `matched_entry_unpack_placed` to `RustCliAllocBudget M`
over `A.repAlloc` and `A.atState lim st s`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  matchedInnerFramePlaced matched_entry_unpack_placed
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

/-- Placed inner coroutine/stack/message frame untouched by `stageP2_matched_ok_framed_placed`,
parameterized by representation allocator `A : RustAlloc` and budget-threaded poll ghost `y`. -/
def matchedInnerFramePlaced {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (rngPtr sp : BitVec 64) : SepProp :=
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
  cells (y.fut + 0x398#64) 2 ∗
  memRegion (y.fut + 0x280#64) 24 ∗
  memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗
  memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗
  memRegion (y.fut + 0x3a8#64) 80 ∗
  memRegion (y.fut + 0x488#64) 8 ∗
  memRegion (y.fut + 0x4b0#64) 65 ∗
  memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x4f8#64) 736 ∗
  (sp ↦₆₄ 0#64) ∗
  memRegion (sp + 0x8#64) 120 ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗
  memRegion (sp + 0x270#64) 48 ∗
  memRegion (sp + 0x2b0#64) 36 ∗
  memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗
  memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗
  memRegion (sp + 0x402#64) 70 ∗
  memRegion (sp + 0x448#64) 240 ∗
  memRegion (sp + 0x538#64) 24 ∗
  memRegion (sp + 0x550#64) 976 ∗
  memRegion (sp + 0x926#64) 10 ∗
  memRegion (sp + 0x930#64) 96 ∗
  memRegion (sp + 0x990#64) 256 ∗
  memRegion (sp + 0xac0#64) 296 ∗
  memRegion (sp + 0xbe8#64) 136 ∗
  signalMessageRestVerAt A y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  preKeyMsgRemMatchedAt A y.g.msgG y.g.msgA y.g.msg ∗
  protocolAddressAt A y.g.peer y.g.peerA ∗
  protocolAddressAt A y.g.me y.g.meA ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  tokenInitPlacedAt

/-- Budget-threaded placed entry spatial unpack into `stageP2MatchedPrePlaced (A.atState lim st s)`
and `matchedInnerFramePlaced A.repAlloc`. -/
theorem matched_entry_unpack_placed {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st : M.σ) (sess : Session (List (BitVec 8))) (s0 s : State)
    (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PostP1At (A.atState lim st s) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A.repAlloc y.fut (some ⟨some sess⟩) ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    tokenInitPlacedAt ∗
    lsLogOff ∗
    stackAt sp rootStack ⊢
      ∃∗ g : RecordGhost, ∃∗ w : MatchedEntryWords,
        stageP2MatchedPrePlaced (A.atState lim st s) s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
          y.g.peerA (y.g.msgA + 0xc8#64)
          w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
          w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
          w.u_2a8 (v_b8.extractLsb' 0 32)
          y.g.msg.messageVersion y.g.msg.message.messageVersion
          w.b_4f1 0#8 0#8 0#8 w.b_3ac
          y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩
          (matchedInnerFramePlaced A.repAlloc y rngPtr sp) := by
  have hp1 : p1LoadedRecordAt Scope A.repAlloc y.fut (some ⟨some sess⟩) =
      p1LoadedRecordAt Scope (A.atState lim st s) y.fut (some ⟨some sess⟩) := rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hp1))) ?_
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun _ => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  dsimp only [stageP2PostP1At, RustCliAllocBudget.atState]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23,
      preKeyMsgAt_eq_base_idKey_sep, signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  have h250 : memRegion (y.fut + 0x250#64) 48 = cells (y.fut + 0x250#64) 6 :=
    ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)
  rw [h250]
  refine Entails.trans (show _ ⊢
      coroUnusedP1At y.fut ∗
      (((sp + 0xb8#64) ↦₆₄ v_b8) ∗ memRegion (sp + 0x3e0#64) 368 ∗ closStackUnusedP1OkAt sp) ∗
      (sessionRecordAt (A.atState lim st s) (y.fut + 0xe0#64) g ⟨some sess⟩ ∗
        decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗
        ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
        ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
        coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        cells (y.fut + 0x250#64) 6 ∗
        ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
        ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗
        ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
          y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
          (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
        processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
          y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
          (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
        ((y.fut + 0x390#64) ↦₈ 0#8) ∗
        cells (y.fut + 0x398#64) 2 ∗
        ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
        (sp ↦₆₄ 0#64) ∗
        ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
        ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        memRegion y.out 48 ∗
        A.pool lim st s ∗
        ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
        signalMessageRestVerAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
        preKeyMsgRemMatchedAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        tokenInitPlacedAt ∗
        lsLogOff ∗
        stackAt sp rootStack) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (coro_unused_split_matched y.fut)
    (sepConj_mono_left (stack_unused_split_matched sp v_b8))) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u298 => Entails.sepExists_elim fun u2a0 =>
    Entails.sepExists_elim fun u2a8 => Entails.sepExists_elim fun b4f1 => ?_
  rw [sepConj_comm _ (∃∗ u_80 : BitVec 64, _), ← sepConj_assoc]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u3a0 =>
    Entails.sepExists_elim fun b3ac => Entails.sepExists_elim fun u3b0 =>
    Entails.sepExists_elim fun u3b8 => Entails.sepExists_elim fun u3c0 =>
    Entails.sepExists_elim fun u3c8 => Entails.sepExists_elim fun u3d0 =>
    Entails.sepExists_elim fun u3d8 => ?_
  exact Entails.sepExists_right g (Entails.sepExists_right
    ⟨u80, u88, u90, u298, u2a0, u3a0, u3b0, u3b8, u3c0, u3c8, u3d0, u3d8, u2a8, b4f1, b3ac⟩
    (by
      dsimp only [stageP2MatchedPrePlaced, matchedInnerFramePlaced, RustCliAllocBudget.atState]
      sep_frame))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
