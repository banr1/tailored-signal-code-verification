/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeySubPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlaced
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433

/-!
# Budget-Threaded Segment 4 (`ConsumeMsgKey`) Seam on CLI Block `433`

Defines pointer-free Segment-4 allocation-event envelopes (`CmkStepEnv`, `CmkSeg4Env`,
`s4DefaultEnv`) and proves `consumeMsgKey_433_placed_ok_ofEnv` and `consumeMsgKey_433_placed_ok`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open scoped LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (
  ChainKey Crypto Mut PublicKey RatchetState SignalMessage TripleRatchet macLength
)
open CryptoVerification (
  LibsignalPlacement lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (
  RustAlloc vecHeader vecU8 vecU8At
)
open CryptoVerification.LibsignalSession (ConsumeMessageKeyGhost cmkStack)
open CryptoVerification.LibsignalSessionRepr (
  chainKeyBytes consumeMessageKeyResultAt msgTypeByte ratchetAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SignalMessageGhost boxU8At optBoxU8At protocolAddressAt sessionStateAt signalMessageAt
  uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost addrDisplayStack
  logOff trAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkLib_eq_434 blkPC_434 blkPl_434 segConsumeMsgKeyPC_at
  tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  extractLsb0_8_append56 mr_cut mr_cut_add sp_fp_eq stackAt_sub
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt (cliTryDecryptCommonHeapPlaced)
open CryptoVerification.Cli.SpqrV1.M4 (
  consumeMessageKey_senderChain empty_vecU8_intro realign_416_436 split_chainKeyBytes
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustAllocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (tryDecryptOnPanic)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (steps_of_sepWP_placed_state)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState trAt_atState
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (lsLogOff_eq_logOff_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeySubPlacedBudget (
  consumeMsgKey_cmk_err_433_placed consumeMsgKey_cmk_ok_433_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailStatePlaced PqRecvStatePlaced S4SeamPlaced
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkEnv CmkLoopAdvanceEvs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  cmkRawSpecPlaced steps_call_out_placed_cro
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  addrDisplayEnvSpec addrDisplaySpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel

private theorem ratchetAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc := rfl

private theorem consumeMessageKeyResultAt_atState_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    consumeMessageKeyResultAt (A.atState lim st s) = consumeMessageKeyResultAt A.repAlloc := rfl

private def trNonRatchetAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
  ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

private theorem trAt_split_ratchet (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      ⌜∀ sc, tr.ratchet.senderChain = some sc →
        clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
      ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
      trNonRatchetAt A sp trG tr := by
  unfold trAt trNonRatchetAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 176#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 200#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 232#64 = 288#64 by rfl]

private def signalMessageNonTheirAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 24#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 40#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 88#64) g.addrPtr m.addresses ∗
    ((a + 104#64) ↦₃₂ m.counter) ∗ ((a + 108#64) ↦₃₂ m.previousCounter) ∗
    ((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7

private theorem signalMessageAt_split_their (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
      signalMessageNonTheirAt A g a m := by
  unfold signalMessageAt signalMessageNonTheirAt
  sep_ac_rfl

/-! ## 1. Pointer-Free Segment-4 Allocation Envelopes -/

/-- Pointer-free projection of `FetchBudget.CmkEnv` determined by `(msgCounter, senderRatchetKey,
trG.ratchet.chains[ci]?.map (·.mkCap), r, ck)`. -/
def CmkStepEnv (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) (evs : List AllocEvent) : Prop :=
  if msgCounter < ck.index then
    FreeOnlyEvs evs
  else if (msgCounter - ck.index).toNat ≤ r.maxForwardJumps then
    match r.findReceiverChainIndex senderRatchetKey with
    | none =>
      if ck.index < msgCounter then
        evs = [] ∨ evs = rustAllocEvents 32 1
      else
        evs = []
    | some ci =>
      let cap0 := (trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64
      let len0 := (r.receiverChains[ci]?.map (·.messageKeys.length)).getD 0
      CmkLoopAdvanceEvs (msgCounter - ck.index).toNat cap0 len0
        (msgCounter == BitVec.allOnes 32) evs
  else
    evs = rustAllocEvents 36 1

example (pk : PublicKey) (trG : TrGhost) (r : RatchetState) (ck : ChainKey) :
    CmkStepEnv 0#32 pk trG r { ck with index := 1#32 } [] := by
  unfold CmkStepEnv
  have hlt : (0#32 : BitVec 32) < 1#32 := by decide
  simp only [hlt, ↓reduceIte]
  exact FreeOnlyEvs.nil

theorem cmkEnv_eq_cmkStepEnv (cmkX : ConsumeMessageKeyGhost) (trG : TrGhost)
    (hG : cmkX.G = trG.ratchet) :
    CmkEnv cmkX = CmkStepEnv cmkX.counter cmkX.their trG cmkX.st cmkX.ck := by
  funext evs
  unfold CmkEnv CmkStepEnv
  cases cmkX.st.findReceiverChainIndex cmkX.their <;> simp only [hG]

/-- Segment-4 (`ConsumeMsgKey`) allocation-event envelope parameterized by `fmtWriteEnv`. -/
def CmkSeg4Env (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) : List AllocEvent → Prop :=
  SeqEnv fmtWriteEnv
    (SeqEnv (CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck) FreeOnlyEvs)

/-- Default Segment-4 allocation-event envelope at `FmtWriteEnv`. -/
abbrev s4DefaultEnv :
    TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop :=
  CmkSeg4Env FmtWriteEnv

example (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) (hlt : x.msg.counter < ck.index) :
    s4DefaultEnv x trG tr ck [] := by
  have hfmt : FmtWriteEnv [] := rfl
  have hcmk : CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck [] := by
    unfold CmkStepEnv
    simp only [hlt, ↓reduceIte]
    exact FreeOnlyEvs.nil
  exact SeqEnv.append hfmt (SeqEnv.append hcmk FreeOnlyEvs.nil)

/-! ## 2. Budget-Threaded Segment-4 Seam Theorems -/

/-- Envelope-parametric `S4SeamPlaced` on CLI Block `433`. -/
theorem consumeMsgKey_433_placed_ok_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (fmtWriteEnv : List AllocEvent → Prop)
    (H : String → Option (State → State))
    (haddrDisplay : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 215)
      (withLsCodeRoLoaded lsmpl (addrDisplayEnvSpec M A lim fmtWriteEnv)))
    (hcmk_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced C.F A lim CmkEnv)))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S4SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S (CmkSeg4Env fmtWriteEnv) := by
  intro x st trG tr st1 ck draws R s0 s hfits hS4 hL
  rcases hS4 with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hfp, htrace, hcl, hvregs⟩,
    hx12, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hmem⟩
  unfold segConsumeMsgKeyPC_at at hpc
  rw [show (0x3e4#64 : BitVec 64) = 996#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hfp
  rw [hsp29_eq] at hfp
  clear hsp29_eq
  unfold cliTryDecryptCommonHeapPlaced at hmem
  rw [lsLogOff_eq_logOff_placed] at hmem
  simp only [sessionStateAt_atState, trAt_atState, protocolAddressAt_atState,
    signalMessageAt_atState, RustCliAllocBudget.atState_pool] at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx12 hx20 hx23 hx25 hfp hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hdrop, htake, hfull⟩ := split_chainKeyBytes ck
  let Out : State → Prop := fun s' =>
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      (∃ evs trG', CmkSeg4Env fmtWriteEnv x trG tr ck evs ∧
          PqRecvStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
      (s'.status = .Panicked ∧
        (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))
    | (.error e, r2) =>
      (e ≠ .panic ∧ ∃ evs trG', CmkSeg4Env fmtWriteEnv x trG tr ck evs ∧
          ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
            x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
      (s'.status = .Panicked ∧
        (e = .panic ∧ s0.trace <+: s'.trace) ∧
        (s'.mem ⊨ anyHeap ∗ R))
  have hOut_split : ∀ (prog : Program) (sm : State),
      (∃ s', Steps prog sm s' ∧ Out s') →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((∃ evs trG', CmkSeg4Env fmtWriteEnv x trG tr ck evs ∧
              PqRecvStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
                x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps prog sm s' ∧
          ((e ≠ .panic ∧ ∃ evs trG', CmkSeg4Env fmtWriteEnv x trG tr ck evs ∧
              ErrTailStatePlaced (blkPl_434).base A lim (M.stepEvents evs st) ctl
                x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (e = .panic ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
    intro prog sm ⟨s', hst, hout⟩
    dsimp only [Out] at hout
    split at hout <;> exact ⟨s', hst, hout⟩
  apply hOut_split
  have hmem0 : s.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 368 ∗
       ((sp + 688#64) ↦₆₄ (w6 ++ w5)) ∗
       ((sp + 696#64) ↦₆₄ (w8 ++ w7)) ∗
       ((sp + 704#64) ↦₆₄ (w1 ++ w0)) ∗
       ((sp + 712#64) ↦₆₄ (w3 ++ w2)) ∗
       ((sp + 720#64) ↦₃₂ w4) ∗
       memRegion (sp + 724#64) 684 ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
       cliTapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R := by
    have hd := hdrop (sp + 688#64)
    have ht := htake (sp + 704#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hd ht
    rw [hd, ht] at hmem
    simp only [sepConj_assoc] at hmem
    simp only [sepConj_assoc]
    exact hmem
  refine steps_of_sepWP_placed_state hmem0 hL hcl
    (mid := lsmpl.base 215)
    (RegMid := fun sm1 =>
      sm1.readReg64 .x1 = sp + 1024#64 ∧
      sm1.readReg64 .x19 = x.ret ∧
      sm1.readReg64 .x20 = sp + 320#64 ∧
      sm1.readReg64 .x21 = x.ss ∧
      sm1.readReg64 .x22 = x.msgA ∧
      sm1.readReg64 .x23 = sp + 1280#64 ∧
      (sm1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
      sm1.readReg64 .x25 = sp + 400#64 ∧
      sm1.readReg64 .fp = sp + 1408#64 ∧
      sm1.readReg64 .lr = (blkPl_434).base + 1092#64 ∧
      sm1.sp = sp ∧ sm1.spAligned = true ∧ sm1.trace = s0.trace ∧
      calleeSavedVRegs sm1 = calleeSavedVRegs s0)
    (P_mid := fun sm1 =>
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion sp 32 ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 416 ∗
      ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
      memRegion (sp + 772#64) 204 ∗
      vecU8 A.repAlloc (sp + 976#64) [] ∗
      memRegion (sp + 1000#64) 24 ∗
      ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
      memRegion (sp + 1032#64) 40 ∗
      memRegion (sp + 1072#64) 336 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool lim st sm1) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 96 272 368 416#64,
        mr_cut sp 416 4 268 272 420#64,
        mr_cut sp 420 8 260 268 428#64,
        mr_cut sp 428 8 252 260 436#64,
        mr_cut sp 724 12 672 684 736#64,
        mr_cut sp 736 8 664 672 744#64,
        mr_cut sp 744 8 656 664 752#64,
        mr_cut sp 752 8 648 656 760#64,
        mr_cut sp 760 8 640 648 768#64,
        mr_cut sp 768 4 636 640 772#64,
        mr_cut sp 772 204 432 636 976#64,
        mr_cut sp 976 8 424 432 984#64,
        mr_cut sp 984 8 416 424 992#64,
        mr_cut sp 992 8 408 416 1000#64,
        mr_cut sp 1000 8 400 408 1008#64,
        mr_cut sp 1008 8 392 400 1016#64,
        mr_cut sp 1016 8 384 392 1024#64,
        mr_cut sp 1024 8 376 384 1032#64,
        mr_cut sp 1032 8 368 376 1040#64,
        mr_cut sp 1040 8 360 368 1048#64,
        mr_cut sp 1048 8 352 360 1056#64,
        mr_cut sp 1056 8 344 352 1064#64,
        mr_cut sp 1064 8 336 344 1072#64]
      simp only [sepConj_assoc,
        memRegion_four (sp + 416#64),
        memRegion_eight (sp + 420#64),
        memRegion_eight (sp + 428#64),
        memRegion_eight (sp + 736#64),
        memRegion_eight (sp + 744#64),
        memRegion_eight (sp + 752#64),
        memRegion_eight (sp + 760#64),
        memRegion_four (sp + 768#64),
        memRegion_eight (sp + 976#64),
        memRegion_eight (sp + 984#64),
        memRegion_eight (sp + 992#64),
        memRegion_eight (sp + 1000#64),
        memRegion_eight (sp + 1008#64),
        memRegion_eight (sp + 1016#64),
        memRegion_eight (sp + 1024#64),
        memRegion_eight (sp + 1032#64),
        memRegion_eight (sp + 1040#64),
        memRegion_eight (sp + 1048#64),
        memRegion_eight (sp + 1056#64),
        memRegion_eight (sp + 1064#64)]
    wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 (mid := lsmpl.base 215)
    intro _m_strip
    wp_steps
    refine SepWP.focus_weaken (realign_416_436 sp w4 w5 w6 w7 w8) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    have hck_fold :
        ((sp + 736#64) ↦₆₄ (w1 ++ w0)) ∗ ((sp + 744#64) ↦₆₄ (w3 ++ w2)) ∗
        ((sp + 752#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 760#64) ↦₆₄ (w7 ++ w6)) ∗
        ((sp + 768#64) ↦₃₂ w8) ⊢
        ((sp + 736#64) ↦ₛ chainKeyBytes ck) := by
      have hf := (hfull (sp + 736#64)).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hf ⊢
      rw [hf]
      exact Entails.refl _
    refine SepWP.focus_weaken hck_fold (by sep_focus) ?_
    have hv_empty := empty_vecU8_intro A.repAlloc (sp + 976#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv_empty
    refine SepWP.focus_weaken hv_empty (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 432#64) w8) (by sep_focus) ?_
    refine SepWP.focus_weaken (pointsTo32_entails_memRegion (sp + 720#64) w4) (by sep_focus) ?_
    have hm320 : memRegion (sp + 320#64) 416 =
        memRegion (sp + 320#64) 96 ∗ (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗
        (memRegion (sp + 432#64) 4 ∗ (memRegion (sp + 436#64) 252 ∗ (memRegion (sp + 688#64) 8 ∗
        (memRegion (sp + 696#64) 8 ∗ (memRegion (sp + 704#64) 8 ∗ (memRegion (sp + 712#64) 8 ∗
        (memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 12))))))))) := by
      rw [mr_cut_add sp 320 96 320 (by decide),
        mr_cut_add sp 416 8 312 (by decide),
        mr_cut_add sp 424 8 304 (by decide),
        mr_cut_add sp 432 4 300 (by decide),
        mr_cut_add sp 436 252 48 (by decide),
        mr_cut_add sp 688 8 40 (by decide),
        mr_cut_add sp 696 8 32 (by decide),
        mr_cut_add sp 704 8 24 (by decide),
        mr_cut_add sp 712 8 16 (by decide),
        mr_cut_add sp 720 4 12 (by decide)]
    have hm1000 : memRegion (sp + 1000#64) 24 =
        memRegion (sp + 1000#64) 8 ∗ (memRegion (sp + 1008#64) 8 ∗ memRegion (sp + 1016#64) 8) := by
      rw [mr_cut_add sp 1000 8 16 (by decide), mr_cut_add sp 1008 8 8 (by decide)]
    have hm1032 : memRegion (sp + 1032#64) 40 =
        memRegion (sp + 1032#64) 8 ∗ (memRegion (sp + 1040#64) 8 ∗ (memRegion (sp + 1048#64) 8 ∗
        (memRegion (sp + 1056#64) 8 ∗ memRegion (sp + 1064#64) 8))) := by
      rw [mr_cut_add sp 1032 8 32 (by decide),
        mr_cut_add sp 1040 8 24 (by decide),
        mr_cut_add sp 1048 8 16 (by decide),
        mr_cut_add sp 1056 8 8 (by decide)]
    rw [hm320, hm1000, hm1032]
    wp_done
  · intro sm1 hpc1 hrun1 hcl1 hL1
      ⟨hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfp1, hlr1, hsp1, hsp_al1, htr1, hvregs1⟩
      hm1
    have hm1032_split : memRegion (sp + 1032#64) 40 =
        (∃∗ vt : BitVec 64, (sp + 1032#64) ↦₆₄ vt) ∗ memRegion (sp + 1040#64) 32 := by
      rw [mr_cut_add sp 1032 8 32 (by decide), memRegion_eight (sp + 1032#64)]
    rw [hm1032_split] at hm1
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hm1
    rcases hm1 with ⟨vt, hm1⟩
    have hfits_disp : FitsEnv M lim st fmtWriteEnv := hfits.seq_left
    have hpre_disp : sm1.mem ⊨
        (addrDisplayEnvSpec M A lim fmtWriteEnv).pre
          (sp + 1024#64, sp + 976#64, vt, ([] : List (BitVec 8)), st) sm1 ∗
        ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          trAt A.repAlloc (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗
          memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 416 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 204 ∗
          memRegion (sp + 1000#64) 24 ∗
          memRegion (sp + 1040#64) 32 ∗
          memRegion (sp + 1072#64) 336 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - addrDisplayStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ R) := by
      dsimp only [addrDisplayEnvSpec]
      rw [hsp1]
      rw [stackAt_sub sp tryDecryptSubStack addrDisplayStack] at hm1
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx1_1, hfits_disp⟩, ?_⟩
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm1 ⊢
      arm64_sep_close
    refine steps_call_out_placed_cro (sp + 1024#64, sp + 976#64, vt, ([] : List (BitVec 8)), st)
      haddrDisplay hpc1 hrun1 hsp_al1 hlr1 hcl1 hL1 hpre_disp ?_ ?_
    · intro sf _ hpost
      dsimp only [addrDisplayEnvSpec] at hpost
      rw [sepConj_assoc] at hpost
      exact (not_satisfies_false_sepConj hpost).elim
    · intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      rcases hcsf1 with ⟨hx19_cs1, hx20_cs1, hx21_cs1, hx22_cs1, hx23_cs1, hx24_cs1, hx25_cs1, _, _, _, hfp_cs1, hvregs_cs1⟩
      have hx19_f1 : sf1.readReg64 .x19 = x.ret := hx19_cs1.trans hx19_1
      have hx20_f1 : sf1.readReg64 .x20 = sp + 320#64 := hx20_cs1.trans hx20_1
      have hx21_f1 : sf1.readReg64 .x21 = x.ss := hx21_cs1.trans hx21_1
      have hx22_f1 : sf1.readReg64 .x22 = x.msgA := hx22_cs1.trans hx22_1
      have hx23_f1 : sf1.readReg64 .x23 = sp + 1280#64 := hx23_cs1.trans hx23_1
      have hx24_f1 : (sf1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
        rw [hx24_cs1]; exact hx24_1
      have hx25_f1 : sf1.readReg64 .x25 = sp + 400#64 := hx25_cs1.trans hx25_1
      have hfp_f1 : sf1.readReg64 .fp = sp + 1408#64 := hfp_cs1.trans hfp1
      have hvregs_f1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := hvregs_cs1.trans hvregs1
      have hsp_f1 : sf1.sp = sp := hspf1.trans hsp1
      dsimp only [addrDisplayEnvSpec] at hpost1
      rw [hsp1] at hpost1
      simp only [vecU8, vecU8At, vecHeader, RustCliAllocBudget.repAlloc_live,
        sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs1, dispBs, dispCap, dispPtr, hpost1⟩
      rw [satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨_hw0_f1, htr_f1, hevs1⟩, hpost1⟩
      have htr_f1' : sf1.trace = s0.trace := htr_f1.trans htr1
      simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨hdisp1, hdisp2, _hdisp3⟩, hpost1⟩
      let st_a := M.stepEvents evs1 st
      have hpost1' : sf1.mem ⊨
          (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           trAt A.repAlloc (sp + 56#64) trG tr ∗
           (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
             (dispPtr ↦ₛ dispBs) ∗
             memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
           ((sp + 976#64) ↦₆₄ dispCap) ∗
           ((sp + 984#64) ↦₆₄ dispPtr) ∗
           ((sp + 992#64) ↦₆₄ BitVec.ofNat 64 dispBs.length) ∗
           ((sp + 1024#64) ↦₆₄ (sp + 976#64)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 32 ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
           memRegion (sp + 44#64) 4 ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 416 ∗
           ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
           memRegion (sp + 772#64) 204 ∗
           memRegion (sp + 1000#64) 24 ∗
           memRegion (sp + 1032#64) 40 ∗
           memRegion (sp + 1072#64) 336 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_a sf1) ∗ R := by
        rw [hm1032_split, stackAt_sub sp tryDecryptSubStack addrDisplayStack]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
          sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1 ⊢
        refine ⟨vt, ?_⟩
        arm64_sep_close
      let msgW : BitVec 32 := (sf1.readReg64 .x24).setWidth 32
      have hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType := by
        have h8 : msgW.setWidth 8 = (sf1.readReg64 .x24).setWidth 8 :=
          BitVec.setWidth_setWidth_of_le (sf1.readReg64 .x24) (by decide)
        exact h8.trans hx24_f1
      refine steps_of_sepWP_placed_state hpost1' hLf1 hclf1
        (mid := lsmpl.base 24)
        (RegMid := fun sm2 =>
          sm2.readReg64 .x0 = sp + 56#64 ∧
          sm2.readReg64 .x1 = x.msgA + 56#64 ∧
          sm2.readReg64 .x2 = sp + 736#64 ∧
          (sm2.readReg64 .x3).setWidth 32 = x.msg.counter ∧
          (sm2.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
          sm2.readReg64 .x8 = sp + 400#64 ∧
          sm2.readReg64 .x19 = x.ret ∧
          sm2.readReg64 .x20 = sp + 320#64 ∧
          sm2.readReg64 .x21 = x.ss ∧
          sm2.readReg64 .x22 = x.msgA ∧
          sm2.readReg64 .x23 = sp + 1280#64 ∧
          sm2.readReg64 .x25 = sp + 400#64 ∧
          sm2.readReg64 .x27 = dispPtr ∧
          sm2.readReg64 .x28 = dispCap ∧
          sm2.readReg64 .fp = sp + 1408#64 ∧
          sm2.readReg64 .lr = (blkPl_434).base + 1144#64 ∧
          sm2.sp = sp ∧ sm2.spAligned = true ∧ sm2.trace = s0.trace ∧
          calleeSavedVRegs sm2 = calleeSavedVRegs s0)
        (P_mid := fun sm2 =>
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          trAt A.repAlloc (sp + 56#64) trG tr ∗
          (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
            (dispPtr ↦ₛ dispBs) ∗
            memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 28 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          memRegion (sp + 400#64) 88 ∗
          memRegion (sp + 488#64) 248 ∗
          ((sp + 736#64) ↦ₛ chainKeyBytes ck) ∗
          memRegion (sp + 772#64) 636 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool lim st_a sm2) ?_ ?_
      · have hsp0 : memRegion sp 32 = memRegion sp 28 ∗ memRegion (sp + 28#64) 4 := by
          have hm := mr_cut_add sp 0 28 4 (by decide)
          simp only [BitVec.add_zero] at hm
          exact hm
        wp_conv_pre =>
          rw [hsp0, memRegion_four (sp + 28#64),
            mr_cut sp 320 80 336 416 400#64,
            mr_cut sp 400 88 248 336 488#64]
          simp only [sepConj_assoc]
        wp_pull_exists
        wp_steps_sync_pool (lsmpl.base 24)
        have hm772 : memRegion (sp + 772#64) 636 =
            memRegion (sp + 772#64) 204 ∗ (memRegion (sp + 976#64) 8 ∗ (memRegion (sp + 984#64) 8 ∗
            (memRegion (sp + 992#64) 8 ∗ (memRegion (sp + 1000#64) 24 ∗
            (memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 40 ∗
             memRegion (sp + 1072#64) 336)))))) := by
          rw [mr_cut_add sp 772 204 432 (by decide),
            mr_cut_add sp 976 8 424 (by decide),
            mr_cut_add sp 984 8 416 (by decide),
            mr_cut_add sp 992 8 408 (by decide),
            mr_cut_add sp 1000 24 384 (by decide),
            mr_cut_add sp 1024 8 376 (by decide),
            mr_cut_add sp 1032 40 336 (by decide)]
        rw [hm772]
        dsimp only [msgW]
        wp_done
      · intro sm2 hpc2 hrun2 hcl2 hL2
          ⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2,
           hx23_2, hx25_2, hx27_2, hx28_2, hfp2, hlr2, hsp2, hsp_al2, htr2, hvregs2⟩
          hm2
        let cmkX : ConsumeMessageKeyGhost :=
          { self := sp + 56#64
            G := trG.ratchet
            st := tr.ratchet
            their := x.msg.senderRatchetKey
            theirA := x.msgA + 56#64
            ck := ck
            ckA := sp + 736#64
            counter := x.msg.counter
            msgType := x.msgType
            ret := sp + 400#64 }
        have hcmk_model : cmkX.model C.F =
            Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
              x.msgType) tr.ratchet := rfl
        have hstack_cmk := stackAt_sub sp tryDecryptSubStack cmkStack (by decide) (by decide)
        have hfits_cmk : FitsEnv M lim st_a (CmkEnv cmkX) := by
          rw [cmkEnv_eq_cmkStepEnv cmkX trG rfl]
          exact (hfits.seq_right hevs1).seq_left
        rw [trAt_split_ratchet, signalMessageAt_split_their] at hm2
        simp only [sepConj_assoc] at hm2
        rw [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm2
        rcases hm2 with ⟨hclamp, hm2⟩
        have hpre_cmk : sm2.mem ⊨
            (cmkRawSpecPlaced C.F A lim CmkEnv).pre (cmkX, st_a) sm2 ∗
            ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
              trNonRatchetAt A.repAlloc sp trG tr ∗
              (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                (dispPtr ↦ₛ dispBs) ∗
                memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
              memRegion x.ret 48 ∗
              memRegion sp 28 ∗
              ((sp + 28#64) ↦₃₂ msgW) ∗
              ((sp + 32#64) ↦₆₄ x.locA) ∗
              ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
              memRegion (sp + 44#64) 4 ∗
              ((sp + 48#64) ↦₆₄ x.remA) ∗
              memRegion (sp + 320#64) 80 ∗
              memRegion (sp + 488#64) 248 ∗
              memRegion (sp + 772#64) 636 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              protocolAddressAt A.repAlloc x.loc x.locA ∗
              signalMessageNonTheirAt A.repAlloc x.msgG x.msgA x.msg ∗
              cliTapeAfter ctl x.cur x.rest draws ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - cmkStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [cmkRawSpecPlaced,
            CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced, cmkX]
          rw [ratchetAt_atState_eq, RustCliAllocBudget.atState_pool, hsp2,
            sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨hfits_cmk, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx8_2⟩, ?_⟩
          rw [hstack_cmk] at hm2
          simp only [sepConj_assoc] at hm2 ⊢
          arm64_sep_close
        refine steps_call_out_placed_cro (cmkX, st_a) hcmk_call
          hpc2 hrun2 hsp_al2 hlr2 hcl2 hL2 hpre_cmk ?_ ?_
        · intro sf hpan hpost
          dsimp only [cmkRawSpecPlaced] at hpost
          rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
          rcases hpost with ⟨⟨hbad, htr_sub⟩, hpost⟩
          have htr0 : s0.trace <+: sf.trace := by rw [← htr2]; exact htr_sub
          rw [← sepConj_assoc] at hpost
          have hany : sf.mem ⊨ anyHeap ∗ R :=
            Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpost
          rw [hcmk_model] at hbad
          dsimp only [Out]
          split
          · next mkg r2 hmod =>
            rw [hmod] at hbad
            cases hbad
          · next e r2 hmod =>
            rw [hmod] at hbad
            exact Or.inr ⟨hpan, ⟨Except.error.inj hbad, htr0⟩, hany⟩
        · intro sf2 hpcf2 hrunf2 hspf2 hsp_alf2 hcsf2 hclf2 hLf2 hpost2
          dsimp only [cmkRawSpecPlaced,
            CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced] at hpost2
          rw [hsp2, hcmk_model] at hpost2
          simp only [cmkX, ratchetAt_atState_eq, consumeMessageKeyResultAt_atState_eq,
            RustCliAllocBudget.atState_pool, sepConj_assoc, sepExists_sepConj_left,
            sepExists_sepConj_right, satisfies_sepExists] at hpost2
          rcases hpost2 with ⟨evs2, rG', hpost2⟩
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨hevs2_raw, hpost2⟩
          have hevs2 : CmkStepEnv x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck evs2 := by
            have hcmk_eq := cmkEnv_eq_cmkStepEnv cmkX trG rfl
            dsimp only [cmkX] at hcmk_eq
            rwa [hcmk_eq] at hevs2_raw
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨⟨hnot_panic, htr_f2⟩, hpost2⟩
          have htr_f2' : sf2.trace = s0.trace := htr_f2.trans htr2
          rw [satisfies_pure_sepConj] at hpost2
          rcases hpost2 with ⟨_, hpost2⟩
          let st_b := M.stepEvents evs2 st_a
          let r2 := (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
            x.msg.counter x.msgType) tr.ratchet).2
          let trG' : TrGhost := { trG with ratchet := rG' }
          have hclamp2 : ∀ sc, r2.senderChain = some sc →
              clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
            intro sc hsc
            rw [consumeMessageKey_senderChain] at hsc
            exact hclamp sc hsc
          have hm_post2 : sf2.mem ⊨
              (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
               trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
               (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
                 (dispPtr ↦ₛ dispBs) ∗
                 memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
               consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (Mut.exec (RatchetState.consumeMessageKey C.F
                 x.msg.senderRatchetKey ck x.msg.counter x.msgType) tr.ratchet).1 ∗
               memRegion x.ret 48 ∗
               memRegion sp 28 ∗
               ((sp + 28#64) ↦₃₂ msgW) ∗
               ((sp + 32#64) ↦₆₄ x.locA) ∗
               ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
               memRegion (sp + 44#64) 4 ∗
               ((sp + 48#64) ↦₆₄ x.remA) ∗
               memRegion (sp + 320#64) 80 ∗
               memRegion (sp + 488#64) 920 ∗
               protocolAddressAt A.repAlloc x.rem x.remA ∗
               protocolAddressAt A.repAlloc x.loc x.locA ∗
               signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
               cliTapeAfter ctl x.cur x.rest draws ∗
               logOff tryDecryptPlacedImg ∗
               stackAt sp tryDecryptSubStack ∗
               tryDecryptSavedRegs s0.sp s0 ∗
               A.pool lim st_b sf2) ∗ R := by
            have hm488 : memRegion (sp + 488#64) 920 =
                memRegion (sp + 488#64) 248 ∗ (memRegion (sp + 736#64) 36 ∗ memRegion (sp + 772#64) 636) := by
              rw [mr_cut_add sp 488 248 672 (by decide), mr_cut_add sp 736 36 636 (by decide)]
            rw [trAt_split_ratchet, signalMessageAt_split_their, hm488, hstack_cmk]
            dsimp only [trG', r2, trNonRatchetAt, st_b] at hpost2 ⊢
            simp only [sepConj_assoc] at hpost2 ⊢
            rw [sepConj_pure_left_comm, satisfies_pure_sepConj]
            refine ⟨hclamp2, ?_⟩
            arm64_sep_close
          clear hpost2
          dsimp only [Out]
          split
          · next mkg r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .ok mkg := congrArg Prod.fst hmod
            rw [hres_eq] at hm_post2
            obtain ⟨s', hsteps_sub, hsub⟩ :=
              consumeMsgKey_cmk_ok_433_placed C A lim st_b ctl S H x trG' tr st1 r2 mkg draws R s0
                hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
                sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
                (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
                htr_f2' (by reg_chain) hclf2 hLf2 hm_post2
            refine ⟨s', hsteps_sub, ?_⟩
            rcases hsub with ⟨evs3, trG'', hfree3, _heq, hpq⟩ | hpan_sub
            · dsimp only [st_b, st_a] at hpq
              rw [← M.stepEvents_append evs2 evs3 (M.stepEvents evs1 st),
                ← M.stepEvents_append evs1 (evs2 ++ evs3) st] at hpq
              exact Or.inl ⟨evs1 ++ (evs2 ++ evs3), trG'',
                SeqEnv.append hevs1 (SeqEnv.append hevs2 hfree3), hpq⟩
            · exact Or.inr hpan_sub
          · next e r2' hmod =>
            have hr2_eq : r2 = r2' := congrArg Prod.snd hmod
            subst hr2_eq
            have hres_eq : (Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
                x.msg.counter x.msgType) tr.ratchet).1 = .error e := congrArg Prod.fst hmod
            have hne_panic : e ≠ .panic := by
              intro hp; subst hp; exact hnot_panic hres_eq
            rw [hres_eq] at hm_post2
            obtain ⟨s', hsteps_sub, hsub⟩ :=
              consumeMsgKey_cmk_err_433_placed C A lim st_b ctl uuidTryParse H x trG' tr st1 r2 e
                draws R s0 hne_panic hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2
                sf2 hpcf2 hrunf2 (by reg_chain) hsp_alf2 (by reg_chain) (by reg_chain) (by reg_chain)
                (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr_f2' (by reg_chain) hclf2 hLf2
                hm_post2
            refine ⟨s', hsteps_sub, ?_⟩
            rcases hsub with ⟨hne, evs3, trG'', hfree3, _heq, herr⟩ | hpan_sub
            · dsimp only [st_b, st_a] at herr
              rw [← M.stepEvents_append evs2 evs3 (M.stepEvents evs1 st),
                ← M.stepEvents_append evs1 (evs2 ++ evs3) st] at herr
              exact Or.inl ⟨hne, evs1 ++ (evs2 ++ evs3), trG'',
                SeqEnv.append hevs1 (SeqEnv.append hevs2 hfree3), herr⟩
            · exact Or.inr hpan_sub

/-- Default `FmtWriteEnv` `S4SeamPlaced` on CLI Block `433`. -/
theorem consumeMsgKey_433_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (haddrDisplay : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 215)
      (withLsCodeRoLoaded lsmpl (addrDisplaySpec M A lim)))
    (hcmk_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced C.F A lim CmkEnv)))
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)) :
    S4SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      C A lim ctl uuidTryParse S s4DefaultEnv :=
  consumeMsgKey_433_placed_ok_ofEnv C A lim ctl S FmtWriteEnv H haddrDisplay hcmk_call hdealloc

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget
