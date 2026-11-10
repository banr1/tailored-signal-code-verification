/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyHelpersPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import ProofLib.RegChain
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Segment `S4` (`ConsumeMsgKey`) Sub-Lemmas on Block `507`

Budget-threaded (`RustCliAllocBudget M`) `Ok`- and `Err`-branch symbolic continuations after
`RatchetState::consume_message_key` in `try_decrypt_with_state::<signal_session_handshake::Coins>`
(Block `507`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open scoped LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
open CryptoGames.LibsignalSession (
  Crypto MessageKeyGenerator RatchetState SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (LibsignalPlacement lsRustDeallocSym lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (consumeMessageKeyResultAt msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser protocolAddressAt sessionStateAt signalMessageAt utf8 uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost logOff trAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  errTailPC_at speBodyAt speTag tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  buf_to_mr extractLsb0_8_append56 mr_cut mr_cut_add pts64_to_mr sp_fp_eq stackAt_sub
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt (cliTryDecryptCommonHeapPlaced)
open CryptoVerification.Cli.SpqrV1.M4 (ErrWordsRel resultAt_err_unpack speBodyAt_err_pack)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507PlacedBudgetAux (
  consumeMsgKey_cmk_ok_507_placed_noPanicAux
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget (
  lsLogOff_eq_logOff_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  ErrTailStatePlaced PqRecvStatePlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (steps_call_out_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (tryDecryptOnPanic)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (steps_of_sepWP_placed_state)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
  speBodyAt_atState trAt_atState
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

@[simp] theorem consumeMessageKeyResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    consumeMessageKeyResultAt (A.atState lim st s) = consumeMessageKeyResultAt A.repAlloc := rfl

theorem consumeMsgKey_cmk_ok_507_placed_noPanic [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (.ok mkg) ∗
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
       A.pool lim st sf2) ∗ R) :
    ∃ s' evs3, Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      FreeOnlyEvs evs3 ∧
      PqRecvStatePlaced (blkPl_508).base A lim (M.stepEvents evs3 st) ctl
        x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s' :=
  consumeMsgKey_cmk_ok_507_placed_noPanicAux A lim st ctl H x trG' tr st1 r2 mkg draws R s0
    hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
    sf2 hpcf2 hrunf2 hsp_f2 hsp_alf2 hx19_f2 hx20_f2 hx21_f2 hx22_f2 hx23_f2
    hx25_f2 hx27_f2 hx28_f2 hfp_f2 htr_f2' hvregs_f2 hclf2 hLf2 hm_post2

theorem consumeMsgKey_cmk_ok_507_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (.ok mkg) ∗
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
       A.pool lim st sf2) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      ((∃ evs3 trG'', FreeOnlyEvs evs3 ∧
          PqRecvStatePlaced (blkPl_508).base A lim (M.stepEvents evs3 st) ctl
            x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 s' ∗ R))) := by
  obtain ⟨s', evs3, hsteps, hfree, hpq⟩ :=
    consumeMsgKey_cmk_ok_507_placed_noPanic A lim st ctl H x trG' tr st1 r2 mkg draws R s0
      hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2 hmsgW_byte
      sf2 hpcf2 hrunf2 hsp_f2 hsp_alf2 hx19_f2 hx20_f2 hx21_f2 hx22_f2 hx23_f2
      hx25_f2 hx27_f2 hx28_f2 hfp_f2 htr_f2' hvregs_f2 hclf2 hLf2 hm_post2
  exact ⟨s', hsteps, Or.inl ⟨evs3, trG', hfree, hpq⟩⟩

set_option maxHeartbeats 1200000 in
theorem consumeMsgKey_cmk_err_507_placed_noPanic [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (.error e) ∗
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
       A.pool lim st sf2) ∗ R) :
    ∃ s' evs3, Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      FreeOnlyEvs evs3 ∧
      ErrTailStatePlaced (blkPl_508).base A lim (M.stepEvents evs3 st) ctl
        x trG' { tr with ratchet := r2 } st1 e draws R s0 s' := by
  suffices ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      ∃ evs3, FreeOnlyEvs evs3 ∧
        ErrTailStatePlaced (blkPl_508).base A lim (M.stepEvents evs3 st) ctl
          x trG' { tr with ratchet := r2 } st1 e draws R s0 s' by
    obtain ⟨s', hsteps, evs3, hfree, herr⟩ := this
    exact ⟨s', evs3, hsteps, hfree, herr⟩
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A.repAlloc e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
        trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool lim st sf2) ∗ R) := by
    have hsp56 : memRegion sp 56 =
        memRegion sp 28 ∗ (memRegion (sp + 28#64) 4 ∗ (memRegion (sp + 32#64) 8 ∗
        (memRegion (sp + 40#64) 4 ∗ (memRegion (sp + 44#64) 4 ∗ memRegion (sp + 48#64) 8)))) := by
      have h1 := mr_cut_add sp 0 28 28 (by decide)
      simp only [BitVec.add_zero] at h1
      rw [h1,
        mr_cut_add sp 28 4 24 (by decide),
        mr_cut_add sp 32 8 16 (by decide),
        mr_cut_add sp 40 4 12 (by decide),
        mr_cut_add sp 44 4 8 (by decide)]
    rw [hsp56]
    refine Satisfies.mono (sepConj_mono_left (resultAt_err_unpack A.repAlloc sp e)) ?_
    have hm_post2' : sf2.mem ⊨
        (((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ ((sp + 48#64) ↦₆₄ x.remA)) ∗
        (consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (.error e) ∗
         sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
         trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
         (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
           (dispPtr ↦ₛ dispBs) ∗
           memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
         memRegion x.ret 48 ∗
         memRegion sp 28 ∗
         memRegion (sp + 44#64) 4 ∗
         memRegion (sp + 320#64) 80 ∗
         memRegion (sp + 488#64) 920 ∗
         protocolAddressAt A.repAlloc x.rem x.remA ∗
         protocolAddressAt A.repAlloc x.loc x.locA ∗
         signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest draws ∗
         logOff tryDecryptPlacedImg ∗
         stackAt sp tryDecryptSubStack ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         A.pool lim st sf2 ∗ R) := by
      simp only [sepConj_assoc] at hm_post2 ⊢
      arm64_sep_close
    have hm_post2'' := Satisfies.mono (sepConj_mono_left (sepConj_mono
      (pointsTo32_entails_memRegion (sp + 28#64) msgW)
      (sepConj_mono (pts64_to_mr (sp + 32#64) x.locA)
        (sepConj_mono (pointsTo32_entails_memRegion (sp + 40#64) x.msg.counter)
          (pts64_to_mr (sp + 48#64) x.remA))))) hm_post2'
    change sf2.mem ⊨ _ at hm_post2'' ⊢
    simp only [sepConj_assoc] at hm_post2'' ⊢
    arm64_sep_close
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP_placed_state hm_err hLf2 hclf2
    (mid := (blkPl_508).base + 1180#64)
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid := fun sm3 =>
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
      trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 56 ∗
      memRegion (sp + 320#64) 40 ∗
      speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
      memRegion (sp + 400#64) 1008 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool lim st sm3) ?_ ?_
  · wp_conv_pre =>
      rw [mr_cut sp 320 40 40 80 360#64,
        mr_cut sp 360 8 32 40 368#64,
        mr_cut sp 368 8 24 32 376#64,
        mr_cut sp 376 8 16 24 384#64,
        mr_cut sp 384 8 8 16 392#64,
        mr_cut sp 488 792 128 920 1280#64,
        mr_cut sp 1280 8 120 128 1288#64,
        mr_cut sp 1288 8 112 120 1296#64,
        mr_cut sp 1296 8 104 112 1304#64,
        mr_cut sp 1304 8 96 104 1312#64]
      simp only [sepConj_assoc,
        memRegion_eight (sp + 360#64),
        memRegion_eight (sp + 368#64),
        memRegion_eight (sp + 376#64),
        memRegion_eight (sp + 384#64),
        memRegion_eight (sp + 392#64),
        memRegion_eight (sp + 1280#64),
        memRegion_eight (sp + 1288#64),
        memRegion_eight (sp + 1296#64),
        memRegion_eight (sp + 1304#64)]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps_sync_pool ((blkPl_508).base + 1180#64)
    refine SepWP.focus_weaken
      (speBodyAt_err_pack A.repAlloc sp e w416 w424 w432 w440 w448 restHeap hrel)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (pointsTo32_entails_memRegion (sp + 400#64) 2#32) (by sep_focus) ?_
    have hm400 : memRegion (sp + 400#64) 1008 =
        memRegion (sp + 400#64) 4 ∗ (memRegion (sp + 404#64) 4 ∗ (memRegion (sp + 408#64) 8 ∗
        (memRegion (sp + 416#64) 8 ∗ (memRegion (sp + 424#64) 8 ∗ (memRegion (sp + 432#64) 8 ∗
        (memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 32 ∗
        (memRegion (sp + 488#64) 792 ∗ (memRegion (sp + 1280#64) 8 ∗
        (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ memRegion (sp + 1312#64) 96))))))))))))) := by
      rw [mr_cut_add sp 400 4 1004 (by decide),
        mr_cut_add sp 404 4 1000 (by decide),
        mr_cut_add sp 408 8 992 (by decide),
        mr_cut_add sp 416 8 984 (by decide),
        mr_cut_add sp 424 8 976 (by decide),
        mr_cut_add sp 432 8 968 (by decide),
        mr_cut_add sp 440 8 960 (by decide),
        mr_cut_add sp 448 8 952 (by decide),
        mr_cut_add sp 456 32 920 (by decide),
        mr_cut_add sp 488 792 128 (by decide),
        mr_cut_add sp 1280 8 120 (by decide),
        mr_cut_add sp 1288 8 112 (by decide),
        mr_cut_add sp 1296 8 104 (by decide),
        mr_cut_add sp 1304 8 96 (by decide)]
    rw [hm400]
    wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ (st_cur : M.σ) (st4 : State),
        st4.pc = (blkPl_508).base + 1200#64 → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st4.mem →
        ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
           trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A.repAlloc x.rem x.remA ∗
           protocolAddressAt A.repAlloc x.loc x.locA ∗
           signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
           cliTapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool lim st_cur st4) ∗ R) →
        ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) st4 s' ∧
          ErrTailStatePlaced (blkPl_508).base A lim st_cur ctl
            x trG' { tr with ratchet := r2 } st1 e draws R s0 s' := by
      intro st_cur st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP_placed_state hm4 hL4 hcl4
        (mid := (blkPl_508).base + 780#64)
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid := fun sf =>
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool lim st_cur sf) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_508).base + 780#64)
        wp_done
      · intro sf hpcf hrunf hclf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, ?_⟩
        unfold ErrTailStatePlaced CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced
        have hpc_err : sf.pc = errTailPC_at (blkPl_508).base := by
          rw [hpcf]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [cliTryDecryptCommonHeapPlaced]
        simp only [sessionStateAt_atState, trAt_atState, speBodyAt_atState,
          protocolAddressAt_atState, signalMessageAt_atState, RustCliAllocBudget.atState_pool]
        rw [lsLogOff_eq_logOff_placed]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP_placed_state hm3 hL3 hcl3
        (mid := (blkPl_508).base + 1200#64)
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid := fun st4 =>
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool lim st st4) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_508).base + 1200#64)
        wp_done
      · intro st4 hpc4 hrun4 hcl4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        obtain ⟨s', hsteps, herr⟩ :=
          herr_tail st st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
        exact ⟨s', hsteps, [], FreeOnlyEvs.nil, by simpa [M.stepEvents_nil] using herr⟩
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP_placed_state hm3 hL3 hcl3
        (mid := lsρ lsRustDeallocSym)
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = (blkPl_508).base + 1200#64 ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid := fun sm4 =>
          sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool lim st sm4) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        refine SepWP.focus_weaken (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2)
          (by sep_focus) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hcl4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            (rustCliDeallocBudgetSpec M A lim).pre (dispPtr, dispCap.toNat, 1, st) sm4 ∗
            ((sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
              trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
              memRegion x.ret 48 ∗
              memRegion sp 56 ∗
              memRegion (sp + 320#64) 40 ∗
              speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
              memRegion (sp + 400#64) 1008 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              protocolAddressAt A.repAlloc x.loc x.locA ∗
              signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
              cliTapeAfter ctl x.cur x.rest draws ∗
              logOff tryDecryptPlacedImg ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - allocHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustCliDeallocBudgetSpec]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl,
            by rw [hlr4]; exact _root_.LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 508 1200#64 (by decide) (by decide)⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out_placed (dispPtr, dispCap.toNat, 1, st) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hcl4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustCliDeallocBudgetSpec] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hcl5 hL5 hpost5
          dsimp only [rustCliDeallocBudgetSpec] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨⟨hpres5, _⟩, hpost5⟩
          have htr5_s0 : st5.trace = s0.trace := hpres5.2.1.trans htr4
          have hm5 : st5.mem ⊨
              (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
               trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
               memRegion x.ret 48 ∗
               memRegion sp 56 ∗
               memRegion (sp + 320#64) 40 ∗
               speBodyAt A.repAlloc (utf8 "decrypt") (sp + 360#64) e ∗
               memRegion (sp + 400#64) 1008 ∗
               protocolAddressAt A.repAlloc x.rem x.remA ∗
               protocolAddressAt A.repAlloc x.loc x.locA ∗
               signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
               cliTapeAfter ctl x.cur x.rest draws ∗
               logOff tryDecryptPlacedImg ∗
               stackAt sp tryDecryptSubStack ∗
               tryDecryptSavedRegs s0.sp s0 ∗
               A.pool lim (M.stepEvents (rustDeallocEvents dispCap.toNat 1) st) st5) ∗ R := by
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost5 ⊢
            arm64_sep_close
          obtain ⟨s', hsteps, herr⟩ :=
            herr_tail (M.stepEvents (rustDeallocEvents dispCap.toNat 1) st) st5
              hpc5 hrun5 (by reg_chain) hsp_al5 (by reg_chain) htr5_s0 (by reg_chain)
              hcl5 hL5 (by reg_chain) (by reg_chain) (by reg_chain) hm5
          exact ⟨s', hsteps, rustDeallocEvents dispCap.toNat 1,
            FreeOnlyEvs.singleton 1 dispCap.toNat, herr⟩

theorem consumeMsgKey_cmk_err_507_placed [LibsignalPlacement] {M : AllocCostModel}
    (_C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (_parse : UuidParser) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_508).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_508).rebase (blkPl_508).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       trAt A.repAlloc (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A.repAlloc (sp + 400#64) (.error e) ∗
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
       A.pool lim st sf2) ∗ R) :
    ∃ s', Steps ((blkPC_508).rebase (blkPl_508).base H) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ evs3 trG'', FreeOnlyEvs evs3 ∧
          ErrTailStatePlaced (blkPl_508).base A lim (M.stepEvents evs3 st) ctl
            x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (e = .panic ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  obtain ⟨s', evs3, hsteps, hfree, herr⟩ :=
    consumeMsgKey_cmk_err_507_placed_noPanic A lim st ctl H x trG' tr st1 r2 e draws R s0
      hsp0_al hsp_al' hdealloc hsp_def hdisp1 hdisp2
      sf2 hpcf2 hrunf2 hsp_f2 hsp_alf2 hx19_f2 hx20_f2 hx23_f2
      hx25_f2 hx27_f2 hx28_f2 hfp_f2 htr_f2' hvregs_f2 hclf2 hLf2 hm_post2
  exact ⟨s', hsteps, Or.inl ⟨hne_panic, evs3, trG', hfree, herr⟩⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ConsumeMsgKeySub507PlacedBudget
