/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import Lean -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Top Regions & `.headerReceived` `encaps1 = none` Panic Arm (Block `427`)

Threads `RustCliAllocBudget` through alignment-free Phase 4 finish (`+6216 -> +4600`) and
the `.headerReceived` `encaps1 = none` panic arm in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.RustHeap
open scoped CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl lsρ sepWP_seq_lscl)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrCoinsAfterPlaced spqrCoinsAtPlaced spqrCoinsAtPlaced_entails_after_zero spqrMlkemEncaps1Sym
   spqrSendDropJumpTablePlacedAt spqrSend_unwrap_failed_placed spqrUnwrapFailedSym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes MlKem PqRatchetState mlkemEncaps1Spec spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack spqrSendResultAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt none2Cap_add_two_beq_zero noneCap_add_two_beq_zero protoPqRatchetStateAt
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   pqRatchetStatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr (v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt chunkedStatesAt_headerReceived_expose exists_words4_of_len32
   extractLsb_hi_append64 extractLsb_lo_append64 ite_zero32_self ite_zero64_self
   memRegion_16_words2 memRegion_24_split_8_16 memRegion_24_words3' memRegion_32_eq_words4
   memRegion_48_eq_words6 memRegion_48_words6 memRegion_72_split_48_24 optKeyAt_none_of_word
   optKeyAt_some_of_words optMsgKeySlotsAt pqRatchetStatePBPinnedAt_entails_proto
   sendResultAt_some_of_parts send_stackAt_callee_eq_allocHook spqrSendCalleeStack
   stackAt_spqrSendCallee_from_allocHook stackAt_spqrSendCallee_from_extHook
   stackAt_spqrSendCallee_to_allocHook stackAt_spqrSendCallee_to_extHook statesSendPreArmScratch
   vecU8Heap_entails_dealloc vecU8Rest vecU8_expose_words words2_to_memRegion_16
   words3_to_memRegion_24' words4At words4At_entails_memRegion words6_to_memRegion_48
   words_to_vecU8)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
  (DeallocOkExtPlaced spqrSend_dealloc_sub_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget
  (step_send_drop_pq_state_32134_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (spqrCoinsFillAtPlaced_of_after0_cro spqrCoinsFillAtSpecPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (HeaderReceived1aEnv fitsEnv_headerReceived1a_iff fitsEvents_headerReceived1aEvents_split
   headerReceived1aEvents spqrSend_allocZeroedNoOom_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (spqrSend_encapsulate1_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (call_lscro_calleeStack_sepWP of_sepWP_lscro_plain spqrSend_shim_ok_placed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (call_sessionShim_budget)
open LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (sepWP_seg_vm sepWPp_seg_vm tpidrEl0_setMem_pre tpidrEl0_writeVReg128_pre
   tpidrEl0_writeVReg32_pre tpidrEl0_writeVReg64_pre transport_budgetPool_norm
   wpp_transport_budgetPool_norm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

export CryptoVerification.Cli.SpqrV1.Top.Send (spqrUnwrapFailedSym spqrSend_unwrap_failed_placed)

variable [LibsignalPlacement]

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero spqrSendPlacedEntry
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32 LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_lo_append64 extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

private def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

omit [LibsignalPlacement] in
private theorem sepWP_seq_mid_lscl {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hM hcl' => h2 sm Pm hpc hrun hcl' hM)

private theorem seq_vm_clean {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP ((blkPC_427).rebase (blkPl_427).base Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target sm P_mid post) :
    SepWP ((blkPC_427).rebase (blkPl_427).base Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem stackAt_spqrSendCallee_from_extHook_of_eq {sp sp' : BitVec 64} (h : sp' = sp) :
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp' extHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [h]
  exact stackAt_spqrSendCallee_from_extHook sp

/-! ## 1. Alignment-Free Result Construction & Epilogue (`+6216 -> +4600`) -/

/-- `spqrSendPlacedEntry + 6216#64 -> spqrSendPlacedEntry + 6328#64` (28 instructions = 112 bytes),
    without requiring `hret_align` on `ret`. -/
theorem step_send_build_result_320a4'_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (st : M.σ) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (Frame : SepProp)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = spqrSendPlacedEntry + 6216#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25)
    (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 6328#64) s
      (memRegion ret 72 ∗
        vecU8 A.repAlloc (s.sp + 1424#64) stBytes ∗
        vecU8 A.repAlloc (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A.repAlloc s.sp key ∗
        ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗
        memRegion (s.sp + 7136#64) 16 ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x19 = v_20 ∧
          sf.readReg64 .x21 = x21 ∧
          sf.readReg64 .x23 = x23 ∧
          sf.readReg64 .x25 = x25 ∧
          sf.readReg64 .x27 = x27 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗
            memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗
            memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗
            memRegion (s.sp + 7136#64) 16 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  have hst_exp := vecU8_expose_words A.repAlloc (s.sp + 1424#64) stBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_exp
  have hmsg_exp := vecU8_expose_words A.repAlloc (s.sp + 4080#64) msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmsg_exp
  refine SepWP.focus_weaken hst_exp (by sep_focus) ?_
  wp_pull_exists; rename_i stCap stPtr
  refine SepWP.focus_weaken hmsg_exp (by sep_focus) ?_
  wp_pull_exists; rename_i msgCap msgPtr
  wp_conv_pre =>
    rw [memRegion_72_split_48_24 ret,
        memRegion_48_words6 ret,
        memRegion_48_words6 (s.sp + 4192#64),
        memRegion_16_words2 (s.sp + 7136#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_pull_exists
  have hret_st := words_to_vecU8 A.repAlloc ret stCap stPtr stBytes
  have hret_msg := words_to_vecU8 A.repAlloc (ret + 24#64) msgCap msgPtr msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_msg
  have h1424 := words3_to_memRegion_24' (s.sp + 1424#64) stCap stPtr (BitVec.ofNat 64 stBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1424
  have h4080 := words3_to_memRegion_24' (s.sp + 4080#64) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4080
  have h4192 := words6_to_memRegion_48 (s.sp + 4192#64)
    stCap stPtr (BitVec.ofNat 64 stBytes.length) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4192
  have h7136 := words2_to_memRegion_16 (s.sp + 7136#64) stCap stPtr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h7136
  cases key with
  | some k =>
    refine seq_vm_clean (mid := (blkPl_427).base + 6328#64)
      (P_mid := spqrSendResultAt A.repAlloc ret (some (stBytes, some k, msgBytes)) ∗
        memRegion (s.sp + 8#64) 8 ∗
        memRegion (s.sp + 24#64) 24 ∗
        memRegion (s.sp + 1424#64) 24 ∗
        memRegion (s.sp + 4080#64) 24 ∗
        memRegion (s.sp + 4192#64) 48 ∗
        memRegion (s.sp + 7136#64) 16 ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (Q := fun sm =>
        AllocCallPreserved s sm ∧
        sm.trace = s.trace ∧
        sm.sp = s.sp ∧
        sm.readReg64 .x19 = v_20 ∧
        sm.readReg64 .x21 = x21 ∧
        sm.readReg64 .x23 = x23 ∧
        sm.readReg64 .x25 = x25 ∧
        sm.readReg64 .x27 = x27 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s)
      ?_ ?_
    · by_vm_steps (
        dsimp only [optMsgKeySlotsAt]
        wp_pull_exists; rename_i mkCap mkPtr
        wp_conv_pre => rw [memRegion_24_words3' (ret + 48#64)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_pull_exists
        wp_steps
        have hret_key := optKeyAt_some_of_words A.repAlloc (ret + 48#64) mkCap mkPtr k
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
        have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
        have h24 := words3_to_memRegion_24' (s.sp + 24#64) 32#64 v_20 mkCap
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
        refine SepWP.focus_weaken hret_st (by sep_focus) ?_
        refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
        refine SepWP.focus_weaken hret_key (by sep_focus) ?_
        refine SepWP.focus_weaken
          (sendResultAt_some_of_parts A.repAlloc ret stBytes msgBytes (some k) hmsg_len) (by sep_focus) ?_
        refine SepWP.focus_weaken h8 (by sep_focus) ?_
        refine SepWP.focus_weaken h24 (by sep_focus) ?_
        refine SepWP.focus_weaken h1424 (by sep_focus) ?_
        refine SepWP.focus_weaken h4080 (by sep_focus) ?_
        refine SepWP.focus_weaken h4192 (by sep_focus) ?_
        refine SepWP.focus_weaken h7136 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
    · intro sf hpcsf hrunsf hvm ⟨hacp, htr, hsp, hx19f, hx21f, hx23f, hx25f, hx27f, hvregs⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact ProofLib.SepWP.done hpcsf hrunsf
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hacp, hrunsf, htr, hsp,
          hx19f, hx21f, hx23f, hx25f, hx27f, hvregs,
          Entails.of_eq (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil])⟩
  | none =>
    dsimp only [optMsgKeySlotsAt]
    wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_split_8_16 (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_pull_exists
    refine SepWP.focus_weaken (vecU8Heap_entails_dealloc A.repAlloc mkCap mkPtr []) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
    have hret_key := optKeyAt_none_of_word A.repAlloc (ret + 48#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    by_cases hc0 : (mkCap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : mkCap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      refine seq_vm_clean (mid := (blkPl_427).base + 6328#64)
        (P_mid := spqrSendResultAt A.repAlloc ret (some (stBytes, none, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗
          memRegion (s.sp + 24#64) 24 ∗
          memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗
          memRegion (s.sp + 4192#64) 48 ∗
          memRegion (s.sp + 7136#64) 16 ∗
          A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm =>
          AllocCallPreserved s sm ∧
          sm.trace = s.trace ∧
          sm.sp = s.sp ∧
          sm.readReg64 .x19 = v_20 ∧
          sm.readReg64 .x21 = x21 ∧
          sm.readReg64 .x23 = x23 ∧
          sm.readReg64 .x25 = x25 ∧
          sm.readReg64 .x27 = x27 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken hret_st (by sep_focus) ?_
          refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
          refine SepWP.focus_weaken hret_key (by sep_focus) ?_
          refine SepWP.focus_weaken
            (sendResultAt_some_of_parts A.repAlloc ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
          refine SepWP.focus_weaken h8 (by sep_focus) ?_
          refine SepWP.focus_weaken (words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 0#64) (by sep_focus) ?_
          refine SepWP.focus_weaken h1424 (by sep_focus) ?_
          refine SepWP.focus_weaken h4080 (by sep_focus) ?_
          refine SepWP.focus_weaken h4192 (by sep_focus) ?_
          refine SepWP.focus_weaken h7136 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      · intro sf hpcsf hrunsf hvm ⟨hacp, htr, hsp, hx19f, hx21f, hx23f, hx25f, hx27f, hvregs⟩
        rw [← A.pool_of_vmPreserved hvm]
        exact ProofLib.SepWP.done hpcsf hrunsf
          ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hacp, hrunsf, htr, hsp,
            hx19f, hx21f, hx23f, hx25f, hx27f, hvregs,
            Entails.of_eq (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil])⟩
    · rw [send_stackAt_callee_eq_allocHook s.sp]
      refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (P_mid := (A.live mkPtr mkCap.toNat 1 ∗ memRegion mkPtr mkCap.toNat) ∗
          A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
          (spqrSendResultAt A.repAlloc ret (some (stBytes, none, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗
            memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗
            memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗
            memRegion (s.sp + 7136#64) 16 ∗
            memRegion (s.sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗ Frame))
        (Q := fun sc =>
          AllocCallPreserved s sc ∧
          sc.trace = s.trace ∧
          sc.sp = s.sp ∧
          sc.readReg64 .x0 = mkPtr ∧
          sc.readReg64 .x1 = mkCap ∧
          sc.readReg64 .x2 = 1#64 ∧
          sc.readReg64 .x30 = (blkPl_427).base + 6328#64 ∧
          sc.readReg64 .x19 = v_20 ∧
          sc.readReg64 .x21 = x21 ∧
          sc.readReg64 .x23 = x23 ∧
          sc.readReg64 .x25 = x25 ∧
          sc.readReg64 .x27 = x27 ∧
          calleeSavedVRegs sc = calleeSavedVRegs s)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken hret_st (by sep_focus) ?_
          refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
          refine SepWP.focus_weaken hret_key (by sep_focus) ?_
          refine SepWP.focus_weaken
            (sendResultAt_some_of_parts A.repAlloc ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
          refine SepWP.focus_weaken h8 (by sep_focus) ?_
          refine SepWP.focus_weaken h24 (by sep_focus) ?_
          refine SepWP.focus_weaken h1424 (by sep_focus) ?_
          refine SepWP.focus_weaken h4080 (by sep_focus) ?_
          refine SepWP.focus_weaken h4192 (by sep_focus) ?_
          refine SepWP.focus_weaken h7136 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, Entails.of_eq (by sep_ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩)
      · intro sc hpcc hrunc hvmc
          ⟨hacpc, htrc, hspc, hx0c, hx1c, hx2c, hlrc, hx19c, hx21c, hx23c, hx25c, hx27c, hvregsc⟩
        rw [← A.pool_of_vmPreserved hvmc, ← hspc]
        wp_call hdealloc_fo (mkPtr, mkCap.toNat, 1, st)
        rw [hspc]
        have hacp_call : AllocCallPreserved sc sf := by assumption
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨rustDeallocEvents mkCap.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 mkCap.toNat,
            hacpc.trans hacp_call,
            by wp_norm_goal, (by wp_norm_goal : _ = sc.trace).trans htrc,
            (by wp_norm_goal : _ = sc.sp).trans hspc,
            (by wp_norm_goal : _ = sc.readReg64 .x19).trans hx19c,
            (by wp_norm_goal : _ = sc.readReg64 .x21).trans hx21c,
            (by wp_norm_goal : _ = sc.readReg64 .x23).trans hx23c,
            (by wp_norm_goal : _ = sc.readReg64 .x25).trans hx25c,
            (by wp_norm_goal : _ = sc.readReg64 .x27).trans hx27c,
            (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs sc).trans hvregsc,
            Entails.of_eq (by sep_ac_rfl)⟩

private theorem step_send_epoch_dealloc_32114_acp_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s : State) (bst : M.σ) (x23 x25 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6328#64) (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23) (hx25 : s.readReg64 .x25 = x25)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x19 = 0#32) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 6360#64) s
      (A.pool lim bst s ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          sf.readReg64 .x25 = x25 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ A.pool lim (M.stepEvents evs bst) sf ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rcases hflag with hx21 | hx19
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg]
          try (first | rfl | sep_ac_rfl))⟩
  · have hgpr19 : BitVec.truncate 32 (s.readReg64 (Reg.gpr 19#5)) = 0#32 := hx19
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [AllocCostModel.stepEvents_nil,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg]
          try (first | rfl | sep_ac_rfl))⟩

/-- `spqrSendPlacedEntry + 6216#64 -> spqrSendPlacedEntry + 4600#64`, without requiring `hret_align`. -/
theorem step_send_finish_320a4'_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = spqrSendPlacedEntry + 6216#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25) (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hflag : x21 = noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !st.chain.isSome)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4600#64) s
      (memRegion ret 72 ∗ vecU8 A.repAlloc (s.sp + 1424#64) stBytes ∗
        vecU8 A.repAlloc (s.sp + 4080#64) msgBytes ∗ optMsgKeySlotsAt A.repAlloc s.sp key ∗
        ((s.sp + 32#64) ↦₆₄ v_20) ∗ memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
        pqRatchetStatePBPinnedAt A.repAlloc g (s.sp + 4704#64) st ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧ AllocCallPreserved s sf ∧ sf.status = .Running ∧
          sf.trace = s.trace ∧ sf.sp = s.sp ∧ sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗ memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 4704#64) 352 ∗
            memRegion (s.sp + 7136#64) 16 ∗ spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  refine SepWP.focus_weaken (pqRatchetStatePBPinnedAt_entails_proto A.repAlloc g (s.sp + 4704#64) st) (by sep_focus) ?_
  refine SepWP.weaken_pre ?_
    (sepWP_seq_mid_lscl hcl
      (step_send_build_result_320a4'_placed hdealloc s bst ret v_20 x21 x23 x25 x27 stBytes msgBytes key
        (protoPqRatchetStateAt A.repAlloc (s.sp + 4704#64) st ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
        hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 hx28 hsp_align) ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 Q1 hpc1 _ hcl1 ⟨evs₁, hevs₁, hacp₁, hrun1, htr1, hsp1, hx19_1, hx21_1, hx23_1, hx25_1, _, hvregs1, hQ1⟩
    have hflag1 : s1.readReg64 .x21 = noneCap ∨ s1.readReg32 .x19 = 0#32 := by
      rcases hflag with h21 | h20
      · left; rw [hx21_1, h21]
      · right; simp only [State.readReg32, hx19_1, h20]
    refine SepWP.weaken_pre ?_
      (sepWP_seq_mid_lscl hcl1
        (step_send_epoch_dealloc_32114_acp_placed (A := A) (lim := lim) s1 (M.stepEvents evs₁ bst) x23 x25
          (spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s.sp + 8#64) 8 ∗ memRegion (s.sp + 24#64) 24 ∗
            memRegion (s.sp + 1424#64) 24 ∗ memRegion (s.sp + 4080#64) 24 ∗
            memRegion (s.sp + 4192#64) 48 ∗ memRegion (s.sp + 7136#64) 16 ∗
            stackAt s.sp spqrSendCalleeStack ∗
            protoPqRatchetStateAt A.repAlloc (s.sp + 4704#64) st ∗ spqrSendDropJumpTablePlacedAt ∗ Frame)
          hpc1 hrun1 hx23_1 hx25_1 hflag1) ?_)
    · exact Entails.trans hQ1 (Entails.of_eq (by sep_ac_rfl))
    · intro s2 Q2 hpc2 _ hcl2 ⟨evs₂, hevs₂, hacp₂, hrun2, htr2, hsp2, hx23_2, hx25_2, hvregs2, hQ2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2, hsp1]
      have hx25_2' : (s2.readReg64 .x25 + 1#64 == 0#64) = !st.chain.isSome := by rw [hx25_2, hx25_ch]
      rw [← hsp1, ← hsp2] at hQ2
      refine SepWP.weaken_pre ?_
        (SepWP.mono (step_send_drop_pq_state_32134_placed hdealloc s2 (M.stepEvents evs₂ (M.stepEvents evs₁ bst)) st x23
          (spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes)) ∗
            memRegion (s2.sp + 8#64) 8 ∗ memRegion (s2.sp + 24#64) 24 ∗
            memRegion (s2.sp + 1424#64) 24 ∗ memRegion (s2.sp + 4080#64) 24 ∗
            memRegion (s2.sp + 4192#64) 48 ∗ memRegion (s2.sp + 7136#64) 16 ∗ Frame)
          hcl2 hpc2 hrun2 hsp2_align hx23_2 hx25_2') ?_)
      · exact Entails.trans hQ2 (Entails.of_eq (by sep_ac_rfl))
      · intro sf Qf _ _ ⟨evs₃, hevs₃, hacp₃, hrunf, htrf, hspf, hx23_f, hvregsf, hQf⟩
        refine ⟨evs₁ ++ evs₂ ++ evs₃, (hevs₁.append hevs₂).append hevs₃, (hacp₁.trans hacp₂).trans hacp₃,
          hrunf, htrf.trans (htr2.trans htr1), hspf.trans (hsp2.trans hsp1),
          hx23_f, hvregsf.trans (hvregs2.trans hvregs1), ?_⟩
        rw [hsp2, hsp1] at hQf; rw [M.stepEvents_append, M.stepEvents_append]
        exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. Relocatable `.headerReceived` Arm when `K.encaps1 hdr rand = none` (`+1312 -> unwrap_failed`) -/

section HeaderReceivedPanicPlaced

private theorem call_shim_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionShimBudgetSpec)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hsplit : P = A.pool lim st s ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf (A.pool lim st sf ∗ Frame) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  exact call_sessionShim_budget hcall st hpc hrun hsp hsp_align hlr htrace hsplit
    fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

private theorem call_allocZeroedNoOom_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim true))
    (size : Nat) (st : M.σ) (hlay : RustLayoutOk size 1)
    (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗ memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall (x := (size, 1, st))
    (F := memRegion (sp_call - 123008#64) 118912 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hlay, hfit, by rw [hlr]; exact hlr_ls⟩, by ac_nf at hm ⊢⟩
  · simp only [rustCliAllocNoOomSpec, ↓reduceIte]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, hne0, _⟩ => ?_
    simp only [Reg.x0] at hne0 ⊢
    have hzero_mem :
        (sf.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ⊢
        memRegion (sf.readReg64 (Reg.gpr 0#5)) size := by
      have h := pointsToBytes_entails_memRegion (sf.readReg64 (Reg.gpr 0#5)) (List.replicate size 0#8)
      rwa [List.length_replicate] at h
    refine SepWP.fold hzero_mem (by sep_focus) ?_
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
          hne0 (beq_false_of_ne hne0) (hacp.2.1.trans htrace))

private theorem call_coinsFill32_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    {ctl cur : BitVec 64} {tape : List (BitVec 8)}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (spqrCoinsFillAtSpecPlaced spqrSendCalleeStack cur tape)))
    (h32 : 32 ≤ tape.length)
    (dstA : BitVec 64) (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dstA) (hx1 : (s.readReg64 .x1).toNat = 32)
    (hsplit : P = (memRegion dstA 32 ∗ spqrCoinsAfterPlaced ctl cur tape 0 ∗
      A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → sf.trace = s0.trace →
      SepWP prog tgt sf
        (((dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  have hcoins0 : spqrCoinsAfterPlaced ctl cur tape 0 = spqrCoinsAfterPlaced 0#64 cur tape 0 := rfl
  rw [hsplit, hcoins0]
  refine call_lscro_calleeStack_sepWP (x := (dstA, 32))
    sp_call spqrSendCalleeStack (by decide)
    (T_pre := memRegion dstA 32 ∗ spqrCoinsAfterPlaced 0#64 cur tape 0)
    (T_post := fun sf => ⌜sf.trace = s.trace⌝ ∗
      (dstA ↦ₛ (tape ++ List.replicate 32 0#8).take 32) ∗
      spqrCoinsAfterPlaced 0#64 cur tape (min 32 tape.length))
    (F := A.pool lim st s ∗ Frame)
    (φ_pre := s.readReg64 .x0 = dstA ∧ (s.readReg64 .x1).toNat = 32)
    (φ_post := fun sf => VmPreserved s sf)
    hcall hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl)
    ⟨hx0, hx1⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf hvm_sf hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  have hcoins_ctl : spqrCoinsAfterPlaced 0#64 cur tape 32 = spqrCoinsAfterPlaced ctl cur tape 32 := rfl
  rw [List.take_append_of_le_length h32, Nat.min_eq_left h32, hcoins_ctl, ← hrand_val,
      ← A.pool_of_vmPreserved hvm_sf]
  have hpure :
      ((stackAt sp_call spqrSendCalleeStack ∗
        (⌜sf.trace = s.trace⌝ ∗ (dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32)) ∗
        (A.pool lim st sf ∗ Frame)) =
      ⌜sf.trace = s.trace⌝ ∗
        (((dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by sep_ac_rfl
  rw [hpure]
  exact SepWP.pure_elim fun htr_sf =>
    hnext sf hcrl_sf hpc_sf hrun_sf hsp_sf
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs (htr_sf.trans htrace)

set_option maxHeartbeats 1600000 in
/-- Total-correctness `SepWP` execution from `spqrSendPlacedEntry + 1312#64` to the
    `core::result::unwrap_failed` panic stub (`lsρ spqrUnwrapFailedSym`) when
    `K.encaps1 hdr rand = none`, with zero OOM branches under
    `FitsEvents M lim bSt headerReceived1aEvents`. -/
theorem step_headerReceived_1312_encaps1_none_sepWP_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
      (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K)))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    (hFit : FitsEvents M lim bSt headerReceived1aEvents)
    {s0 s : State} {P Frame : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ A.pool lim bSt s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWP (spqrSendPlacedProg ext) (lsρ spqrUnwrapFailedSym) s P
      (fun sm _ => sm.status = .Running ∧ sm.trace = s0.trace) := by
  have ⟨hfit_2080, hfit_32, _⟩ := fitsEvents_headerReceived1aEvents_split hFit
  let st1 := M.stepEvents (rustAllocEvents 2080 1) bSt
  have hshim := spqrSend_shim_ok_placed hA
  have hallocz := spqrSend_allocZeroedNoOom_ok_placed hZero
  have hrng_call := spqrCoinsFillAtPlaced_of_after0_cro (cur := cur) (rest := tape) hcoinsFill
  have henc1_call := spqrSend_encapsulate1_ok_placed henc1
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim hallocz hrng_call henc1_call ⊢
  dsimp only [withVmPreserved, mlkemEncaps1Spec] at henc1_call
  subst hP
  simp only [Reg.x24, Reg.x26, Reg.x28] at hx24 hx26 hx28
  apply of_sepWP_lscro_plain (mid := lsmpl.base 618) hcrl
  rw [memRegion_48_eq_words6 (sp + 4192#64),
      memRegion_32_eq_words4 (sp + 7136#64),
      memRegion_32_eq_words4 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  step_vm_pool (lsmpl.base 618) =>
    refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _)
      (by dsimp only [words4At]; sep_focus) ?_
    refine SepWP.fold (spqrCoinsAtPlaced_entails_after_zero ctl cur tape)
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv_rng
    refine call_coinsFill32_lscro (ctl := ctl) hrng_call h32 (sp + 7136#64) rand hrand_val bSt
      (s0 := s0) (sp_call := sp) hinv_rng
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x0, BitVec.add_assoc, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      fun sr1 hinv_sr1 hpc_sr1 hrun_sr1 hsp_sr1
        hx19_r1 hx20_r1 hx21_r1 hx22_r1 hx23_r1 hx24_r1 hx25_r1 hx26_r1 hx27_r1 hx28_r1 hvregs_r1 htr_sr1 => ?_
    simp only [Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sr1 hx19_r1 hx20_r1 hx21_r1 hx22_r1 hx23_r1 hx24_r1 hx25_r1 hx26_r1 hx27_r1 hx28_r1 hvregs_r1
    apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv_sr1
    step_vm_pool (lsρ spqrRustNoAllocShimSym) =>
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hinv_sh1
      refine call_shim_lscro hshim bSt (s0 := s0) (sp_call := sp) hinv_sh1
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
        (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
        fun sh1 hinv_sh1' hpc_sh1 hrun_sh1 hsp_sh1 hcs_sh1 htr_sh1 => ?_
      rcases hcs_sh1 with ⟨hx19_s1, hx20_s1, hx21_s1, hx22_s1, hx23_s1, hx24_s1, hx25_s1, hx26_s1, hx27_s1, hx28_s1, _, hvregs_s1⟩
      simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh1 hx19_s1 hx20_s1 hx21_s1 hx22_s1 hx23_s1 hx24_s1 hx25_s1 hx26_s1 hx27_s1 hx28_s1 hvregs_s1
      apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocZeroedSym) hinv_sh1'
      step_vm_pool (lsρ spqrRustAllocZeroedSym) =>
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        intro hinv_az1
        refine call_allocZeroedNoOom_lscro hallocz 2080 bSt ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_2080
          (s0 := s0) (ret_pc := (blkPl_427).base + 1400#64) (sp_call := sp) hinv_az1
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *]) hsp_align
          (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
          (by sep_focus)
          fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_
        rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
        simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
        apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv_ok1
        step_vm_pool (lsρ spqrRustNoAllocShimSym) =>
          apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          intro hinv_sh2
          refine call_shim_lscro hshim st1 (s0 := s0) (sp_call := sp) hinv_sh2
            (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
            (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
            fun sh2 hinv_sh2' hpc_sh2 hrun_sh2 hsp_sh2 hcs_sh2 htr_sh2 => ?_
          rcases hcs_sh2 with ⟨hx19_s2, hx20_s2, hx21_s2, hx22_s2, hx23_s2, hx24_s2, hx25_s2, hx26_s2, hx27_s2, hx28_s2, _, hvregs_s2⟩
          simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh2 hx19_s2 hx20_s2 hx21_s2 hx22_s2 hx23_s2 hx24_s2 hx25_s2 hx26_s2 hx27_s2 hx28_s2 hvregs_s2
          apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocZeroedSym) hinv_sh2'
          step_vm_pool (lsρ spqrRustAllocZeroedSym) =>
            apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            intro hinv_az2
            refine call_allocZeroedNoOom_lscro hallocz 32 st1 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_32
              (s0 := s0) (ret_pc := (blkPl_427).base + 1424#64) (sp_call := sp) hinv_az2
              (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              (by simp only [State.sp, arm64_norm, *]) hsp_align
              (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
              (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
              (by sep_focus)
              fun sf2 _hinv_ok2 hpc2 hrun2 hsp2 hcs2 _hne0_2 _h0b_2 htr_ok2 => ?_
            rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩
            simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
            obtain ⟨rw0, rw1, rw2, rw3, hrand_words⟩ :=
              exists_words4_of_len32 rand.toList (List.Vector.toList_length rand)
            wp_conv_pre => rw [hrand_words (sp + 7136#64)]; dsimp only [words4At]
            wp_steps
            have hfold_rand_7536 :
                words4At (sp + 7536#64) rw0 rw1 rw2 rw3 ⊢ ((sp + 7536#64) ↦ₛ rand.toList) := by
              rw [hrand_words (sp + 7536#64)]
              exact Entails.refl _
            refine SepWP.fold hfold_rand_7536 (by dsimp only [words4At]; sep_focus) ?_
            clear hrand_words hfold_rand_7536
            refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
            wp_apply
            wp_conv_pre => simp only [hencaps, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            apply SepWP.exists_elim; intro _
            refine SepWP.fold (stackAt_spqrSendCallee_from_extHook_of_eq (sp := sp) ?_)
              (by sep_focus) ?_
            · simp only [State.sp, arm64_norm, wp_norm, *]
            have h7536 : ((sp + 7536#64) ↦ₛ rand.toList) ⊢ memRegion (sp + 7536#64) 32 := by
              have h := pointsToBytes_entails_memRegion (sp + 7536#64) rand.toList
              rwa [List.Vector.toList_length] at h
            refine SepWP.fold h7536 (by sep_focus) ?_
            have hsplit_7536 : memRegion (sp + 7536#64) 32 =
                memRegion (sp + 7536#64) 1 ∗ memRegion (sp + 7537#64) 31 :=
              ProofLib.memRegion_split' rfl (by rw [BitVec.add_assoc]; rfl) (by decide)
            rw [hsplit_7536, ProofLib.memRegion_one (sp + 7536#64)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro _
            wp_steps
            exact ProofLib.SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

/-- Lift a `SepWP` segment ending at `lsρ spqrUnwrapFailedSym` into `SepWPp` for arbitrary `post`,
    `R`, and `oom`. -/
private theorem sepWPp_of_unwrap_failed {ext : String → Option (State → State)}
    (hunwrap_sym : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P R : SepProp} {φ : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hφ : ∀ sf : State, sf.trace = s0.trace → φ sf)
    (hseg : SepWP (spqrSendPlacedProg ext) (lsρ spqrUnwrapFailedSym) s P
      (fun sm _ => sm.status = .Running ∧ sm.trace = s0.trace)) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ sf⌝ ∗ anyHeap) ∗ R)) oom := by
  have hunwrap := spqrSend_unwrap_failed_placed (ext := ext) hunwrap_sym
  intro R' hm hL
  rcases hseg.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, _, htrm⟩ | ⟨_, hfalse⟩⟩
  · have hpan :
        SepWPp (spqrSendPlacedProg ext) ret sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ sf⌝ ∗ anyHeap) ∗ R)) oom :=
      SepWPp.panic hrunm (hpcm ▸ hunwrap) fun hmR => by
        have htrp : (Rust.panicked sm).trace = s0.trace := by
          simp only [Rust.panicked, htrm]
        exact Satisfies.mono
          (sepConj_mono_left (Entails.pure_right (hφ (Rust.panicked sm) htrp) (entails_anyHeap _)))
          hmR
    obtain ⟨sf, hsteps', hout⟩ := hpan R' hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Budget-threaded relocatable `[LibsignalPlacement]` execution of `.headerReceived` (`+1312 ->
    unwrap_failed`) when `K.encaps1 hdr rand = none`, with zero OOM branches under
    `FitsEvents M lim bSt headerReceived1aEvents`. -/
theorem step_headerReceived_1312_encaps1_none_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
      (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K)))
    (hunwrap_sym : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    (hFit : FitsEvents M lim bSt headerReceived1aEvents)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P_panic) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ A.pool lim bSt s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜P_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) oom :=
  sepWPp_of_unwrap_failed hunwrap_sym
    (fun _ htr => ⟨hp, htr ▸ List.prefix_refl s0.trace⟩)
    (step_headerReceived_1312_encaps1_none_sepWP_placed hA hZero hcoinsFill henc1 g auth epoch
      hdr_cap hdr_ptr hdr hhdr_lt sp cur tape h32 rand hrand_val hencaps d4056 hFit
      hcrl hsp_align hpc hrun hsp hx24 hx26 hx28 htrace hP)

/-- `FitsEnv M lim bSt HeaderReceived1aEnv` wrapper around
    `step_headerReceived_1312_encaps1_none_placed`. -/
theorem step_headerReceived_1312_encaps1_none_ofEnv_placed
    {K : MlKem} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {bSt : M.σ} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
      (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K)))
    (hunwrap_sym : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (hencaps : K.encaps1 hdr rand = none) (d4056 : BitVec 64)
    (hFit : FitsEnv M lim bSt HeaderReceived1aEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P_panic) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ A.pool lim bSt s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜P_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) oom :=
  step_headerReceived_1312_encaps1_none_placed hA hZero hcoinsFill henc1 hunwrap_sym g auth epoch
    hdr_cap hdr_ptr hdr hhdr_lt sp cur tape h32 rand hrand_val hencaps d4056
    (fitsEnv_headerReceived1a_iff.mp hFit) hp hcrl hsp_align hpc hrun hsp hx24 hx26 hx28
    htrace hP

/-- Wrapper around `step_headerReceived_1312_encaps1_none_placed` starting from
    `chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st)` and
    `statesSendPreArmScratch sp`, under `FitsEvents M lim bSt headerReceived1aEvents`. -/
theorem step_send_arm_headerReceived_encaps1_none_placed {F : ShaCompress} {K : MlKem}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {bSt : M.σ}
    {ctl : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
      (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K)))
    (hunwrap_sym : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked)
    {s0 s : State} (sp cur : BitVec 64) (tape : Bytes) (h32 : 32 ≤ tape.length)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none)
    (hFit : FitsEvents M lim bSt headerReceived1aEvents)
    {ret : BitVec 64} {P Frame R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P_panic) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt s ∗ spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
      statesSendPreArmScratch sp) ∗ Frame) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜P_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) oom := by
  refine sepWPp_of_unwrap_failed hunwrap_sym
    (fun _ htr' => ⟨hp, htr' ▸ List.prefix_refl s0.trace⟩) ?_
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  have hsplit_4192 : memRegion (sp + 4192#64) 504 =
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 456 :=
    ProofLib.memRegion_split' rfl (by rw [BitVec.add_assoc]; rfl) (by decide)
  have hsplit_1260 : memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 0x1260#64) 961 ∗ memRegion (sp + 5665#64) 1439 :=
    ProofLib.memRegion_split' rfl (by rw [BitVec.add_assoc]; rfl) (by decide)
  have hsplit_7136 : memRegion (sp + 7136#64) 400 =
      memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7168#64) 368 :=
    ProofLib.memRegion_split' rfl (by rw [BitVec.add_assoc]; rfl) (by decide)
  have hsplit_7536 : memRegion (sp + 7536#64) 400 =
      memRegion (sp + 7536#64) 32 ∗ memRegion (sp + 7568#64) 368 :=
    ProofLib.memRegion_split' rfl (by rw [BitVec.add_assoc]; rfl) (by decide)
  subst hP; unfold statesSendPreArmScratch
  apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 1312#64) hcrl
  refine SepWP.fold (chunkedStatesAt_headerReceived_expose (A := A.repAlloc) sp st) (by sep_focus) ?_
  rw [ProofLib.memRegion_eight (sp + 4056#64),
      hsplit_4192, hsplit_1260, hsplit_7136, hsplit_7536,
      show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056; apply SepWP.exists_elim; intro g
  apply SepWP.exists_elim; intro hdr_cap; apply SepWP.exists_elim; intro hdr_ptr
  refine SepWP.fold (Entails.refl ⌜st.uc.hdr.length < 2 ^ 63⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_lt => ?_
  apply SepWP.done hpc hrun; intro hcrl0
  exact step_headerReceived_1312_encaps1_none_sepWP_placed (ctl := ctl) hA hZero hcoinsFill henc1
    g st.uc.auth st.uc.epoch hdr_cap hdr_ptr st.uc.hdr hhdr_lt sp cur tape h32 rand rfl hencaps
    d4056 hFit
    (Frame := memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4240#64) 456 ∗ memRegion (sp + 5665#64) 1439 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗
      memRegion (sp + 7568#64) 368 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      polyDecoderAt A.repAlloc (sp + 2472#64) st.receiving_ek ∗
      memRegion (sp + 2872#64) 440 ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hcrl0 hsp_align hpc hrun hsp hx24 hx26 hx28 htr (by sep_ac_rfl)

/-- `FitsEnv M lim bSt HeaderReceived1aEnv` wrapper around
    `step_send_arm_headerReceived_encaps1_none_placed`. -/
theorem step_send_arm_headerReceived_encaps1_none_ofEnv_placed {F : ShaCompress} {K : MlKem}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {bSt : M.σ}
    {ctl : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym
      (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym
      (withVmPreserved (mlkemEncaps1Spec K)))
    (hunwrap_sym : (Rust.withPanics ext) spqrUnwrapFailedSym = some Rust.panicked)
    {s0 s : State} (sp cur : BitVec 64) (tape : Bytes) (h32 : 32 ≤ tape.length)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none)
    (hFit : FitsEnv M lim bSt HeaderReceived1aEnv)
    {ret : BitVec 64} {P Frame R : SepProp} {P_panic : Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P_panic) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim bSt s ∗ spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
      statesSendPreArmScratch sp) ∗ Frame) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜P_panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) oom :=
  step_send_arm_headerReceived_encaps1_none_placed hA hZero hcoinsFill henc1 hunwrap_sym
    sp cur tape h32 st hencaps (fitsEnv_headerReceived1a_iff.mp hFit)
    hp hcrl hpc hrun hsp hsp_align htr hx24 hx26 hx28 hP

end HeaderReceivedPanicPlaced

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
