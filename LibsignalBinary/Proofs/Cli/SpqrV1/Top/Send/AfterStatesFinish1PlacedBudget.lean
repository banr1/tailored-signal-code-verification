/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Phase 4 (Part 1) of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Threads `RustCliAllocBudget` and `FreeOnlyEvs` through return struct assembly (`+6216..+6328`),
epoch secret deallocation (`+6328..+6360`), and non-looping `PqRatchetState` outer field drops.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withMemEq libsignalSessionCode
   ls_subroutine_ok_of_block lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain
   withLsCodeLoaded withMemEq)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendDropJumpTablePlacedAt spqrSendDropJumpTablePlacedAt_eq_expanded
   spqrSendDropJumpTablePlacedExpanded spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (Bytes ChainPB VersionNegotiationPB)
open CryptoVerification.LibsignalTripleRatchet (spqrSendResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (auth8HeadersAt auth8HeadersAt_entails_memRegion_56 cap_ne_zero_lt_one_false
   cap_ne_zero_slt_one_false none2Cap none2Cap_add_two_beq_zero none3Cap'
   optChainPBAt_none_entails_memRegion_80 optProtoAuthenticatorAt_8_none_entails_memRegion_56
   optProtoAuthenticatorAt_none optProtoAuthenticatorAt_some optProtoInnerStateAt
   optProtoInnerState_none_entails_224 optProtoPqRatchetInnerAt
   optProtoPqRatchetInnerAt_none_entails_memRegion_224 optProtoUnchunkedKeysUnsampledAt
   optProtoUnchunkedNoHeaderReceivedAt optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
   optVersionNegotiationPBAt_none_entails_memRegion_48 protoAuthenticatorAt_entails_dealloc
   protoChunkedKeysUnsampledAt protoInnerStateAt protoUnchunkedKeysUnsampledAt
   tag_and_two_regions_entails_224 twoVecHeadersAt_8_eq vecCapPtrDealloc
   versionNegotiationPBAt_entails_dealloc vnHeader_entails_memRegion_48)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero)
open CryptoVerification.SpqrV1.ProtoRepr
  (chainPBSize optChainPBAt optVersionNegotiationPBAt v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.Top.Send
  (ite_zero32_self ite_zero64_self memRegion_16_words2 memRegion_24_split_8_16
   memRegion_24_words3' memRegion_48_words6 memRegion_72_split_48_24 optKeyAt_none_of_word
   optKeyAt_some_of_words optMsgKeySlotsAt sendResultAt_some_of_parts
   send_stackAt_callee_eq_allocHook spqrSendCalleeStack stackAt_spqrSendCallee_eq_dropStack48
   vecU8Heap_entails_dealloc vecU8_expose_words words2_to_memRegion_16 words3_to_memRegion_24'
   words6_to_memRegion_48 words_to_vecU8)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlacedBudget (drop_proto_spqr_chain_placed)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)

variable [LibsignalPlacement]

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendDropJumpTablePlacedExpanded spqrSendDropJumpTablePlacedAt_eq_expanded)

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32 LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.extractLsb_lo_append64
  CryptoVerification.SpqrV1.Top.Send.extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

/-- Budget-threaded relocatable `DeallocOkExt`: `HookSat` for `__rustc::__rust_dealloc` under `Rust.withPanics ext`. -/
abbrev DeallocOkExtPlaced (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
    (rustCliDeallocBudgetSpec M A lim)

theorem spqrSend_dealloc_sub_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hdealloc

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
private theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (hcl : LibsignalCodeLoaded pl m)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hm, hpre⟩ := extract_withMemEq hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

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

/-! ## 1. Tail-Deallocation Helpers at `+4592` and `+4596` -/

/-- `spqrSendPlacedEntry + 4596#64 -> spqrSendPlacedEntry + 4600#64` (1 instruction):
    calls `bl __rust_dealloc` with `(x0 = ptr, x1 = sz, x2 = align)` and lands at `+4600`
    preserving `x23`. -/
theorem step_tail_dealloc_31a50_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (st : M.σ) (ptr : BitVec 64) (sz align : Nat) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4596#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      ((A.repAlloc.live ptr sz align ∗ memRegion ptr sz) ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_fo (ptr, sz, align, st)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨rustDeallocEvents sz align, LibsignalBinary.Heap.FreeOnlyEvs.singleton align sz,
      by simp only [wp_norm, arm64_norm, *],
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by sep_ac_rfl)⟩

/-- `spqrSendPlacedEntry + 4592#64 -> spqrSendPlacedEntry + 4600#64` (2 instructions):
    executes `mov w2, #1; bl __rust_dealloc` with `(x0 = ptr, x1 = cap)` and lands at `+4600`
    preserving `x23`. -/
theorem step_tail_dealloc_31a4c_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (st : M.σ) (ptr cap x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4592#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      ((A.repAlloc.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_fo (ptr, cap.toNat, 1, st)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨rustDeallocEvents cap.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 cap.toNat,
      by simp only [wp_norm, arm64_norm, *],
      by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 2. Return Struct Assembly (`+6216..+6328`) & Epoch Secret Dealloc (`+6328..+6360`) -/

/-- `spqrSendPlacedEntry + 6216#64 -> spqrSendPlacedEntry + 6328#64` (28 instructions = 112 bytes):
    Assembles `spqrSendResultAt A.repAlloc ret (some (stBytes, key, msgBytes))` at `ret` (`x19`) from
    `vecU8 A.repAlloc (s.sp + 1424#64) stBytes`, `vecU8 A.repAlloc (s.sp + 4080#64) msgBytes`, and
    `optMsgKeySlotsAt A.repAlloc s.sp key`, reloads `x19 = v_20` from `[s.sp + 32#64]`, and lands at `+6328`. -/
theorem step_send_build_result_320a4_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
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
    (hret_align : (ret &&& 7#64 == 0#64) = true)
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

/-- `spqrSendPlacedEntry + 6328#64 -> spqrSendPlacedEntry + 6360#64` (4 instructions = 16 bytes):
    When `x21 = noneCap ∨ s.readReg32 .x19 = 0#32`, branches directly to `+6360`. -/
theorem step_send_epoch_dealloc_32114_placed
    {ext : String → Option (State → State)}
    (s : State) (x23 x25 : BitVec 64) (P : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6328#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x19 = 0#32) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 6360#64) s P
      (fun sf Q =>
        VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        sf.readReg64 .x25 = x25 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ P)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rcases hflag with hx21 | hx19
  · by_vm_steps (
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩)
  · have hgpr19 : BitVec.truncate 32 (s.readReg64 (Reg.gpr 19#5)) = 0#32 := hx19
    by_vm_steps (
      wp_steps
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩)

/-! ## 3. Inlined `drop_in_place::<PqRatchetState>` (`+6360..`) Part 1 -/

theorem spqrSend_dropProtoSpqrChain_ok_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeLoaded lsmpl (dropProtoSpqrChainSpec M A lim)) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_proto_spqr_chain_placed hdealloc))
    (by decide) (by decide) (by decide)

/-- `spqrSendPlacedEntry + 6360#64 -> spqrSendPlacedEntry + 6408#64` (12 instructions = 48 bytes):
    Drops `vn : Option VersionNegotiationPB` at `s.sp + 4704#64` (`sp + 0x1260`) and
    `ch : Option ChainPB` at `s.sp + 4752#64` (`sp + 0x1290`, calling `lsmpl.base 439`
    when `ch = some _`), setting `x19 = s.sp + 4704#64` and turning `[s.sp + 4704 .. s.sp + 4832)`
    into `memRegion (s.sp + 4704#64) 128`. -/
theorem step_send_drop_vn_chain_32134_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (st : M.σ) (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6360#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : (s.readReg64 .x25 + 1#64 == 0#64) = !ch.isSome) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 6408#64) s
      (optVersionNegotiationPBAt A.repAlloc (s.sp + 4704#64) vn ∗
        optChainPBAt A.repAlloc (s.sp + 4752#64) ch ∗
        A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x19 = s.sp + 4704#64 ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4704#64) 128 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  have hchain_ok := spqrSend_dropProtoSpqrChain_ok_placed hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo hchain_ok ⊢
  refine sepWP_seq_mid_lscl
    (mid := (blkPl_427).base + 6392#64)
    (Mid := fun sm Pm =>
      ∃ evs₁ : List AllocEvent,
        FreeOnlyEvs evs₁ ∧
        AllocCallPreserved s sm ∧
        sm.sp = s.sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.sp + 4704#64 ∧
        sm.readReg64 .x23 = x23 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ memRegion (s.sp + 4704#64) 48 ∗
          optChainPBAt A.repAlloc (s.sp + 4752#64) ch ∗
          A.pool lim (M.stepEvents evs₁ st) sm ∗
          stackAt s.sp spqrSendCalleeStack ∗ Frame))
    hcl ?_ ?_
  · cases vn with
    | none =>
      dsimp only [optVersionNegotiationPBAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone48 := optVersionNegotiationPBAt_none_entails_memRegion_48 (s.sp + 4704#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
      refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          Entails.of_eq (by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
            try sep_ac_rfl)⟩
    | some vnVal =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken
        (versionNegotiationPBAt_entails_dealloc A.repAlloc (s.sp + 4704#64) vnVal) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩
      wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
      have hhdr48 := vnHeader_entails_memRegion_48 (s.sp + 4704#64) cap ptr
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq
        wp_steps
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            Entails.of_eq (by
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
                LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
              try sep_ac_rfl)⟩
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        rw [send_stackAt_callee_eq_allocHook s.sp]
        wp_steps
        wp_call hdealloc_fo (ptr, cap.toNat, 1, st)
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨rustDeallocEvents cap.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 cap.toNat,
            by simp only [wp_norm, arm64_norm, *],
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            Entails.of_eq (by sep_ac_rfl)⟩
  · intro s1 P1 hpc1 hrun1 hcl1
      ⟨evs₁, hevs₁, hacp₁, hsp1, htr1, hx19_1, hx23_1, hx25_1, hvregs1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hjoin128 : memRegion (s.sp + 4704#64) 48 ∗ memRegion (s.sp + 4752#64) 80 ⊢
        memRegion (s.sp + 4704#64) 128 := by
      have h4752 : (s.sp + 4704#64) + 48#64 = s.sp + 4752#64 := by bv_omega
      rw [← h4752, ProofLib.memRegion_split (s.sp + 4704#64) 48 80 (by decide)]
      exact Entails.refl _
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    cases ch with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hx25
      have hx25_1' : (s1.readReg64 .x25 + 1#64 == 0#64) = true := by rw [hx25_1, hx25]
      dsimp only [optChainPBAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone80 := optChainPBAt_none_entails_memRegion_80 (s.sp + 4752#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨evs₁, hevs₁, hacp₁.trans (by wp_norm_goal),
          by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
          (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x19).trans hx19_1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
          Entails.of_eq (by
            simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
            try sep_ac_rfl)⟩
    | some chVal =>
      simp only [Option.isSome_some, Bool.not_true] at hx25
      have hx25_1' : ¬((s1.readReg64 .x25 + 1#64 == 0#64) = true) := by
        rw [hx25_1, hx25]; decide
      have hchain_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hcl1 hchain_ok
      simp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget.dropProtoSpqrChainSpec] at hchain_mem
      dsimp only [chainPBSize, BitVec.ofNat_eq_ofNat] at hchain_mem
      dsimp only [optChainPBAt]
      rw [← hsp1, stackAt_spqrSendCallee_eq_dropStack48 s1.sp]
      wp_steps
      wp_call hchain_mem (⟨s1.sp + 4752#64, chVal⟩, M.stepEvents evs₁ st)
      rw [hsp1]
      have hacp_ch : AllocCallPreserved s1 sf := by simp only [wp_norm, arm64_norm, *]
      have hevs_ch : FreeOnlyEvs w := by assumption
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨evs₁ ++ w, LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ hevs_ch, hacp₁.trans hacp_ch,
          by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
          (by wp_norm_goal : _ = s1.sp).trans hsp1,
          (by wp_norm_goal : _ = s1.readReg64 .x19).trans hx19_1,
          (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
          (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1, ?_⟩
      rw [M.stepEvents_append]
      exact Entails.of_eq (by sep_ac_rfl)

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` (4 instructions = 16 bytes)
    when `st.inner = none` (`0xfffffffffffffffd#64` = `none3Cap'`). -/
theorem step_send_drop_inner_none_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoPqRatchetInnerAt A.repAlloc (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
    none3Cap', BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone224 := optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s.sp + 4832#64)
    dsimp only [none3Cap'] at hnone224
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
    refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by sep_ac_rfl)⟩)

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` (4 instructions = 16 bytes)
    when `st.inner = some (.v1 ⟨none⟩)` (`0xfffffffffffffffe#64` = `none2Cap`). -/
theorem step_send_drop_inner_v1_none_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        VmPreserved s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    none2Cap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone224 := optProtoInnerState_none_entails_224 (s.sp + 4832#64)
    dsimp only [none2Cap] at hnone224
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
    refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by sep_ac_rfl)⟩)

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.keysUnsampled ku)⟩)` (`idx = 0`, target `spqrSendPlacedEntry + 7220#64`). -/
theorem step_send_drop_inner_keysUnsampled_32164_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s : State) (bst : M.σ) (ku : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A.repAlloc (s.sp + 4832#64) (some (.keysUnsampled ku)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst s ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          sf.status = .Running ∧
          sf.trace = s.trace ∧
          sf.sp = s.sp ∧
          sf.readReg64 .x23 = x23 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
            spqrSendDropJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly (spqrSend_dealloc_sub_ok_placed hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedKeysUnsampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
  let a := s.sp + 4832#64
  have hjoin224 : (a ↦₆₄ 0x8000000000000000#64) ∗
      memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 160 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000000#64 56 160 64#64
      (BitVec.add_assoc a 8#64 56#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin224
  cases huc : ku.uc with
  | none =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, spqrSendDropJumpTablePlacedExpanded]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (s.sp + 4840#64)
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal,
        Entails.of_eq (by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
            LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
          sep_ac_rfl)⟩
  | some u =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
    cases hauth : u.auth with
    | none =>
      have hnone8 := optProtoAuthenticatorAt_8_none_entails_memRegion_56 A.repAlloc (s.sp + 4832#64) u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone8
      rw [optProtoAuthenticatorAt_none]
      dsimp only [spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      refine SepWP.focus_weaken hnone8 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal,
          Entails.of_eq (by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
              LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
            try sep_ac_rfl)⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken
        (protoAuthenticatorAt_entails_dealloc A.repAlloc (s.sp + 4832#64 + 8#64) auth)
        (by sep_focus) ?_
      wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_8_eq]
      wp_focus_pure; intro hga_lt
      have hne_none2 := CryptoVerification.SpqrV1.Drop.cap_add_two_beq_zero_false hga_lt
      have hne_none1 := CryptoVerification.SpqrV1.Drop.cap_add_one_beq_zero_false hga_lt
      have hhdr56 := auth8HeadersAt_entails_memRegion_56 (s.sp + 4832#64) ga u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
      refine SepWP.seq
        (mid := (blkPl_427).base + 7256#64)
        (Mid := fun sm Pm =>
          ∃ evs₁ : List AllocEvent,
            FreeOnlyEvs evs₁ ∧
            AllocCallPreserved s sm ∧
            sm.sp = s.sp ∧ sm.trace = s.trace ∧
            sm.readReg64 .x23 = x23 ∧
            calleeSavedVRegs sm = calleeSavedVRegs s ∧
            (Pm ⊢ ((s.sp + 4832#64) ↦₆₄ 0x8000000000000000#64) ∗
              ((auth8HeadersAt (s.sp + 4832#64) ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                ((s.sp + 4888#64) ↦₆₄ u.epoch)) ∗
              memRegion (s.sp + 4896#64) 160 ∗
              spqrSendDropJumpTablePlacedExpanded ∗
              A.pool lim (M.stepEvents evs₁ bst) sm ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame))
        ?_ ?_
      · dsimp only [auth8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
          spqrSendDropJumpTablePlacedExpanded]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              Entails.of_eq (by
                simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
                  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState, LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64]
                sep_ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, bst)
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨rustDeallocEvents ga.v1.cap.toNat 1, LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v1.cap.toNat,
              by simp only [wp_norm, arm64_norm, *],
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by simp only [wp_norm, arm64_norm, *],
              Entails.of_eq (by sep_ac_rfl)⟩
      · intro s1 P1 hpc1 hrun1 ⟨evs₁, hevs₁, hacp₁, hsp1, htr1, hx23_1, hvregs1, hP1⟩
        refine SepWP.weaken_pre hP1 ?_
        have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
        dsimp only [auth8HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨evs₁, hevs₁, hacp₁.trans (by wp_norm_goal),
              by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              (by wp_norm_goal : _ = calleeSavedVRegs s1).trans hvregs1,
              Entails.of_eq (by
                simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC, LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
                  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64])⟩
        · rw [← hsp1, send_stackAt_callee_eq_allocHook s1.sp]
          wp_steps
          wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, M.stepEvents evs₁ bst)
          rw [hsp1]
          have hacp₂ : AllocCallPreserved s1 sf := by simp only [wp_norm, arm64_norm, *]
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨evs₁ ++ rustDeallocEvents ga.v2.cap.toNat 1,
              LibsignalBinary.Heap.FreeOnlyEvs.append hevs₁ (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat),
              hacp₁.trans hacp₂,
              by wp_norm_goal, (by wp_norm_goal : _ = s1.trace).trans htr1,
              (by wp_norm_goal : _ = s1.sp).trans hsp1,
              (by wp_norm_goal : _ = s1.readReg64 .x23).trans hx23_1,
              (by simp only [wp_norm, arm64_norm, *] : _ = calleeSavedVRegs s1).trans hvregs1, ?_⟩
          rw [M.stepEvents_append]
          exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
