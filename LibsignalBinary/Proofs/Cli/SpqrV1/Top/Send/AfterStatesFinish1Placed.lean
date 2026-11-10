/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlaced
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import ProofLib.SepLogic.WPp

/-!
# Relocatable Phase 4 (Part 1) of `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Proves return struct assembly (`+6216..+6328`), epoch secret deallocation (`+6328..+6360`),
and non-looping `PqRatchetState` outer field drops (`+6360..`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.SpqrV1
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L22
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero spqrSendPlacedEntry
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.Top.Send.extractLsb_lo_append64
  CryptoVerification.SpqrV1.Top.Send.extractLsb_hi_append64
  ite_zero32_self ite_zero64_self

/-- Relocatable `DeallocOkExt`: `HookSat` for `__rustc::__rust_dealloc` under `Rust.withPanics ext`. -/
abbrev DeallocOkExtPlaced (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)

theorem spqrSend_dealloc_sub_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExtPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
  spqr_hook_ok_of_mem hdealloc

/-! ## 1. Tail-Deallocation Helpers at `+4592` and `+4596` -/

/-- `spqrSendPlacedEntry + 4596#64 -> spqrSendPlacedEntry + 4600#64` (1 instruction):
    calls `bl __rust_dealloc` with `(x0 = ptr, x1 = sz, x2 = align)` and lands at `+4600`
    preserving `x23`. -/
theorem step_tail_dealloc_31a50_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s : State) (ptr : BitVec 64) (sz align : Nat) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4596#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      ((A.live ptr sz align ∗ memRegion ptr sz) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_raw (ptr, sz, align)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by ac_rfl)⟩

/-- `spqrSendPlacedEntry + 4592#64 -> spqrSendPlacedEntry + 4600#64` (2 instructions):
    executes `mov w2, #1; bl __rust_dealloc` with `(x0 = ptr, x1 = cap)` and lands at `+4600`
    preserving `x23`. -/
theorem step_tail_dealloc_31a4c_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s : State) (ptr cap x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4592#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      ((A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_raw (ptr, cap.toNat, 1)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by ac_rfl)⟩

/-! ## 2. Return Struct Assembly (`+6216..+6328`) & Epoch Secret Dealloc (`+6328..+6360`) -/

/-- `spqrSendPlacedEntry + 6216#64 -> spqrSendPlacedEntry + 6328#64` (28 instructions = 112 bytes):
    Assembles `spqrSendResultAt A ret (some (stBytes, key, msgBytes))` at `ret` (`x19`) from
    `vecU8 A (s.sp + 1424#64) stBytes`, `vecU8 A (s.sp + 4080#64) msgBytes`, and
    `optMsgKeySlotsAt A s.sp key`, reloads `x19 = v_20` from `[s.sp + 32#64]`, and lands at `+6328`. -/
theorem step_send_build_result_320a4_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
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
        vecU8 A (s.sp + 1424#64) stBytes ∗
        vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗
        ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗
        memRegion (s.sp + 7136#64) 16 ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = v_20 ∧
        sf.readReg64 .x21 = x21 ∧
        sf.readReg64 .x23 = x23 ∧
        sf.readReg64 .x25 = x25 ∧
        sf.readReg64 .x27 = x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗
          memRegion (s.sp + 24#64) 24 ∗
          memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗
          memRegion (s.sp + 4192#64) 48 ∗
          memRegion (s.sp + 7136#64) 16 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  have hst_exp := vecU8_expose_words A (s.sp + 1424#64) stBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_exp
  have hmsg_exp := vecU8_expose_words A (s.sp + 4080#64) msgBytes
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
  have hret_st := words_to_vecU8 A ret stCap stPtr stBytes
  have hret_msg := words_to_vecU8 A (ret + 24#64) msgCap msgPtr msgBytes
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
    dsimp only [optMsgKeySlotsAt]
    wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_words3' (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_pull_exists
    wp_steps
    have hret_key := optKeyAt_some_of_words A (ret + 48#64) mkCap mkPtr k
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 32#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    refine SepWP.focus_weaken hret_st (by sep_focus) ?_
    refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
    refine SepWP.focus_weaken hret_key (by sep_focus) ?_
    refine SepWP.focus_weaken
      (sendResultAt_some_of_parts A ret stBytes msgBytes (some k) hmsg_len) (by sep_focus) ?_
    refine SepWP.focus_weaken h8 (by sep_focus) ?_
    refine SepWP.focus_weaken h24 (by sep_focus) ?_
    refine SepWP.focus_weaken h1424 (by sep_focus) ?_
    refine SepWP.focus_weaken h4080 (by sep_focus) ?_
    refine SepWP.focus_weaken h4192 (by sep_focus) ?_
    refine SepWP.focus_weaken h7136 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | none =>
    dsimp only [optMsgKeySlotsAt]
    wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_split_8_16 (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_pull_exists
    refine SepWP.focus_weaken (vecU8Heap_entails_dealloc A mkCap mkPtr []) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    have hret_key := optKeyAt_none_of_word A (ret + 48#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    by_cases hc0 : (mkCap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : mkCap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken
        (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken (words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 0#64) (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · rw [send_stackAt_callee_eq_allocHook s.sp]
      wp_steps
      wp_call hdealloc_raw (mkPtr, mkCap.toNat, 1)
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken
        (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken h24 (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

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
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        sf.readReg64 .x25 = x25 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ P)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rcases hflag with hx21 | hx19
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
  · have hgpr19 : BitVec.truncate 32 (s.readReg64 (Reg.gpr 19#5)) = 0#32 := hx19
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩

/-! ## 3. Inlined `drop_in_place::<PqRatchetState>` (`+6360..`) Part 1 -/

theorem seq_clean_lscl {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post := by
  refine sepWP_seq_lscl hcl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hPm, hQ⟩ hcl_m
  exact SepWP.weaken_pre hPm (h2 sm hpc hrun hcl_m hQ)

theorem spqrSend_dropProtoSpqrChain_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExtPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeLoaded lsmpl (dropProtoSpqrChainSpec A)) :=
  ls_subroutine_ok_of_block
    (subroutine_ok_withLsCodeLoaded_of_plain
      (CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_placed_ok (spqr_hook_ok_of_mem hdealloc)))
    (by decide) (by decide) (by decide)

/-- `spqrSendPlacedEntry + 6360#64 -> spqrSendPlacedEntry + 6408#64` (12 instructions = 48 bytes):
    Drops `vn : Option VersionNegotiationPB` at `s.sp + 4704#64` (`sp + 0x1260`) and
    `ch : Option ChainPB` at `s.sp + 4752#64` (`sp + 0x1290`, calling `lsmpl.base 439`
    when `ch = some _`), setting `x19 = s.sp + 4704#64` and turning `[s.sp + 4704 .. s.sp + 4832)`
    into `memRegion (s.sp + 4704#64) 128`. -/
theorem step_send_drop_vn_chain_32134_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s : State) (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (x23 : BitVec 64) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 6360#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : (s.readReg64 .x25 + 1#64 == 0#64) = !ch.isSome) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 6408#64) s
      (optVersionNegotiationPBAt A (s.sp + 4704#64) vn ∗
        optChainPBAt A (s.sp + 4752#64) ch ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.sp + 4704#64 ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4704#64) 128 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  have hchain_raw := spqrSend_dropProtoSpqrChain_ok_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  simp only [withLsCodeLoaded, dropProtoSpqrChainSpec] at hchain_raw
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, chainPBSize,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hchain_raw ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_427).base + 6392#64)
    (P_mid := memRegion (s.sp + 4704#64) 48 ∗
      optChainPBAt A (s.sp + 4752#64) ch ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧
      sm.readReg64 .x19 = s.sp + 4704#64 ∧
      sm.readReg64 .x23 = x23 ∧
      sm.readReg64 .x25 = s.readReg64 .x25 ∧
      calleeSavedVRegs sm = calleeSavedVRegs s)
    ?_ ?_
  · cases vn with
    | none =>
      dsimp only [optVersionNegotiationPBAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone48 := optVersionNegotiationPBAt_none_entails_memRegion_48 (s.sp + 4704#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
      refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.of_eq (by ac_rfl),
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    | some vnVal =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken
        (versionNegotiationPBAt_entails_dealloc A (s.sp + 4704#64) vnVal) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩
      wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
      have hhdr48 := vnHeader_entails_memRegion_48 (s.sp + 4704#64) cap ptr
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq
        wp_steps
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        rw [send_stackAt_callee_eq_allocHook s.sp]
        wp_steps
        wp_call hdealloc_raw (ptr, cap.toNat, 1)
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hx19_1, hx23_1, hx25_1, hvregs1⟩
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
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some chVal =>
      simp only [Option.isSome_some, Bool.not_true] at hx25
      have hx25_1' : ¬((s1.readReg64 .x25 + 1#64 == 0#64) = true) := by
        rw [hx25_1, hx25]; decide
      dsimp only [optChainPBAt]
      rw [stackAt_spqrSendCallee_eq_dropStack48 s.sp]
      wp_steps
      wp_call hchain_raw ⟨s.sp + 4752#64, chVal⟩
      rw [hsp1]
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

def spqrSendDropJumpTablePlacedExpanded : SepProp :=
  ((lsρ spqrSendRoSym + 44#64) ↦₈ᵣ 0xbb#8) ∗ ((lsρ spqrSendRoSym + 45#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 46#64) ↦₈ᵣ 0x00#8) ∗ ((lsρ spqrSendRoSym + 47#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 48#64) ↦₈ᵣ 0x7b#8) ∗ ((lsρ spqrSendRoSym + 49#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 50#64) ↦₈ᵣ 0x00#8) ∗ ((lsρ spqrSendRoSym + 51#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 52#64) ↦₈ᵣ 0x3c#8) ∗ ((lsρ spqrSendRoSym + 53#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 54#64) ↦₈ᵣ 0xc8#8) ∗ ((lsρ spqrSendRoSym + 55#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 56#64) ↦₈ᵣ 0xe7#8) ∗ ((lsρ spqrSendRoSym + 57#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 58#64) ↦₈ᵣ 0xa4#8) ∗ ((lsρ spqrSendRoSym + 59#64) ↦₈ᵣ 0x00#8) ∗
  ((lsρ spqrSendRoSym + 60#64) ↦₈ᵣ 0x25#8) ∗ ((lsρ spqrSendRoSym + 61#64) ↦₈ᵣ 0x01#8) ∗
  ((lsρ spqrSendRoSym + 62#64) ↦₈ᵣ 0x66#8) ∗ ((lsρ spqrSendRoSym + 63#64) ↦₈ᵣ 0x00#8)

theorem spqrSendDropJumpTablePlacedAt_eq_expanded :
    spqrSendDropJumpTablePlacedAt = spqrSendDropJumpTablePlacedExpanded := by
  unfold spqrSendDropJumpTablePlacedAt spqrSendDropJumpTableBytes spqrSendDropJumpTablePlacedExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` (4 instructions = 16 bytes)
    when `st.inner = none` (`0xfffffffffffffffd#64` = `none3Cap'`). -/
theorem step_send_drop_inner_none_32164_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoPqRatchetInnerAt A (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoPqRatchetInnerAt,
    none3Cap', BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hnone224 := optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s.sp + 4832#64)
  dsimp only [none3Cap'] at hnone224
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` (4 instructions = 16 bytes)
    when `st.inner = some (.v1 ⟨none⟩)` (`0xfffffffffffffffe#64` = `none2Cap`). -/
theorem step_send_drop_inner_v1_none_32164_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    none2Cap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hnone224 := optProtoInnerState_none_entails_224 (s.sp + 4832#64)
  dsimp only [none2Cap] at hnone224
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `spqrSendPlacedEntry + 6408#64 -> spqrSendPlacedEntry + 4600#64` for
    `st.inner = some (.v1 ⟨some (.keysUnsampled st)⟩)` (`idx = 0`, target `spqrSendPlacedEntry + 7220#64`). -/
theorem step_send_drop_inner_keysUnsampled_32164_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced A ext)
    (s : State) (st : V1State.Chunked.KeysUnsampled) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.keysUnsampled st)) ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          spqrSendDropJumpTablePlacedAt ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw := spqrSend_dealloc_sub_ok_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  rw [spqrSendDropJumpTablePlacedAt_eq_expanded]
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedKeysUnsampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  let a := s.sp + 4832#64
  have hjoin224 : (a ↦₆₄ 0x8000000000000000#64) ∗
      memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 160 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000000#64 56 160 64#64
      (BitVec.add_assoc a 8#64 56#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin224
  cases huc : st.uc with
  | none =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, spqrSendDropJumpTablePlacedExpanded]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (s.sp + 4840#64)
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some u =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
    cases hauth : u.auth with
    | none =>
      have hnone8 := optProtoAuthenticatorAt_8_none_entails_memRegion_56 A (s.sp + 4832#64) u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone8
      rw [optProtoAuthenticatorAt_none]
      dsimp only [spqrSendDropJumpTablePlacedExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      refine SepWP.focus_weaken hnone8 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4832#64 + 8#64) auth)
        (by sep_focus) ?_
      wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_8_eq]
      wp_focus_pure; intro hga_lt
      have hne_none2 := Drop.cap_add_two_beq_zero_false hga_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hga_lt
      have hhdr56 := auth8HeadersAt_entails_memRegion_56 (s.sp + 4832#64) ga u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
      refine seq_clean (mid := (blkPl_427).base + 7256#64)
        (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000000#64) ∗
          ((auth8HeadersAt (s.sp + 4832#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            ((s.sp + 4888#64) ↦₆₄ u.epoch)) ∗
          memRegion (s.sp + 4896#64) 160 ∗
          spqrSendDropJumpTablePlacedExpanded ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ sm.readReg64 .x23 = x23 ∧ calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · dsimp only [auth8HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTablePlacedExpanded]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hx23_1, hvregs1⟩
        have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
        dsimp only [auth8HeadersAt, vecCapPtrDealloc]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
          rw [hsp1]
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

end CryptoVerification.Cli.SpqrV1.Top.Send
