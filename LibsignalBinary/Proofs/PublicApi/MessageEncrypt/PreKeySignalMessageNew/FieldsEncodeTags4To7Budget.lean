/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Field Encoding: Tags 4–7

Relocatable `[LibsignalPlacement]` encoding steps for protobuf tags 4–7 (`+0x35c..+0x450`) within
the pre-allocated `serialized` capacity under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSessionApi.Prost (uint32Field bytesField)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCodeLoaded
   blkPC_10 blkPl_10 lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsMemcpySym
   ls_hook_ok_of_mem lsρ)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost PreKeyMsgGhostWf preKeyMsgSubStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
  (PreKeyMsgTagRegs serPrefix3 serPrefix4 serPrefix5 serPrefix6 serPrefix7 serPrefix_lengths_le
   prost_key_4_2 prost_key_5_0 prost_key_6_0 prost_key_7_0
   prost_uint32Field_some prost_bytesField_some
   vecU8Buf vecSliceRest vecU8Buf_eq_open_one vecU8Buf_snoc_eq
   vecU8Buf_eq_open_slice vecU8Buf_append_eq boxU8Buf_nonempty_eq
   cap_beq_len_false bv_len_add_one
   cap_sub_len_ult_false cap_sub_len_ule_true
   fp_sub_48_eq fp_sub_48_sub_eq fp_sub_40_eq fp_sub_32_eq)
open scoped CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.EncodeVarintNorm
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
  (preKeyMsg_memcpy_placed_ok)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
  (encodeVarintNoGrowPlacedSpec encodeVarintNoGrow_placed_ok encodeVarintNoGrow_placed_ok_sessionShim
   step_call_encVarint_placed_of_ok step_call_memcpy_placed_of_ok)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

private theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl h

private theorem bv_len_beq_zero_false' {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have h0 : (BitVec.ofNat 64 n).toNat = 0 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h0
  omega

/-! ## Tag 4 (`message`, `+0x35c..+0x3b8`) -/

theorem step_preKeyMsg_tag4_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 860#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 952#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hmsg_lt : x.msg.serialized.length < 2 ^ 64 := by
    have : x.msg.serialized.length ≤ (serPrefix4 x).length := by
      simp [serPrefix4, bytesField]; omega
    omega
  have hser4 : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)) ++
      x.msg.serialized = serPrefix4 x := by
    rw [serPrefix4, prost_bytesField_some 4 x.msg.serialized hmsg_lt, prost_key_4_2]
    simp only [← List.append_assoc, List.singleton_append]
  have h4_len : (serPrefix4 x).length = (serPrefix3 x).length + 1 +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length + x.msg.serialized.length := by
    rw [← hser4, List.length_append, List.length_append, List.length_cons]; omega
  have hlt3 : (serPrefix3 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq3 := cap_beq_len_false hlt3
  have hle_var : (serPrefix3 x ++ [34#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hle_slice : (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
      x.msg.serialized.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix3 x) hlt3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
  wp_steps_sync_pool ((blkPl_10).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix3 x) 34#8 hlt3
  refine step_call_encVarint_placed_of_ok henc0
    (BitVec.ofNat 64 x.msg.serialized.length) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 900#64) (serPrefix3 x ++ [34#8]) st tr s hle_var (by omega)
    (F := (sp ↦₆₄ g.msgCopyPtr) ∗ boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗ F) hcl0
    (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by
      rw [bv_len_add_one (serPrefix3 x) 34#8, ← hsnoc]
      sep_ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx27_1 : sf1.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  by_cases hmsg_nil : x.msg.serialized = []
  · have hser4_nil : serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length) =
        serPrefix4 x := by
      simpa [hmsg_nil] using hser4
    have hmsg_bv0 : BitVec.ofNat 64 x.msg.serialized.length = 0#64 := by simp [hmsg_nil]
    clear hmsg_nil h4_len hser4
    rw [hser4_nil] at hult1 hule1 ⊢
    rw [hmsg_bv0] at hx27_1 hult1 hule1
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 952#64)
    wp_steps_sync_pool ((blkPl_41).base + 952#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hclf2 => ?_
    refine SepWPp.congr_pre ?_
      (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hclf2
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl
  · have hmsg_pos : 0 < x.msg.serialized.length := List.length_pos_of_ne_nil hmsg_nil
    have hmsg_beq := bv_len_beq_zero_false' hmsg_pos hmsg_lt
    have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmsg_lt]
    rw [vecU8Buf_eq_open_slice A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
      x.msg.serialized.length hle_slice hcap_pos,
      boxU8Buf_nonempty_eq A.repAlloc g.msgCopyPtr x.msg.serialized hmsg_nil]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hclf1' => ?_
    refine step_call_memcpy_placed_of_ok hmc
      (g.serPtr + BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      g.msgCopyPtr sp ((blkPl_41).base + 944#64)
      (BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length)
      (BitVec.ofNat 64 x.model.serialized.length)
      x.msg.serialized tr s
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄
          BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
        vecSliceRest A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
          x.msg.serialized.length ∗
        A.pool lim st _ ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.msgCopyPtr ≠ 0#64 ∧ x.msg.serialized.length < 2 ^ 63⌝ ∗
          A.repAlloc.live g.msgCopyPtr x.msg.serialized.length 1) ∗ F)
      hclf1' (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign1)
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by sep_ac_rfl)
      fun sf2 hpcf2 hrunf2 hspf2 htrf2 hvm2 hclf2 hregs2 hx23_2 hx26_2 => ?_
    have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_2 : sf2.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    simp only [arm64_norm] at hx23_2 hx27_2
    have hadd_len :
        BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length +
          BitVec.ofNat 64 x.msg.serialized.length =
        BitVec.ofNat 64 (serPrefix4 x).length := by
      simp only [h4_len, List.length_append, List.length_cons, BitVec.ofNat_add]
      bv_lin
    clear h4_len
    refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
    refine SepWPp.congr_pre
      (P' := (((sp ↦₆₄ g.msgCopyPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄
          BitVec.ofNat 64 (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length)).length) ∗
        vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        A.pool lim st sf2 ∗ stackAt sp preKeyMsgSubStack) ∗ F))
      (by
        rw [← hser4,
          ← vecU8Buf_append_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix3 x ++ 34#8 :: encodeVarint (BitVec.ofNat 64 x.msg.serialized.length))
            x.msg.serialized hcap_pos,
          boxU8Buf_nonempty_eq A.repAlloc g.msgCopyPtr x.msg.serialized hmsg_nil]
        sep_ac_rfl) ?_
    apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 952#64)
    wp_steps_sync_pool ((blkPl_41).base + 952#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hclf3 => ?_
    refine SepWPp.congr_pre ?_
      (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hclf3
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag4_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 860#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 952#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag4_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    (ls_hook_ok_of_mem hmemcpy)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx23 hx26 hx27 hP hnext

theorem step_preKeyMsg_tag4_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 860#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hP : P = ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 952#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        (((sp ↦₆₄ g.msgCopyPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
          boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag4_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx23 hx26 hx27 hP hnext

/-! ## Tag 5 (`registration_id`, `+0x3b8..+0x3ec`) -/

theorem step_preKeyMsg_tag5_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 952#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1004#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hvar_pos : 1 ≤ (encodeVarint (x.regId.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser5 : (serPrefix4 x ++ [40#8]) ++ encodeVarint (x.regId.zeroExtend 64) = serPrefix5 x := by
    simp [serPrefix5, prost_uint32Field_some, prost_key_5_0, List.append_assoc]
  have h5_len : (serPrefix5 x).length = (serPrefix4 x).length + 1 +
      (encodeVarint (x.regId.zeroExtend 64)).length := by
    rw [← hser5, List.length_append, List.length_append, List.length_singleton]
  have hlt4 : (serPrefix4 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq4 := cap_beq_len_false hlt4
  have hle_var : (serPrefix4 x ++ [40#8]).length +
      (encodeVarint (x.regId.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix4 x) hlt4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
  wp_steps_sync_pool ((blkPl_10).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix4 x) 40#8 hlt4
  refine step_call_encVarint_placed_of_ok henc0
    (x.regId.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 996#64) (serPrefix4 x ++ [40#8]) st tr s hle_var (by omega)
    (F := ((sp + 24#64) ↦₃₂ x.regId) ∗ F) hcl0
    (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by
      rw [bv_len_add_one (serPrefix4 x) 40#8, ← hsnoc]
      sep_ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  rw [hser5]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 1004#64)
  wp_steps_sync_pool ((blkPl_41).base + 1004#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hclf2 => ?_
  refine SepWPp.congr_pre ?_
    (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hclf2
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
  simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag5_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 952#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1004#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag5_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx23 hx26 hP hnext

theorem step_preKeyMsg_tag5_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 952#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix4 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix4 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix4 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1004#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length →
      sm.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 24#64) ↦₃₂ x.regId) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag5_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx23 hx26 hP hnext

/-! ## Tag 6 (`signed_pre_key_id`, `+0x3ec..+0x414`) -/

theorem step_preKeyMsg_tag6_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1004#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1044#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hw21 : s.readReg32 .x21 = x.spk := by simpa [State.readReg32] using hx21
  have hvar_pos : 1 ≤ (encodeVarint (x.spk.zeroExtend 64)).length := by
    unfold encodeVarint encodeVarintAux; split <;> simp
  have hser6 : (serPrefix5 x ++ [48#8]) ++ encodeVarint (x.spk.zeroExtend 64) = serPrefix6 x := by
    simp [serPrefix6, prost_uint32Field_some, prost_key_6_0, List.append_assoc]
  have h6_len : (serPrefix6 x).length = (serPrefix5 x).length + 1 +
      (encodeVarint (x.spk.zeroExtend 64)).length := by
    rw [← hser6, List.length_append, List.length_append, List.length_singleton]
  have hlt5 : (serPrefix5 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq5 := cap_beq_len_false hlt5
  have hle_var : (serPrefix5 x ++ [48#8]).length +
      (encodeVarint (x.spk.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix5 x) hlt5]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
  wp_steps_sync_pool ((blkPl_10).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix5 x) 48#8 hlt5
  refine step_call_encVarint_placed_of_ok henc0
    (x.spk.zeroExtend 64) (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 1044#64) (serPrefix5 x ++ [48#8]) st tr s hle_var (by omega)
    (F := F) hcl0
    (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by
      rw [bv_len_add_one (serPrefix5 x) 48#8, ← hsnoc]
      sep_ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  rw [hser6]
  exact hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1

theorem step_preKeyMsg_tag6_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1004#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1044#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag6_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx1 hx8 hx21 hP hnext

theorem step_preKeyMsg_tag6_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1004#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix5 x).length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.model.serialized.length)
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix5 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix5 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1044#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag6_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx1 hx8 hx21 hP hnext

/-! ## Tag 7 (`kyber_pre_key_id`, `+0x414..+0x450`) -/

theorem step_preKeyMsg_tag7_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1044#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1104#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _, _, hkp_val⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hkp : x.kp with
  | none =>
    have hser7 : serPrefix7 x = serPrefix6 x := by
      simp [serPrefix7, hkp, uint32Field]
    simp only [hkp, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 1104#64)
    wp_steps_sync_pool ((blkPl_41).base + 1104#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hcl1 => ?_
    rw [← hser7]
    refine SepWPp.congr_pre ?_
      (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl1
        (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl
  | some k =>
    have hkid : g.kyberId32 = k.preKeyId := hkp_val k hkp
    have hser7 : (serPrefix6 x ++ [56#8]) ++ encodeVarint (k.preKeyId.zeroExtend 64) = serPrefix7 x := by
      simp [serPrefix7, hkp, prost_uint32Field_some, prost_key_7_0, List.append_assoc]
    have h7_len : (serPrefix7 x).length = (serPrefix6 x).length + 1 +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      rw [← hser7, List.length_append, List.length_append, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (k.preKeyId.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt6 : (serPrefix6 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq6 := cap_beq_len_false hlt6
    have hle_var : (serPrefix6 x ++ [56#8]).length +
        (encodeVarint (k.preKeyId.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    simp only [hkp, Option.isSome, ↓reduceIte] at hnext ⊢
    rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix6 x) hlt6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
    wp_steps_sync_pool ((blkPl_10).base)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
      (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
    have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix6 x) 56#8 hlt6
    refine step_call_encVarint_placed_of_ok henc0
      (k.preKeyId.zeroExtend 64) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 1104#64) (serPrefix6 x ++ [56#8]) st tr s hle_var (by omega)
      (F := ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ 1#32) ∗ F) hcl0
      (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by
        rw [bv_len_add_one (serPrefix6 x) 56#8, ← hsnoc]
        sep_ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    rw [hser7]
    exact SepWPp.congr_pre (by sep_ac_rfl) (hnext sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1)

theorem step_preKeyMsg_tag7_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1044#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1104#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag7_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hP hnext

theorem step_preKeyMsg_tag7_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1044#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hP : P = (((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix6 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix6 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 1104#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 44#64) ↦₃₂ g.kyberId32) ∗
          ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag7_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hP hnext

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7Budget
