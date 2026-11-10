/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7Budget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Tag 8 Encoding and Core Composition

Relocatable `[LibsignalPlacement]` encoding step for protobuf tag 8 (`kyber_ciphertext`,
`+0x450..+0x4c4`) and composition of tags 1–8 (`SeamA_placed → SeamB_placed`) under
`RustCliAllocBudget M` with zero additional allocations.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoGames.LibsignalSessionApi.Prost (bytesField)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCodeLoaded
   blkPC_10 blkPl_10 lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsMemcpySym
   ls_hook_ok_of_mem lsρ)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (optKyberAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost PreKeyMsgGhostWf preKeyMsgSubStack preKeyMsgSavedRegs
   optKyberCopyBuf vecU8AtLen preKeyMsgFrameSlotsAt' preKeyMsgHeapAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
  (PreKeyMsgTagRegs serPrefix0 serPrefix7 serPrefix8 serPrefix_lengths_le
   serPrefix8_eq_model_serialized prost_key_8_2 prost_bytesField_some
   ct_len_add_one_beq_zero_false bv_len_beq_zero_false
   vecU8Buf vecSliceRest vecU8Buf_eq_open_one vecU8Buf_snoc_eq
   vecU8Buf_eq_open_slice vecU8Buf_append_eq boxU8Buf_nonempty_eq
   preKeyMsgFrameSlotsAt_open_buf
   cap_beq_len_false bv_len_add_one cap_sub_len_ult_false cap_sub_len_ule_true)
open scoped CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.EncodeVarintNorm
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (SeamA_placed SeamB_placed PreKeyMsgSegExit_placed)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
  (preKeyMsg_memcpy_placed_ok)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
  (encodeVarintNoGrowPlacedSpec encodeVarintNoGrow_placed_ok encodeVarintNoGrow_placed_ok_sessionShim
   step_call_encVarint_placed_of_ok step_call_memcpy_placed_of_ok
   step_preKeyMsg_tag1_placed_of_ok step_preKeyMsg_tag2_placed_of_ok
   step_preKeyMsg_tag3_placed_of_ok)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags4To7Budget
  (step_preKeyMsg_tag4_placed_of_ok step_preKeyMsg_tag5_placed_of_ok
   step_preKeyMsg_tag6_placed_of_ok step_preKeyMsg_tag7_placed_of_ok)
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

private theorem optKyberAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberAt (A.atState lim st s) a ptr kp = optKyberAt A.repAlloc a ptr kp := by
  cases kp <;> rfl

private theorem vecU8Buf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf (A.atState lim st s) cap ptr bs = vecU8Buf A.repAlloc cap ptr bs := rfl

private theorem optKyberCopyBuf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberCopyBuf (A.atState lim st s) ptr kp = optKyberCopyBuf A.repAlloc ptr kp := by
  cases kp <;> rfl

private theorem boxU8Buf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf (A.atState lim st s) ptr bs = boxU8Buf A.repAlloc ptr bs := rfl

/-! ## Tag 8 (`kyber_ciphertext`, `+0x450..+0x4c4`) -/

theorem step_preKeyMsg_tag8_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (blkPl_41).base + 1220#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  subst hP
  cases hkp : x.kp with
  | none =>
    rw [hkp] at hx19 hnext
    have hser8 : serPrefix8 x = serPrefix7 x := by
      simp [serPrefix8, hkp, bytesField]
    clear h8_len
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 1220#64)
    wp_steps_sync_pool ((blkPl_41).base + 1220#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hcl1 => ?_
    rw [← hser8]
    refine SepWPp.congr_pre ?_
      (hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl1
        (by simp only [wp_norm, arm64_norm, *])
        (by rw [hser8]; simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl
  | some k =>
    rw [hkp] at hx19 hnext
    have hct_lt : k.ciphertext.length < 2 ^ 63 := by
      have : k.ciphertext.length ≤ (serPrefix8 x).length := by
        simp [serPrefix8, hkp, bytesField]; omega
      omega
    have hct_lt64 : k.ciphertext.length < 2 ^ 64 := by omega
    have hadd1 := ct_len_add_one_beq_zero_false hct_lt
    have hvar_pos : 1 ≤ (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hser8 : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)) ++
        k.ciphertext = serPrefix8 x := by
      rw [serPrefix8, hkp, Option.map_some, prost_bytesField_some 8 k.ciphertext hct_lt64, prost_key_8_2]
      simp only [← List.append_assoc, List.singleton_append]
    have h8_len_eq : (serPrefix8 x).length = (serPrefix7 x).length + 1 +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length + k.ciphertext.length := by
      rw [← hser8, List.length_append, List.length_append, List.length_cons]; omega
    have hlt7 : (serPrefix7 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq7 := cap_beq_len_false hlt7
    have hle_var : (serPrefix7 x ++ [66#8]).length +
        (encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hle_slice : (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
        k.ciphertext.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, List.length_cons]; omega
    clear h8_len
    dsimp only [optKyberCopyBuf] at hnext ⊢
    rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix7 x) hlt7]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
    wp_steps_sync_pool ((blkPl_10).base)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
      (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
    have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix7 x) 66#8 hlt7
    refine step_call_encVarint_placed_of_ok henc0
      (BitVec.ofNat 64 k.ciphertext.length) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 1164#64) (serPrefix7 x ++ [66#8]) st tr s hle_var (by omega)
      (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A.repAlloc g.kyberCopyPtr k.ciphertext ∗ F) hcl0
      (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by
        rw [bv_len_add_one (serPrefix7 x) 66#8, ← hsnoc]
        sep_ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    simp only [List.append_assoc, List.singleton_append]
    have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_1 : sf1.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs1.1.trans hx19
    have hult1 := cap_sub_len_ult_false hle_slice
    have hule1 := cap_sub_len_ule_true hle_slice
    by_cases hct_nil : k.ciphertext = []
    · have hser8_nil : serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length) =
          serPrefix8 x := by
        simpa [hct_nil] using hser8
      have hct_bv0 : BitVec.ofNat 64 k.ciphertext.length = 0#64 := by simp [hct_nil]
      clear hct_nil h8_len_eq hser8
      rw [hser8_nil] at hult1 hule1 ⊢
      rw [hct_bv0] at hx19_1 hult1 hule1
      apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 1220#64)
      wp_steps_sync_pool ((blkPl_41).base + 1220#64)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hclf2 => ?_
      refine SepWPp.congr_pre ?_
        (hnext _ (BitVec.ofNat 64 (serPrefix8 x).length)
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hclf2
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (PreKeyMsgTagRegs.trans hregs1
            (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
      simp only [wp_norm, arm64_norm, *]; sep_ac_rfl
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_of_ne_nil hct_nil
      have hct_beq := bv_len_beq_zero_false hct_pos hct_lt64
      have hct_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hct_lt64]
      rw [vecU8Buf_eq_open_slice A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
        k.ciphertext.length hle_slice hcap_pos,
        boxU8Buf_nonempty_eq A.repAlloc g.kyberCopyPtr k.ciphertext hct_nil]
      apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ lsMemcpySym)
      wp_steps_sync_pool (lsρ lsMemcpySym)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hclf1' => ?_
      refine step_call_memcpy_placed_of_ok hmc
        (g.serPtr + BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        g.kyberCopyPtr sp ((blkPl_41).base + 1212#64)
        (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
        (BitVec.ofNat 64 x.model.serialized.length)
        k.ciphertext tr s
        (F := ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
          vecSliceRest A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
            (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
            k.ciphertext.length ∗
          A.pool lim st _ ∗ stackAt sp preKeyMsgSubStack ∗
          (⌜g.kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
            A.repAlloc.live g.kyberCopyPtr k.ciphertext.length 1) ∗ F)
        hclf1' (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign1)
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by sep_ac_rfl)
        fun sf2 hpcf2 hrunf2 hspf2 htrf2 hvm2 hclf2 hregs2 hx23_2 hx26_2 => ?_
      have halign2 : sf2.spAligned = true := by simpa only [State.spAligned, hspf2, hsp] using halign
      have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
      have hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 k.ciphertext.length := hregs2.1.trans hx19
      simp only [arm64_norm] at hx23_2 hx19_2
      have hadd_len :
          BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length +
            BitVec.ofNat 64 k.ciphertext.length =
          BitVec.ofNat 64 (serPrefix8 x).length := by
        simp only [h8_len_eq, List.length_append, List.length_cons, BitVec.ofNat_add]
        bv_lin
      clear h8_len_eq
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
      refine SepWPp.congr_pre
        (P' := ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄
            BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          boxU8Buf A.repAlloc g.kyberCopyPtr k.ciphertext ∗
          A.pool lim st sf2 ∗ stackAt sp preKeyMsgSubStack) ∗ F))
        (by
          rw [← hser8,
            ← vecU8Buf_append_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
              (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length))
              k.ciphertext hcap_pos,
            boxU8Buf_nonempty_eq A.repAlloc g.kyberCopyPtr k.ciphertext hct_nil]
          sep_ac_rfl) ?_
      apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 1220#64)
      wp_steps_sync_pool ((blkPl_41).base + 1220#64)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) fun hclf3 => ?_
      refine SepWPp.congr_pre ?_
        (hnext _
          (BitVec.ofNat 64 (serPrefix7 x ++ 66#8 :: encodeVarint (BitVec.ofNat 64 k.ciphertext.length)).length)
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hclf3
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (PreKeyMsgTagRegs.trans hregs2
            (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
      simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag8_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (blkPl_41).base + 1220#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag8_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    (ls_hook_ok_of_mem hmemcpy)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx19 hP hnext

theorem step_preKeyMsg_tag8_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 1104#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx19 : s.readReg64 .x19 =
      (match x.kp with
       | none => noneCap
       | some k => BitVec.ofNat 64 k.ciphertext.length))
    (hP : P = (((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix7 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix7 x) ∗
      optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ (sm : State) (lenW : BitVec 64),
      sm.pc = (blkPl_41).base + 1220#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x8 = x.bkA →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix8 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
          ((sp + 56#64) ↦₆₄ x.bkA) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ lenW) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix8 x) ∗
          optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag8_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx19 hP hnext

/-! ## Core Composition (`SeamA_placed → SeamB_placed`) -/

set_option maxHeartbeats 800000 in
theorem fields_encode_core_placed_ok_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) := by
  rcases hA with ⟨evs, hevs_valid, hlr0, hpc, hcl, hwf, hcommon, hmem⟩
  rcases hcommon with
    ⟨hrun, hsp, halign0, halign, htr, hfp0, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, _hvregs0⟩
  let st' := M.stepEvents evs st
  let sp := s0.sp - 368#64
  have hfp : s.readReg64 .fp = sp + 272#64 := by
    have : s0.sp - 96#64 = sp + 272#64 := by dsimp [sp]; bv_omega
    exact hfp0.trans this
  let F_rest : SepProp :=
    ((sp + 8#64) ↦₆₄ x.ikA) ∗
      memRegion (sp + 28#64) 8 ∗
      ((sp + 36#64) ↦₃₂ g.ver32) ∗
      ((sp + 40#64) ↦₃₂ x.spk) ∗
      ((sp + 64#64) ↦₆₄ x.ret) ∗
      ((sp + 76#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
      ((sp + 80#64) ↦₆₄ x.msgA) ∗
      ((sp + 88#64) ↦₆₄ x.kyA) ∗
      memRegion (sp + 96#64) 128 ∗
      memRegion (sp + 248#64) 24 ∗
      preKeyMsgSavedRegs s0.sp s0 ∗
      (s0.sp ↦₆₄ x.msgA) ∗
      optKyberAt A.repAlloc x.kyA x.kyPtr x.kp ∗
      (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      memRegion x.ret 248
  let P_init : SepProp :=
    ((sp ↦₆₄ g.msgCopyPtr) ∗
      ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 24#64) ↦₃₂ x.regId) ∗
      ((sp + 44#64) ↦₃₂ g.kyberId32) ∗
      ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
      ((sp + 56#64) ↦₆₄ x.bkA) ∗
      ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ 1#64) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
      boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
      boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
      optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
      A.pool lim st' s ∗
      stackAt sp preKeyMsgSubStack) ∗ F_rest
  have hmem_init : s.mem ⊨ P_init ∗ R := by
    have h1 := preKeyMsgFrameSlotsAt_open_buf (A.atState lim st' s) x g s0 1#64 (serPrefix0 x)
    simp only [optKyberAt_atState_eq, vecU8Buf_atState_eq,
      optKyberCopyBuf_atState_eq, boxU8Buf_atState_eq, RustCliAllocBudget.atState_pool] at h1
    dsimp only [serPrefix0] at h1
    rw [← sepConj_assoc, h1] at hmem
    exact hmem
  have hwp : SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1220#64) s P_init
      (fun sf P_f =>
        sf.sp = sp ∧ sf.trace = s0.trace ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
        sf.readReg64 .x8 = x.bkA ∧
        sf.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length ∧
        PreKeyMsgTagRegs s sf ∧
        ∃ lenW,
          P_f = preKeyMsgFrameSlotsAt' (A.atState lim st' sf) x g s0 lenW x.model.serialized ∗
            preKeyMsgHeapAt (A.atState lim st' sf) x g s0)
      (fun _ _ => False) := by
    refine step_preKeyMsg_tag1_placed_of_ok henc0 x g sp st' s0.trace hwf
      hcl hpc hrun hsp halign htr hfp hx20 hx25
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by dsimp [P_init]; sep_ac_rfl)
      fun s1 hpc1 hrun1 hsp1 htr1 hcl1 hx1_1 hregs1 => ?_
    have halign1 : s1.spAligned = true := by simpa only [State.spAligned, hsp1, hsp] using halign
    have hfp1 : s1.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx24_1 : s1.readReg64 .x24 = 33#64 := by reg_chain
    have hx28_1 : s1.readReg64 .x28 = g.bkSerPtr := by reg_chain
    refine step_preKeyMsg_tag2_placed_of_ok henc0 hmc x g sp st' s0.trace hwf
      hcl1 hpc1 hrun1 hsp1 halign1 htr1 hfp1 hx1_1 hx24_1 hx28_1
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s2 hpc2 hrun2 hsp2 htr2 hcl2 hx23_2 hx26_2 hregs2 => ?_
    have halign2 : s2.spAligned = true := by simpa only [State.spAligned, hsp2, hsp] using halign
    have hfp2 : s2.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx22_2 : s2.readReg64 .x22 = 33#64 := by reg_chain
    refine step_preKeyMsg_tag3_placed_of_ok henc0 hmc x g sp st' s0.trace hwf
      hcl2 hpc2 hrun2 hsp2 halign2 htr2 hfp2 hx22_2 hx23_2 hx26_2
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s3 hpc3 hrun3 hsp3 htr3 hcl3 hx23_3 hx26_3 hregs3 => ?_
    have halign3 : s3.spAligned = true := by simpa only [State.spAligned, hsp3, hsp] using halign
    have hfp3 : s3.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx27_3 : s3.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length := by reg_chain
    refine step_preKeyMsg_tag4_placed_of_ok henc0 hmc x g sp st' s0.trace hwf
      hcl3 hpc3 hrun3 hsp3 halign3 htr3 hfp3 hx23_3 hx26_3 hx27_3
      (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s4 hpc4 hrun4 hsp4 htr4 hcl4 hx23_4 hx26_4 hregs4 => ?_
    have halign4 : s4.spAligned = true := by simpa only [State.spAligned, hsp4, hsp] using halign
    have hfp4 : s4.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag5_placed_of_ok henc0 x g sp st' s0.trace hwf
      hcl4 hpc4 hrun4 hsp4 halign4 htr4 hfp4 hx23_4 hx26_4
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s5 hpc5 hrun5 hsp5 htr5 hcl5 hx1_5 hx8_5 hregs5 => ?_
    have halign5 : s5.spAligned = true := by simpa only [State.spAligned, hsp5, hsp] using halign
    have hfp5 : s5.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx21_5 : (s5.readReg64 .x21).setWidth 32 = x.spk := by reg_chain
    refine step_preKeyMsg_tag6_placed_of_ok henc0 x g sp st' s0.trace hwf
      hcl5 hpc5 hrun5 hsp5 halign5 htr5 hfp5 hx1_5 hx8_5 hx21_5
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗
        ((sp + 56#64) ↦₆₄ x.bkA) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s6 hpc6 hrun6 hsp6 htr6 hcl6 hregs6 => ?_
    have halign6 : s6.spAligned = true := by simpa only [State.spAligned, hsp6, hsp] using halign
    have hfp6 : s6.readReg64 .fp = sp + 272#64 := by reg_chain
    refine step_preKeyMsg_tag7_placed_of_ok henc0 x g sp st' s0.trace hwf
      hcl6 hpc6 hrun6 hsp6 halign6 htr6 hfp6
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 48#64) ↦₆₄ g.kyberCopyPtr) ∗ ((sp + 56#64) ↦₆₄ x.bkA) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
        optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗ F_rest)
      (by sep_ac_rfl)
      fun s7 hpc7 hrun7 hsp7 htr7 hcl7 hregs7 => ?_
    have halign7 : s7.spAligned = true := by simpa only [State.spAligned, hsp7, hsp] using halign
    have hfp7 : s7.readReg64 .fp = sp + 272#64 := by reg_chain
    have hx19_7 : s7.readReg64 .x19 =
        (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) :=
      (show s7.readReg64 .x19 = s.readReg64 .x19 by reg_chain).trans hx19
    refine step_preKeyMsg_tag8_placed_of_ok henc0 hmc x g sp st' s0.trace hwf
      hcl7 hpc7 hrun7 hsp7 halign7 htr7 hfp7 hx19_7
      (F := (sp ↦₆₄ g.msgCopyPtr) ∗ ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ ((sp + 24#64) ↦₃₂ x.regId) ∗
        ((sp + 44#64) ↦₃₂ g.kyberId32) ∗ ((sp + 72#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
        boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
        boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
        boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗ F_rest)
      (by sep_ac_rfl)
      fun s8 lenW hpc8 hrun8 hsp8 htr8 hcl8 hx8_8 hx23_8 hx26_8 hregs8 => ?_
    apply SepWPp.done hpc8 hrun8
    refine ⟨hsp8, htr8, hcl8, hx8_8, ?_, hx26_8, by reg_chain, lenW, ?_⟩
    · rw [serPrefix8_eq_model_serialized x] at hx23_8; exact hx23_8
    · rw [serPrefix8_eq_model_serialized x]
      have hopen8 := preKeyMsgFrameSlotsAt_open_buf (A.atState lim st' s8) x g s0 lenW x.model.serialized
      simp only [optKyberAt_atState_eq, vecU8Buf_atState_eq,
        optKyberCopyBuf_atState_eq, boxU8Buf_atState_eq, RustCliAllocBudget.atState_pool] at hopen8
      rw [hopen8]
      dsimp only [F_rest, sp]
      sep_ac_rfl
  intro hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htrf, hclf, hx8f, hx23f, hx26f, hregsf, lenW, hPf⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hmem_init hL
  · refine ⟨sf, hsteps, Or.inl ⟨evs, hevs_valid, hlr0, ?_⟩⟩
    have halignf : sf.spAligned = true := by simpa only [State.spAligned, hspf, hsp] using halign
    refine ⟨hpcf, hclf, hwf, ?_, hx8f, hx23f, hx26f, lenW, ?_⟩
    · exact ⟨hrunf, hspf, halign0, halignf, htrf, by reg_chain⟩
    · rw [hPf, sepConj_assoc] at hmf
      exact hmf
  · exact False.elim hfalse
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem fields_encode_core_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) :=
  fields_encode_core_placed_ok_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    (ls_hook_ok_of_mem hmemcpy)
    x st g R s0 s hA

theorem fields_encode_core_placed_ok_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (st : M.σ) (g : PreKeyMsgFrameGhost) (R : SepProp) (s0 s : State)
    (hA : SeamA_placed A lim x st g R s0 s) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s (SeamB_placed A lim x st g R s0) :=
  fields_encode_core_placed_ok_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x st g R s0 s hA

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTag8Budget
