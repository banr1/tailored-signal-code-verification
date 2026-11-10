/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Segment 2a (`+0x100 .. +0x278`)

Re-exports `NewEncodeTags123BudgetAux` (`+0x100 → +0x1b8`) and proves relocatable
`[LibsignalPlacement]` budget-threaded segment lemmas (`0` allocations) for encoding protobuf
tags 1–3 (`+0x1b8 → +0x278`) on Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123Budget

open Arm64 ProofLib SepProp CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl lsρ
   lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym withLsCodeLoaded)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  encodedLenSpec encodeVarintSpec encodeVarintSpecX
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.NewEncodeTags123Callees
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   RustLayoutOk fitsEvents_append fitsEvents_nil rustAllocEvents rustCliAllocBudgetSpec
   rustCliAllocNoOomSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (EncodeVarintEnv encodeVarintEvents_of_spare encodeVarintSpec encodeVarintSpecX encodedLenSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (call_noPanic_placed newPostPrologueEvents stackAt_split_ge)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_allocNoOom_placed_ok new_memcpy_placed_ok
   new_shim_placed_ok noAllocShimBudgetSpec)

open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
  (addresses_length_parse bind_state call_noPanic_extern
   encodeBytesField_1_protoMsg_parse encodeBytesField_4_protoMsg_parse
   encodeBytesField_5_protoMsg_empty_parse encodeBytesField_5_protoMsg_nonempty_parse
   encodeBytesField_6_protoMsg_none_parse encodeBytesField_6_protoMsg_some_parse
   encodeUint32Field_2_protoMsg_parse encodeUint32Field_3_protoMsg_parse
   encodeVarintSpecWithStack encodeVarintSpecWithStack_post_eq encodeVarintSpecWithStack_pre_eq
   encodeVarintSpecX_eq_withStack encodeVarintSpec_eq_withStack
   encode_protoMsg_length_bounds_parse encodedLenBudgetSpec_pre_eq
   fitsEnv_encodeVarint_of_spare fitsEvents_serAlloc_and_after_of_postPrologue
   newAfterSerAllocEvents newPostPrologueEvents_eq_serAlloc_append
   new_alloc_ser_wpp_placed new_alloc_ser_wpp_placed_at new_alloc_ser_wpp_placed_x
   new_store_wire_wp_placed pack_wire_post_parse serPrefix6_eq_serializeContent_parse
   serPrefix6_length_parse serPrefix_lengths_le_parse tag123_pure_facts_parse
   wireLengthsFit_protoMsg_parse wireSignalMessageAt_expose_rk_parse)

export LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
  (newAfterSerAllocEvents newPostPrologueEvents_eq_serAlloc_append
   fitsEvents_serAlloc_and_after_of_postPrologue
   addresses_length_parse encodeBytesField_1_protoMsg_parse
   encodeUint32Field_2_protoMsg_parse encodeUint32Field_3_protoMsg_parse
   encodeBytesField_4_protoMsg_parse encodeBytesField_5_protoMsg_empty_parse
   encodeBytesField_5_protoMsg_nonempty_parse encodeBytesField_6_protoMsg_none_parse
   encodeBytesField_6_protoMsg_some_parse encode_protoMsg_length_bounds_parse
   wireLengthsFit_protoMsg_parse serPrefix6_eq_serializeContent_parse
   serPrefix6_length_parse serPrefix_lengths_le_parse tag123_pure_facts_parse
   pack_wire_post_parse wireSignalMessageAt_expose_rk_parse
   encodedLenBudgetSpec_pre_eq encodeVarintSpecWithStack
   encodeVarintSpec_eq_withStack encodeVarintSpecX_eq_withStack
   fitsEnv_encodeVarint_of_spare encodeVarintSpecWithStack_pre_eq
   encodeVarintSpecWithStack_post_eq new_store_wire_wp_placed
   new_alloc_ser_wpp_placed_at new_alloc_ser_wpp_placed new_alloc_ser_wpp_placed_x)
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## Encoding tags 1, 2, 3 (`+0x1b8 → +0x278`, `0` allocations) -/

theorem new_encode_tag1_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix1 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, h0_len, hcmp1, hvar1_lt, hvar1_fit, hbs1a_len, hcmp_rk, hrk_len,
      hrk_ne, hp1_eq, _, _, _, _, _, _, _, _, _, _⟩ :=
    tag123_pure_facts_parse parse x (encode (x.protoMsg parse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr 1#64 (serPtr + 2#64) x.serPrefix0 (by omega) htot_lt hserPtr
        (by simp [h0_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx1 : EncodeVarintGhost :=
    ⟨33#64, sp0 - 176#64, BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9), serPtr,
      x.serPrefix0 ++ [0x0a#8]⟩
  refine call_noPanic_placed (x := (gx1, st))
    (F := ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx1 st _ (sp0 - 416#64)
          (by simp only [gx1, wp_norm, arm64_norm])
          (by simp only [gx1, wp_norm, arm64_norm]) hvar1_lt hvar1_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr 1#64 2#64 (serPtr + 2#64) x.serPrefix0 0x0a#8
            (by omega) htot_lt hserPtr (by simp [h0_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx1 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs1 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs1 => ?_
  have hevs1_nil : evs1 = [] := by
    rw [hevs1]; exact encodeVarintEvents_of_spare (x := gx1) hvar1_fit
  subst hevs1_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar1_fit with ⟨hcap', hptr'⟩
  dsimp only [gx1] at hcap' hptr' ⊢
  subst cap' ptr'
  rw [serVec_expose_slice A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr 3#64 33#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) 33
        (by omega) htot_lt hserPtr (by decide) rfl rfl (by bv_kernel),
      wireSignalMessageAt_expose_rk_parse parse A.repAlloc x rkPtr ctCopyPtr pqCap pqCopyPtr
        addrCap addrPtr (sp0 - 288#64)]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
  refine bind_state ?_
  intro s_mc
  refine call_noPanic_extern (x := (serPtr + 3#64, rkPtr, x.senderRatchetKey.serialize))
    (F := ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗ ((sp0 - 160#64) ↦₆₄ 3#64) ∗
          A.repAlloc.live serPtr (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)) ∗
          memRegion (serPtr + 36#64) ((BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat -
            ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length - 33) ∗
          A.pool lim st s_mc ∗ stackAt (sp0 - 416#64) varStack ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          (((sp0 - 288#64) ↦₆₄ 33#64) ∗ (((sp0 - 288#64) + 8#64) ↦₆₄ rkPtr) ∗
           (((sp0 - 288#64) + 16#64) ↦₆₄ 33#64) ∗
           ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗
           A.repAlloc.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
           optVecU8At A.repAlloc ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A.repAlloc ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           optVecU8At A.repAlloc ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses parse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hmemcpy (by simp only [s_mc, wp_norm, arm64_norm])
    (by simp only [s_mc, wp_norm, arm64_norm, hrun1])
    (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [s_mc, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_mc] at hm ⊢
    simp only [framelessMemcpyBudgetSpec, withVmPreserved]
    rw [session2MemcpySpec_pre_eq _ _ _ _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrk_len])]
    simp only [State.mem_setMem, hrk_len, sepConj_assoc]
      at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  dsimp only [s_mc] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  dsimp only [s_mc] at hvm2 htr2 ⊢
  rw [← A.pool_transport lim st _ sf2 hvm2]
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 536#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp2, hsp0_align,
      h19_2, h20_2, h21_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, htr2, and_self]
  · rw [stackAt_split_ge hle hbnd (sp0 - 416#64),
        ← hp1_eq,
        ← serVec_pack_slice A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr 3#64 33#64 36#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)
            x.senderRatchetKey.serialize (by omega) htot_lt hserPtr hrk_ne rfl
            (by rw [hrk_len]) rfl (by bv_kernel),
        hrk_len]
    simp only [arm64_norm, sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag1_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix1 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag1_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag1_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix1 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag1_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag2_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix1 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix2 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, h1_len, hcmp2, hvar2_lt, hvar2_fit, hp2_eq,
      _, _, _, _, _⟩ :=
    tag123_pure_facts_parse parse x (encode (x.protoMsg parse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr 36#64 (serPtr + 37#64) (x.serPrefix1 parse) (by omega) htot_lt hserPtr
        (by simp [h1_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx2 : EncodeVarintGhost :=
    ⟨x.counter.zeroExtend 64, sp0 - 176#64, BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9),
      serPtr, x.serPrefix1 parse ++ [0x10#8]⟩
  refine call_noPanic_placed (x := (gx2, st))
    (F := ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx2 st _ (sp0 - 416#64)
          (by simp only [gx2, wp_norm, arm64_norm])
          (by simp only [gx2, wp_norm, arm64_norm]) hvar2_lt hvar2_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr 36#64 37#64 (serPtr + 37#64) (x.serPrefix1 parse) 0x10#8
            (by omega) htot_lt hserPtr (by simp [h1_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx2 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs2 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs2 => ?_
  have hevs2_nil : evs2 = [] := by
    rw [hevs2]; exact encodeVarintEvents_of_spare (x := gx2) hvar2_fit
  subst hevs2_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar2_fit with ⟨hcap', hptr'⟩
  dsimp only [gx2] at hcap' hptr' ⊢
  subst cap' ptr'
  apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1])
    (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align,
      h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_split_ge hle hbnd (sp0 - 416#64), ← hp2_eq]
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag2_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix1 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix2 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag2_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCopyPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag2_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix1 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix2 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag2_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCopyPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag3_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix2 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix3 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp2_lt, hcmp3, hvar3_lt,
      hvar3_fit, hp3_eq⟩ :=
    tag123_pure_facts_parse parse x (encode (x.protoMsg parse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix2 parse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix2 parse).length + 1#64)
        (x.serPrefix2 parse) hp2_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx3 : EncodeVarintGhost :=
    ⟨x.previousCounter.zeroExtend 64, sp0 - 176#64,
      BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9), serPtr,
      x.serPrefix2 parse ++ [0x18#8]⟩
  refine call_noPanic_placed (x := (gx3, st))
    (F := ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx3 st _ (sp0 - 416#64)
          (by simp only [gx3, wp_norm, arm64_norm])
          (by simp only [gx3, wp_norm, arm64_norm]) hvar3_lt hvar3_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0 (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (BitVec.ofNat 64 (x.serPrefix2 parse).length)
            (BitVec.ofNat 64 (x.serPrefix2 parse).length + 1#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix2 parse).length + 1#64)
            (x.serPrefix2 parse) 0x18#8 hp2_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx3 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs3 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs3 => ?_
  have hevs3_nil : evs3 = [] := by
    rw [hevs3]; exact encodeVarintEvents_of_spare (x := gx3) hvar3_fit
  subst hevs3_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar3_fit with ⟨hcap', hptr'⟩
  dsimp only [gx3] at hcap' hptr' ⊢
  subst cap' ptr'
  apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1])
    (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align,
      h19_1, h20_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_split_ge hle hbnd (sp0 - 416#64), ← hp3_eq]
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag3_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix2 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix3 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag3_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag3_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix2 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix3 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag3_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123Budget
