/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Field Encoding: Tags 1–3

Zero-growth relocatable `encode_varint` contract (`blkPl_10`), budget-threaded `encode_varint` and
`memcpy` call combinators, and encoding steps for protobuf tags 1–3 (`+0x25c..+0x35c`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSessionApi.Prost (uint32Field)
open CryptoGames.LibsignalSession (PublicKey IdentityKey)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl withLsCodeLoaded
   extract_withLsCodeLoaded blkPC_10 blkPl_10 blkPC_13 blkPl_13 blkPC_45 blkPl_45
   lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsMemcpySym
   ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block lsρ)
open CryptoVerification.RustHeap (allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost encodeVarintStack)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost PreKeyMsgGhostWf preKeyMsgSubStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
  (PreKeyMsgTagRegs serPrefix0 serPrefix1 serPrefix2 serPrefix3 serPrefix_lengths_le
   prost_key_1_0 prost_key_2_2 prost_key_3_2 encodeVarint_33
   prost_uint32Field_some prost_bytesField_some
   vecU8Buf vecSliceRest vecU8At_eq_header_sep_buf vecU8Buf_eq_open_one vecU8Buf_snoc_eq
   vecU8Buf_eq_open_slice vecU8Buf_append_eq boxU8Buf_nonempty_eq
   cap_beq_len_false bv_len_add_one
   cap_sub_len_ult_false cap_sub_len_ule_true stackAt_preKeyMsgSubStack_eq_encodeVarint
   fp_sub_48_eq fp_sub_48_sub_eq fp_sub_40_eq fp_sub_32_eq)
open scoped CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode.EncodeVarintNorm
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved FitsEnv
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (subroutine_ok_rustCliAllocNoOom_externWithStack
   subroutine_ok_rustCliReallocNoOom_externWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrowBudget (finish_grow_placed_ok_of_hooks_opt)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
  (do_reserve_raw_placed_ok_of_fg_opt do_reserve_placed_ok_of_raw_opt)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (EncodeVarintEnv encodeVarintEvents_of_spare encodeVarintSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBudget
  (encode_varint_placed_ok encode_varint_placed_ok_of_doReserve)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
  (subroutine_ok_shimAllocHook_of_sessionShimBudget preKeyMsg_memcpy_placed_ok)
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

/-! ## Zero-Growth `encode_varint` Contract (`blkPl_10`) -/

/-- Zero-allocation relocatable contract for `prost::encoding::varint::encode_varint` when
existing spare capacity covers `(encodeVarint x.val).length`, leaving cost-model state `st`
unchanged. -/
def encodeVarintNoGrowPlacedSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 61⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp encodeVarintStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      A.pool lim st sf ∗ stackAt s0.sp encodeVarintStack

theorem encodeVarintNoGrow_placed_ok_of_enc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim))) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [encodeVarintNoGrowPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hle, hcap⟩, hpre⟩
  have hfit : FitsEnv M lim st (EncodeVarintEnv x) := by
    rintro _ rfl
    rw [encodeVarintEvents_of_spare hle]
    trivial
  have hpre_ev : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, encodeVarintSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inr (by omega), hfit⟩, hpre⟩
  refine henc.mono_outcome (x, st) R s0 hpc hrun hpre_ev hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeVarintSpec] at hpost
    dsimp only [withLsCodeLoaded, encodeVarintNoGrowPlacedSpec]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, cap', ptr', hpost⟩
    have hpull :
        ((⌜sf.trace = s0.trace⌝ ∗
          (⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
          (⌜EncodeVarintEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt s0.sp encodeVarintStack) ∗ R) =
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        (⌜EncodeVarintEnv x evs⌝ ∗
          ((⌜sf.trace = s0.trace⌝ ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encodeVarintStack) ∗ R)) := by
      sep_ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, hno⟩, hpost⟩
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hevs, hpost⟩
    obtain ⟨rfl, rfl⟩ := hno hle
    rw [hevs, encodeVarintEvents_of_spare hle, AllocCostModel.stepEvents_nil] at hpost
    exact hpost
  · exact Or.inr hrest

theorem encodeVarintNoGrow_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)) :=
  encodeVarintNoGrow_placed_ok_of_enc (encode_varint_placed_ok hshim halloc hrealloc)

theorem encodeVarintNoGrow_placed_ok_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)) :=
  encodeVarintNoGrow_placed_ok_of_enc
    (encode_varint_placed_ok_of_doReserve A lim H
      (do_reserve_placed_ok_of_raw_opt
        (do_reserve_raw_placed_ok_of_fg_opt (hookStack := allocHookStack) (by decide)
          (finish_grow_placed_ok_of_hooks_opt (hookStack := allocHookStack) (by decide)
            (subroutine_ok_shimAllocHook_of_sessionShimBudget (ls_hook_ok_of_mem hshim))
            (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
              (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))
            (subroutine_ok_rustCliReallocNoOom_externWithStack (by decide) (by decide)
              (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_mem hrealloc)))))))

/-! ## Relocatable Call Combinators -/

theorem step_call_encVarint_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ) (tr : List TraceEvent) (s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 61)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_10).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val) (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ A.pool lim st s0 ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      SepWPp (lsProg_41 H) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A.repAlloc cap ptr (bs ++ encodeVarint val) ∗
          A.pool lim st sf ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp := by
  subst hsp
  have henc := ls_subroutine_ok_cl_of_block (callerProg := lsProg_41 H) henc0
  refine SepWPp.call_wpp (x := (⟨val, v, cap, ptr, bs⟩, st))
    (F := memRegion (s0.sp - 7824#64) 3568 ∗ F)
    henc hpc hrun halign hlr ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec] at hm
      exact (not_satisfies_false_sepConj hm).elim) ?_
  · intro R' hm
    dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hle, hcap⟩, ?_⟩
    have heq0 : P ∗ R' = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s0 ∗
        stackAt s0.sp encodeVarintStack) ∗ ((memRegion (s0.sp - 7824#64) 3568 ∗ F) ∗ R') := by
      rw [hP, stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
      sep_ac_rfl
    exact heq0 ▸ hm
  intro sf hpcf hrunf hspf hcsf
  dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hclf => ?_
  refine SepWPp.pure_elim fun htrf => ?_
  have heq1 :
      vecU8At A.repAlloc v cap ptr (bs ++ encodeVarint val) ∗ A.pool lim st sf ∗
        stackAt s0.sp encodeVarintStack ∗ memRegion (s0.sp - 7824#64) 3568 ∗ F =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A.repAlloc cap ptr (bs ++ encodeVarint val) ∗
        A.pool lim st sf ∗ stackAt s0.sp preKeyMsgSubStack) ∗ F) := by
    rw [stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
    sep_ac_rfl
  rw [heq1]
  exact hnext sf hpcf hrunf hspf (htrf.trans htr) hclf (by reg_chain)

theorem step_call_encVarint_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ) (tr : List TraceEvent) (s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 61)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_10).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val) (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ A.pool lim st s0 ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      SepWPp (lsProg_41 H) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A.repAlloc cap ptr (bs ++ encodeVarint val) ∗
          A.pool lim st sf ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp :=
  step_call_encVarint_placed_of_ok (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    val v cap ptr sp ret_pc bs st tr s_init hle hcap hcl hpc hrun hsp halign hlr htr hregs
    hx0 hx1 hP hnext

theorem step_call_encVarint_placed_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ) (tr : List TraceEvent) (s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 61)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_10).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val) (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A.repAlloc cap ptr bs ∗ A.pool lim st s0 ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      SepWPp (lsProg_41 H) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A.repAlloc cap ptr (bs ++ encodeVarint val) ∗
          A.pool lim st sf ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp :=
  step_call_encVarint_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    val v cap ptr sp ret_pc bs st tr s_init hle hcap hcl hpc hrun hsp halign hlr htr hregs
    hx0 hx1 hP hnext

theorem step_call_memcpy_placed_of_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsρ lsMemcpySym) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → VmPreserved s0 sf → LibsignalCodeLoaded lsmpl sf.mem →
      PreKeyMsgTagRegs s_init sf → sf.readReg64 .x23 = v23 → sf.readReg64 .x26 = v26 →
      SepWPp (lsProg_41 H) ret sf (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp := by
  subst hsp
  intro R hm hL
  have hpre : s0.mem ⊨ framelessMemcpyBudgetSpec.pre (dst, src, payload) s0 ∗ (F ∗ R) := by
    dsimp only [framelessMemcpyBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [hP, sepConj_assoc] at hm; exact hm
  obtain ⟨sf, hsteps, hout, _⟩ :=
    hmc.no_fault_before_outcome (dst, src, payload) (F ∗ R) s0 hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [framelessMemcpyBudgetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, htrf, hvmf⟩, hpost⟩
    rw [hlr] at hpcf
    have hpost' : sf.mem ⊨ (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) ∗ R := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sf', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf (htrf.trans htr) hvmf (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (by reg_chain) (by reg_chain) (by reg_chain) R hpost' (hsteps.codeLoaded hL)
    exact ⟨sf', hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem step_call_memcpy_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsρ lsMemcpySym) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → VmPreserved s0 sf → LibsignalCodeLoaded lsmpl sf.mem →
      PreKeyMsgTagRegs s_init sf → sf.readReg64 .x23 = v23 → sf.readReg64 .x26 = v26 →
      SepWPp (lsProg_41 H) ret sf (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp :=
  step_call_memcpy_placed_of_ok (ls_hook_ok_of_mem hmemcpy)
    dst src sp ret_pc v23 v26 payload tr s_init hcl hpc hrun hsp halign hlr htr hregs
    hx23 hx26 hx0 hx1 hx2 hP hnext

theorem step_call_memcpy_placed_sessionHooks [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsρ lsMemcpySym) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → VmPreserved s0 sf → LibsignalCodeLoaded lsmpl sf.mem →
      PreKeyMsgTagRegs s_init sf → sf.readReg64 .x23 = v23 → sf.readReg64 .x26 = v26 →
      SepWPp (lsProg_41 H) ret sf (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp :=
  step_call_memcpy_placed_of_ok
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    dst src sp ret_pc v23 v26 payload tr s_init hcl hpc hrun hsp halign hlr htr hregs
    hx23 hx26 hx0 hx1 hx2 hP hnext

/-! ## Tag 1 (`pre_key_id`, `+0x25c..+0x2a0`) -/

theorem step_preKeyMsg_tag1_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 672#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length → PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _, hpk_val, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hpk : x.preKeyId with
  | none =>
    simp only [hpk, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hx20
    have hw20 : s.readReg32 .x20 = 0#32 := by simpa [State.readReg32] using hx20
    have hser1 : serPrefix1 x = serPrefix0 x := by
      simp [serPrefix1, hpk, uint32Field]
    have h1_len_bv : BitVec.ofNat 64 (serPrefix1 x).length = 1#64 := by simp [hser1, h0_len]
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 672#64)
    wp_steps_sync_pool ((blkPl_41).base + 672#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hcl1 => ?_
    rw [← hser1]
    refine SepWPp.congr_pre ?_
      (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl1
        (by rw [h1_len_bv]; simp only [wp_norm, arm64_norm, *])
        (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl
  | some pid =>
    simp only [hpk, Option.isSome, ↓reduceIte] at hx20
    rw [hpk_val pid hpk] at hx25
    have hw20 : s.readReg32 .x20 = 1#32 := by simpa [State.readReg32] using hx20
    have hw25 : s.readReg32 .x25 = pid := by simpa [State.readReg32] using hx25
    have hser1 : (serPrefix0 x ++ [0x08#8]) ++ encodeVarint (pid.zeroExtend 64) = serPrefix1 x := by
      simp [serPrefix1, hpk, prost_uint32Field_some, prost_key_1_0, List.append_assoc]
    have h1_len : (serPrefix1 x).length = 2 + (encodeVarint (pid.zeroExtend 64)).length := by
      rw [← hser1, List.length_append, List.length_append, h0_len, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (pid.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt0 : (serPrefix0 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq0 := cap_beq_len_false hlt0
    have h0_len_bv : BitVec.ofNat 64 (serPrefix0 x).length = 1#64 := by simp [h0_len]
    rw [h0_len_bv] at hbeq0
    have hle_var : (serPrefix0 x ++ [0x08#8]).length + (encodeVarint (pid.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, h0_len, List.length_singleton]; omega
    rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix0 x) hlt0, h0_len_bv]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
    wp_steps_sync_pool ((blkPl_10).base)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
      (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
    have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
      (serPrefix0 x) 8#8 hlt0
    rw [h0_len_bv] at hsnoc
    refine step_call_encVarint_placed_of_ok henc0
      (pid.zeroExtend 64) (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 660#64) (serPrefix0 x ++ [8#8]) st tr s hle_var (by omega)
      (F := F) hcl0
      (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by
        simp only [List.length_append, h0_len, List.length_singleton]
        rw [← hsnoc]
        sep_ac_rfl)
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    rw [hser1]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 672#64)
    wp_steps_sync_pool ((blkPl_41).base + 672#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hcl2 => ?_
    refine SepWPp.congr_pre ?_
      (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl2
        (by simp only [wp_norm, arm64_norm, *])
        (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
    simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 672#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length → PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag1_placed_of_ok (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx20 hx25 hP hnext

theorem step_preKeyMsg_tag1_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 672#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length → PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag1_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx20 hx25 hP hnext

/-! ## Tag 2 (`base_key`, `+0x2a0..+0x300`) -/

theorem step_preKeyMsg_tag2_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 768#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hbk_len : x.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbk_bv : BitVec.ofNat 64 x.baseKey.serialize.length = 33#64 := by simp [hbk_len]
  have hser2 : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) ++ x.baseKey.serialize = serPrefix2 x := by
    rw [serPrefix2, prost_bytesField_some 2 x.baseKey.serialize (by omega), prost_key_2_2, hbk_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h2_len : (serPrefix2 x).length = (serPrefix1 x).length + 1 + 1 + 33 := by
    rw [← hser2, List.length_append, List.length_append, List.length_cons, hvar33_len, hbk_len]
  have hlt1 : (serPrefix1 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq1 := cap_beq_len_false hlt1
  have hle_var : (serPrefix1 x ++ [0x12#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length +
      x.baseKey.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hbk_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x) hlt1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
  wp_steps_sync_pool ((blkPl_10).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x) 18#8 hlt1
  refine step_call_encVarint_placed_of_ok henc0
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 716#64) (serPrefix1 x ++ [18#8]) st tr s hle_var (by omega)
    (F := boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗ F) hcl0
    (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by
      rw [bv_len_add_one (serPrefix1 x) 18#8, ← hsnoc]
      sep_ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_1 : sf1.readReg64 .x24 = 33#64 := by reg_chain
  have hx28_1 : sf1.readReg64 .x28 = g.bkSerPtr := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hbk_bv] at hult1 hule1
  have hbk_ne : x.baseKey.serialize ≠ [] := by intro h; simp [h] at hbk_len
  rw [vecU8Buf_eq_open_slice A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A.repAlloc g.bkSerPtr x.baseKey.serialize hbk_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hclf1' => ?_
  refine step_call_memcpy_placed_of_ok hmc
    (g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    g.bkSerPtr sp ((blkPl_41).base + 760#64)
    (BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.baseKey.serialize tr s
    (F := ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄
        BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
      A.pool lim st _ ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗
        A.repAlloc.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F)
    hclf1' (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self]))
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by sep_ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hvm2 hclf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_2 : sf2.readReg64 .x24 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx24_2
  have hadd_len : BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix2 x).length := by
    simp only [h2_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]
    bv_lin
  clear h2_len
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  refine SepWPp.congr_pre
    (P' := ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄
        BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
      A.pool lim st sf2 ∗ stackAt sp preKeyMsgSubStack) ∗ F))
    (by
      rw [← hser2,
        ← vecU8Buf_append_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize hcap_pos,
        boxU8Buf_nonempty_eq A.repAlloc g.bkSerPtr x.baseKey.serialize hbk_ne]
      sep_ac_rfl) ?_
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 768#64)
  wp_steps_sync_pool ((blkPl_41).base + 768#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hcl3 => ?_
  refine SepWPp.congr_pre ?_
    (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl3
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
  simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 768#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag2_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    (ls_hook_ok_of_mem hmemcpy)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx1 hx24 hx28 hP hnext

theorem step_preKeyMsg_tag2_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 768#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag2_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx1 hx24 hx28 hP hnext

/-! ## Tag 3 (`identity_key`, `+0x300..+0x35c`) -/

theorem step_preKeyMsg_tag3_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A lim)))
    (hmc : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 860#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hik_len : x.ik.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hik_bv : BitVec.ofNat 64 x.ik.serialize.length = 33#64 := by simp [hik_len]
  have hser3 : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) ++ x.ik.serialize = serPrefix3 x := by
    rw [serPrefix3, prost_bytesField_some 3 x.ik.serialize (by omega), prost_key_3_2, hik_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h3_len : (serPrefix3 x).length = (serPrefix2 x).length + 1 + 1 + 33 := by
    rw [← hser3, List.length_append, List.length_append, List.length_cons, hvar33_len, hik_len]
  have hlt2 : (serPrefix2 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq2 := cap_beq_len_false hlt2
  have hle_var : (serPrefix2 x ++ [26#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length +
      x.ik.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hik_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x) hlt2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base)
  wp_steps_sync_pool ((blkPl_10).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  have hsnoc := vecU8Buf_snoc_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x) 26#8 hlt2
  refine step_call_encVarint_placed_of_ok henc0
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 808#64) (serPrefix2 x ++ [26#8]) st tr s hle_var (by omega)
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗ F) hcl0
    (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [State.spAligned, wp_norm, arm64_norm, *] using halign)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by
      rw [bv_len_add_one (serPrefix2 x) 26#8, ← hsnoc]
      sep_ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_1 : sf1.readReg64 .x22 = 33#64 := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hik_bv] at hult1 hule1
  have hik_ne : x.ik.serialize ≠ [] := by intro h; simp [h] at hik_len
  rw [vecU8Buf_eq_open_slice A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A.repAlloc g.ikSerPtr x.ik.serialize hik_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hclf1' => ?_
  refine step_call_memcpy_placed_of_ok hmc
    (g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    g.ikSerPtr sp ((blkPl_41).base + 852#64)
    (BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.ik.serialize tr s
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄
        BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
      A.pool lim st _ ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗
        A.repAlloc.live g.ikSerPtr x.ik.serialize.length 1) ∗ F)
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
  have hx22_2 : sf2.readReg64 .x22 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx22_2
  have hadd_len : BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix3 x).length := by
    simp only [h3_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]
    bv_lin
  clear h3_len
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  refine SepWPp.congr_pre
    (P' := ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄
        BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
      boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
      A.pool lim st sf2 ∗ stackAt sp preKeyMsgSubStack) ∗ F))
    (by
      rw [← hser3,
        ← vecU8Buf_append_eq A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize hcap_pos,
        boxU8Buf_nonempty_eq A.repAlloc g.ikSerPtr x.ik.serialize hik_ne]
      sep_ac_rfl) ?_
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 860#64)
  wp_steps_sync_pool ((blkPl_41).base + 860#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hcl3 => ?_
  refine SepWPp.congr_pre ?_
    (hnext _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hcl3
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, wp_norm, arm64_norm, and_self])))
  simp only [wp_norm, arm64_norm, *]; sep_ac_rfl

theorem step_preKeyMsg_tag3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 860#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag3_placed_of_ok
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc)
    (ls_hook_ok_of_mem hmemcpy)
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx22 hx23 hx26 hP hnext

theorem step_preKeyMsg_tag3_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (st : M.σ) (tr : List TraceEvent) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = tr)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
      A.pool lim st s ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 860#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = tr → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
          A.pool lim st sm ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_41 H) ret s P Q Qp :=
  step_preKeyMsg_tag3_placed_of_ok
    (encodeVarintNoGrow_placed_ok_sessionShim hshim halloc hrealloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    x g sp st tr hwf hcl hpc hrun hsp halign htr hfp hx22 hx23 hx26 hP hnext

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeTags1To4Budget
