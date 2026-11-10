/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.VarintBridge

/-!
# Budget-Threaded `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]`

Defines allocator event envelopes (`decodeVarint2Events`, `DecodeVarint2Env`) and proves
`RustCliAllocBudget`-threaded `[LibsignalPlacement]` contracts (`decodeVarint2Spec`,
`decodeVarint2SpecX`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Prost (DecodeVarintSlowGhost VarintSlicePre byte9_ule_of_ge byte9_ule_of_lt cbz_len_cons_false decodeErrorHookStackX decodeVarintSlowStack decodeVarintSlowStackX decodeVarint_eq_none_of_pre exists_cons_of_all_gt memRegion_48_split ovf_byte10 ovf_byte2 ovf_byte3 ovf_byte6 ovf_byte7 pointsTo64_pair_entails_memRegion16 sliceCursorAfter sliceCursorAt toNat_le_0x7f_iff two_le_toNat_iff ult_10_of_ge_11 ult_10_of_lt_11)

namespace LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkLib_eq_291 blkPC_291 blkPl_291 lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (decodeVarintAux_suffix decodeVarint_eq_varintSlow)
open CryptoVerification.SpqrV1.Varint
  (byte9_ult1_of_ge byte9_ult1_of_lt decodeVarint2Stack decodeVarint2StackX decodeVarint_1
   decodeVarint_10 decodeVarint_2 decodeVarint_3 decodeVarint_4 decodeVarint_5 decodeVarint_6
   decodeVarint_7 decodeVarint_8 decodeVarint_9 getLsbD_31_signExtend signExtend32_and_127
   signExtend32_and_255 sliceCursorAfter_of_eq stackAt_decodeVarint2 stackAt_decodeVarint2X
   stackAt_errorHookX_entails_slowX stackAt_errorHook_entails_slow stackAt_slowX_eq_errorHookX
   stackAt_slow_eq_errorHook zeroExtend64_zeroExtend32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowBudgetSpec decodeVarintSlowBudgetSpecWithStack
   decodeVarintSlowBudgetSpecWithStack_eq_varintSlowStack decodeVarintSlowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  signExtend32_and_255 zeroExtend64_zeroExtend32 signExtend32_and_127 getLsbD_31_signExtend

/-! ## Envelope and Specifications -/

/-- Deterministic allocator events of `decode_varint::<&mut &[u8]> [local#2]` (`[]` on `Ok`,
`rustAllocEvents 72 8` via `DecodeError::from` on `Err`). -/
abbrev decodeVarint2Events (bs : List (BitVec 8)) : List AllocEvent :=
  decodeVarintSliceEvents bs

abbrev DecodeVarint2Env (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DecodeVarintSliceEnv bs evs

theorem decodeVarintSlowEvents_eq_decodeVarint2Events (bs : List (BitVec 8)) :
    decodeVarintSlowEvents bs = decodeVarint2Events bs := by
  have hvs : varintSlow bs =
      (decodeVarint bs).map (fun p => (p.1, bs.length - p.2.length)) :=
    decodeVarint_eq_varintSlow bs
  unfold decodeVarintSlowEvents decodeVarint2Events decodeVarintSliceEvents
  rw [hvs]
  cases decodeVarint bs <;> rfl

theorem decodeVarintSlowEnv_iff_decodeVarint2Env (bs : List (BitVec 8)) (evs : List AllocEvent) :
    DecodeVarintSlowEnv bs evs ↔ DecodeVarint2Env bs evs := by
  unfold DecodeVarintSlowEnv DecodeVarint2Env DecodeVarintSliceEnv
  rw [decodeVarintSlowEvents_eq_decodeVarint2Events]

/-- Stack-parameterized budget-threaded `DecodeVarintSlowGhost` contract for `decode_varint_slow`. -/
def decodeVarintSlowProstSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarint2Env x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0x40 + errStack)
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x40 + errStack) ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

def decodeVarintSlowProstSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarintSlowProstSpecGen A lim decodeErrorHookStack

def decodeVarintSlowProstSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarintSlowProstSpecGen A lim decodeErrorHookStackX

theorem decodeVarintSlowProstGen_ok_of_session2 {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {errStack : Nat}
    (hSlow : subroutine_ok prog entry
      (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack))) :
    subroutine_ok prog entry (decodeVarintSlowProstSpecGen A lim errStack) := by
  refine subroutine_ok_outcome_intro fun ⟨y, st⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack)).pre
        (y.bufRef, y.slot, y.ptr, y.bs, st) s0 ∗ R := by
    simp only [decodeVarintSlowProstSpecGen, decodeVarintSlowBudgetSpecWithStack,
      sliceCursorAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hlen, hfits⟩, hmem⟩
    have hfits' : FitsEnv M lim st (DecodeVarintSlowEnv y.bs) := fun evs hevs =>
      hfits evs ((decodeVarintSlowEnv_iff_decodeVarint2Env y.bs evs).mp hevs)
    exact ⟨⟨hx0, by omega, hfits'⟩, hmem⟩
  refine hSlow.mono_outcome (y.bufRef, y.slot, y.ptr, y.bs, st) R s0 hpc hrun hpre' hal
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hvs : varintSlow y.bs =
        (decodeVarint y.bs).map (fun p => (p.1, y.bs.length - p.2.length)) :=
      decodeVarint_eq_varintSlow y.bs
    dsimp only [decodeVarintSlowBudgetSpecWithStack, decodeVarintSlowProstSpecGen] at hpost ⊢
    rw [hvs] at hpost
    have henv_eq : DecodeVarintSlowEnv y.bs = DecodeVarint2Env y.bs :=
      funext fun evs => propext (decodeVarintSlowEnv_iff_decodeVarint2Env y.bs evs)
    rw [henv_eq] at hpost
    cases hd : decodeVarint y.bs with
    | some p =>
      rcases p with ⟨v, rest⟩
      rw [hd] at hpost
      dsimp only [Option.map, sliceCursorAfter] at hpost ⊢
      obtain ⟨k, _, _, hrest_eq⟩ := decodeVarintAux_suffix y.bs 0 0#64 v rest hd
      have hlen_sub : y.bs.length - (y.bs.length - rest.length) = rest.length := by
        rw [hrest_eq, List.length_drop]; omega
      rw [hlen_sub] at hpost
      exact Satisfies.of_eq hpost
    | none =>
      rw [hd] at hpost
      dsimp only [Option.map] at hpost ⊢
      have hpost1 : sf.mem ⊨
          ((y.slot ↦₆₄ (y.ptr + BitVec.ofNat 64 (min 10 y.bs.length))) ∗
            ((y.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (y.bs.length - min 10 y.bs.length))) ∗
          (⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
            ⌜sf.trace = s0.trace⌝ ∗
            (y.bufRef ↦₆₄ y.slot) ∗
            (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env y.bs evs⌝ ∗
              A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
            (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hpost
      have hmem1 := Satisfies.mono
        (sepConj_mono_left (pointsTo64_pair_entails_memRegion16 y.slot _ _)) hpost1
      have hmem2 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          (⌜sf.trace = s0.trace⌝ ∗
            (y.bufRef ↦₆₄ y.slot) ∗
            (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env y.bs evs⌝ ∗
              A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
            memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.of_eq hmem1
      rw [satisfies_pure_sepConj] at hmem2
      rcases hmem2 with ⟨⟨hx0, hx1⟩, hmem3⟩
      have hmem4 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64⌝ ∗
          (⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
            (⌜sf.trace = s0.trace⌝ ∗
              (y.bufRef ↦₆₄ y.slot) ∗
              (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env y.bs evs⌝ ∗
                A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt s0.sp (0x40 + errStack) ∗
              decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
              memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R)) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hx0, hx1, hmem3⟩
      exact Satisfies.of_eq hmem4
  · dsimp only [decodeVarintSlowBudgetSpecWithStack] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [decodeVarintSlowBudgetSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [decodeVarintSlowBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Stack-parameterized budget-threaded contract of
`prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]` (Block `291`). -/
def decodeVarint2SpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarint2Env x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0x40 + (0x40 + errStack))
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x40 + (0x40 + errStack)) ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

def decodeVarint2Spec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarint2SpecGen A lim decodeErrorHookStack

def decodeVarint2SpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarint2SpecGen A lim decodeErrorHookStackX

/-! ## Relocatable `[LibsignalPlacement]` Proof -/

private theorem sepConj_pointsToBytes_cons (a : BitVec 64) (b : BitVec 8)
    (bs : List (BitVec 8)) (R : SepProp) :
    (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) ∗ R = (a ↦ₛ (b :: bs)) ∗ R := by
  rw [← sepConj_assoc, ← pointsToBytes_cons]

private theorem sepConj_pointsToBytes_split_last (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63) (R : SepProp) :
    (ptr ↦ₛ bs.dropLast) ∗ ((ptr + BitVec.ofNat 64 bs.length - 1#64) ↦₈ bs.getLast hne) ∗ R =
      (ptr ↦ₛ bs) ∗ R := by
  rw [← sepConj_assoc, ← CryptoVerification.LibsignalTripleRatchet.Prost.pointsToBytes_split_last ptr bs hne hlen]

private theorem decodeVarint2_pool_of_some {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p) (st : M.σ) (sf : State) :
    (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env bs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) =
      A.pool lim st sf := by
  apply Entails.antisymm
  · refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
    have hnil : evs = [] := by
      simpa [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using hevs
    subst hnil
    exact Entails.refl _
  · refine Entails.sepExists_right [] ?_
    have henv : DecodeVarint2Env bs [] := by
      simp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd]
    simp only [eq_true henv, pure_true, emp_sepConj]
    exact Entails.refl _

private theorem decodeVarint2Env_of_fromEnv {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hnone : decodeVarint bs = none) (h : DecodeErrorFromEnv evs) :
    DecodeVarint2Env bs evs := by
  dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents]
  rw [hnone]
  exact h

set_option hygiene false in
local macro "wp_done_sync_pool" : tactic => `(tactic| (
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_done
))

set_option hygiene false in
local macro "decode_varint2_some_ret_budget" : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_291).rebase (blkPl_291).base (hooksException H))
    blkLib_eq_291 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  wp_steps 4
  by_cases hb1 : b1 ≤ 0x7f#8
  · have hbit1 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb1
    have hd_eq := decodeVarint_2 bs2 hb0 hb1
    simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
    rw [sliceCursorAfter_of_eq (k := 2) rfl]
    wp_steps
    conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
    wp_done_sync_pool
  · have hbit1 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb1
    have hovf2 := ovf_byte2 hb0 hb1
    obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        hb0, hb1, not_false_eq_true, and_self])
    conv => arg 4; rw [pointsToBytes_cons]
    wp_steps 7
    by_cases hb2 : b2 ≤ 0x7f#8
    · have hbit2 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb2
      have hd_eq := decodeVarint_3 bs3 hb0 hb1 hb2
      simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
      rw [sliceCursorAfter_of_eq (k := 3) rfl]
      wp_steps
      conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
      wp_done_sync_pool
    · have hbit2 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb2
      have hovf3 := ovf_byte3 hb0 hb1 hb2
      obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          hb0, hb1, hb2, not_false_eq_true, and_self])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb3 : b3 ≤ 0x7f#8
      · have hbit3 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb3
        have hd_eq := decodeVarint_4 bs4 hb0 hb1 hb2 hb3
        simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
        rw [sliceCursorAfter_of_eq (k := 4) rfl]
        wp_steps
        conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
        wp_done_sync_pool
      · have hbit3 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb3
        have hovf4 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
        obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb4 : b4 ≤ 0x7f#8
        · have hbit4 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb4
          have hd_eq := decodeVarint_5 bs5 hb0 hb1 hb2 hb3 hb4
          simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
          rw [sliceCursorAfter_of_eq (k := 5) rfl]
          wp_steps
          conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
          wp_done_sync_pool
        · have hbit4 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb4
          obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 5
          by_cases hb5 : b5 ≤ 0x7f#8
          · have hbit5 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb5
            have hd_eq := decodeVarint_6 bs6 hb0 hb1 hb2 hb3 hb4 hb5
            simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
            rw [sliceCursorAfter_of_eq (k := 6) rfl]
            wp_steps
            conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
            wp_done_sync_pool
          · have hbit5 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb5
            have hovf6 := ovf_byte6 hb4 hb5
            obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) hpre
              (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb6 : b6 ≤ 0x7f#8
            · have hbit6 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb6
              have hd_eq := decodeVarint_7 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6
              simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
              rw [sliceCursorAfter_of_eq (k := 7) rfl]
              wp_steps
              conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
              wp_done_sync_pool
            · have hbit6 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb6
              have hovf7 := ovf_byte7 hb4 hb5 hb6
              obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                (pre := [b0, b1, b2, b3, b4, b5, b6]) hpre (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                  forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 7
              by_cases hb7 : b7 ≤ 0x7f#8
              · have hbit7 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hb7
                have hd_eq := decodeVarint_8 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
                simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
                rw [sliceCursorAfter_of_eq (k := 8) rfl]
                wp_steps
                conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
                wp_done_sync_pool
              · have hbit7 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb7
                have hovf8 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
                obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                  (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) hpre (by simp)
                  (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                    forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb8 : b8 ≤ 0x7f#8
                · have hbit8 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb8
                  have hd_eq := decodeVarint_9 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
                  simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
                  rw [sliceCursorAfter_of_eq (k := 9) rfl]
                  wp_steps
                  conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
                  wp_done_sync_pool
                · have hbit8 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
                  obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) hpre (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                      and_self])
                  have hb9 : ¬ 2#8 ≤ b9 := by
                    intro hge
                    apply hnone
                    rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                    by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                      simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                        hb6, hb7, hb8, hb9_le, hge]
                  have hb9_ult := byte9_ult1_of_lt hb9
                  have hb9_ule := byte9_ule_of_lt hb9
                  have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                  conv => arg 4; rw [pointsToBytes_cons]
                  have hd_eq := decodeVarint_10 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                  simp only [decodeVarint2_pool_of_some A lim hd_eq]; rw [hd_eq]; dsimp only
                  rw [sliceCursorAfter_of_eq (k := 10) rfl]
                  wp_steps
                  conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
                  wp_done_sync_pool
))

set_option hygiene false in
local macro "decode_varint2_budget_body "
    fromTarget:term:max slowTarget:term:max prog:term:max
    slowStack:term:max stackSplit:term:max slowEqErr:ident errEntailsSlow:ident : tactic => `(tactic| (
  wp_init g s0
  rcases g with ⟨⟨bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  wp_simp_pre only [sliceCursorAt, $stackSplit:term, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_stk_0
  apply SepWP.exists_elim; intro v_stk_1
  apply SepWP.exists_elim; intro v_stk_2
  simp only [$stackSplit:term]
  have hlen_lt : bs.length < 2 ^ 63 := ‹bs.length < 2 ^ 63›
  have hfits_top : FitsEnv M lim st (DecodeVarint2Env bs) := ‹FitsEnv M lim st (DecodeVarint2Env bs)›
  cases bs with
  | nil =>
    have hd_nil : decodeVarint ([] : List (BitVec 8)) = none := rfl
    have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := hfits_top
    have hknh : KindNoHeap 0x8000000000000001#64 := by decide
    rw [hd_nil]
    dsimp only
    wp_steps_sync_pool $fromTarget
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 [].length)) (by sep_focus)
    conv => arg 4; rw [$slowEqErr (s0.sp - 64#64)]
    wp_call hFromCall (s0.sp - 64#64, 0x8000000000000001#64, st)
    have hsp_sf : sf.sp = s0.sp - 64#64 := by
      refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
    have hevs_dv : DecodeVarint2Env ([] : List (BitVec 8)) _ := ‹DecodeErrorFromEnv _›
    conv => arg 4; simp only [hsp_sf, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_err
    apply SepWP.fold ($errEntailsSlow s0.sp) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    wp_done
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false hlen_lt
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.signExtend64_getLsbD_63_beq_of_le hb0
      have hd_1 := decodeVarint_1 bs1 hb0
      simp only [decodeVarint2_pool_of_some A lim hd_1]
      rw [hd_1]
      dsimp only
      rw [sliceCursorAfter_of_eq (k := 1) rfl]
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      simp only [State.setMem_setMem]
      conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
      wp_done
    · have hbit0 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_sync_pool ((blkPl_291).base + 64#64)
      simp only [State.setMem_setMem]
      by_cases hpre : VarintSlicePre (b0 :: bs1)
      · obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        refine (fun (hjoin : ∀ (sj : State)
            (_ : sj.pc = (blkPl_291).base + 88#64)
            (_ : sj.status = .Running)
            (_ : sj.sp = s0.sp - 64#64)
            (_ : sj.trace = s0.trace)
            (_ : sj.readReg64 (Reg.gpr 1#5) = BitVec.signExtend 64 b0)
            (_ : sj.readReg64 (Reg.gpr 8#5) = slot)
            (_ : sj.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (b0 :: b1 :: bs2).length)
            (_ : sj.readReg64 (Reg.gpr 10#5) = ptr)
            (_ : sj.readReg64 (Reg.gpr 11#5) =
              BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1)))
            (_ : sj.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
            (_ : sj.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
            (_ : sj.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5))
            (_ : sj.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5))
            (_ : sj.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5))
            (_ : sj.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
            (_ : sj.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
            (_ : sj.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
            (_ : sj.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
            (_ : sj.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5))
            (_ : sj.readReg64 (Reg.gpr 29#5) = s0.sp - 16#64)
            (_ : calleeSavedVRegs sj = calleeSavedVRegs s0),
            SepWP $prog (s0.readReg64 Reg.lr) sj
              (A.pool lim st sj ∗
                bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
                (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
                (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 1#64 + 1#64) ↦ₛ bs2)) ∗
                stackAt (s0.sp - 64#64) $slowStack ∗ memRegion (s0.sp - 56#64) 40 ∗
                (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
                (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
              (fun sf P_f =>
                (sf.mem ⊨ P_f ∗ R →
                    sf.mem ⊨
                      ((match decodeVarint (b0 :: b1 :: bs2) with
                          | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
                          | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
                        ⌜sf.trace = s0.trace⌝ ∗ bufRef ↦₆₄ slot ∗
                        (∃∗ evs : List AllocEvent, ⌜DecodeVarint2Env (b0 :: b1 :: bs2) evs⌝ ∗
                          A.pool lim (M.stepEvents evs st) sf) ∗
                        (stackAt (s0.sp - 64#64) $slowStack ∗
                          memRegion (s0.sp - 56#64) 40 ∗
                          ∃∗ v1, ∃∗ v2, ∃∗ v8,
                            (s0.sp - 64#64) ↦₆₄ v8 ∗ (s0.sp - 16#64) ↦₆₄ v2 ∗
                            (s0.sp - 8#64) ↦₆₄ v1) ∗
                        match decodeVarint (b0 :: b1 :: bs2) with
                        | some (_, rest) =>
                          sliceCursorAfter slot ptr (b0 :: b1 :: bs2) rest
                        | none =>
                          ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
                            decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
                            memRegion slot 16 ∗ ptr ↦ₛ (b0 :: b1 :: bs2)) ∗ R) ∧
                  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) => ?_)
          (fun sj hpc_j hrun_j hsp_j htr_j hx1_j hx8_j hx9_j hx10_j hx11_j
            hx19_j hx20_j hx21_j hx22_j hx23_j hx24_j hx25_j hx26_j hx27_j hx28_j hx29_j hvregs_j => ?_)
        · by_cases h11 : 11 ≤ (b0 :: b1 :: bs2).length
          · have hhi := ult_10_of_ge_11 h11 hlen_lt
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps_sync_pool ((blkPl_291).base + 88#64)
            simp only [State.setMem_setMem]
            apply SepWP.weaken_pre
            case h =>
              refine hjoin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
                wp_norm_lhs
            case hent =>
              simp only [arm64_norm]
              sep_entail
          · rcases hpre with h11' | ⟨hne, hlast⟩
            · exact (h11 h11').elim
            · have hhi := ult_10_of_lt_11 h11 hlen_lt
              have hbit_last := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_le hlast
              conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]; rw [pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne]
              wp_steps_sync_pool ((blkPl_291).base + 84#64)
              simp only [State.setMem_setMem]
              conv => arg 4; simp only [sepConj_pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne hlen_lt]; rw [pointsToBytes_cons]; simp only [sepConj_assoc]; rw [pointsToBytes_cons]
              wp_steps_sync_pool ((blkPl_291).base + 88#64)
              simp only [State.setMem_setMem]
              apply SepWP.weaken_pre
              case h =>
                refine hjoin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
                  wp_norm_lhs
              case hent =>
                simp only [arm64_norm]
                sep_entail
        · by_cases hnone : decodeVarint (b0 :: b1 :: bs2) = none
          · obtain ⟨b0', b1', b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
              hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre hpre hnone
            cases heq
            have hfits_from : FitsEnv M lim st DecodeErrorFromEnv := fun evs hevs =>
              hfits_top evs (by
                dsimp [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents]
                rw [hnone]
                simpa [DecodeErrorFromEnv] using hevs)
            have hknh : KindNoHeap 0x8000000000000001#64 := by decide
            rw [hnone]; dsimp only
            have hbit1 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb1
            have hbit2 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb2
            have hbit3 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb3
            have hbit4 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb4
            have hbit5 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb5
            have hbit6 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb6
            have hbit7 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hb7
            have hbit8 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.signExtend64_getLsbD_63_beq_of_gt hb8
            have hovf2 := ovf_byte2 hb0 hb1
            have hovf3 := ovf_byte3 hb0 hb1 hb2
            have hovf4 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.ovf_byte4_zext hb0 hb1 hb2 hb3
            have hovf6 := ovf_byte6 hb4 hb5
            have hovf7 := ovf_byte7 hb4 hb5 hb6
            have hovf8 := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.ovf_byte8_zext hb4 hb5 hb6 hb7
            have hb9_ult := byte9_ult1_of_ge hb9
            have hb9_ule := byte9_ule_of_ge hb9
            conv => arg 4; simp only [pointsToBytes_cons]
            wp_steps_sync_pool $fromTarget
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length)) (by sep_focus)
            conv => arg 4; rw [$slowEqErr (s0.sp - 64#64)]
            wp_call hFromCall (s0.sp - 64#64, 0x8000000000000001#64, st)
            have hsp_sf : sf.sp = s0.sp - 64#64 := by
              refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
            have hevs_dv := decodeVarint2Env_of_fromEnv hnone ‹DecodeErrorFromEnv _›
            conv => arg 4; simp only [hsp_sf, memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
            apply SepWP.exists_elim; intro v_err
            apply SepWP.fold ($errEntailsSlow s0.sp) (by sep_focus)
            wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
            simp only [State.setMem_setMem]
            conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]
            wp_done
          · decode_varint2_some_ret_budget
      · have h11 : ¬ 11 ≤ (b0 :: bs1).length := fun h => hpre (Or.inl h)
        have hne : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        have hlast : ¬ (b0 :: bs1).getLast hne ≤ 0x7f#8 := fun h => hpre (Or.inr ⟨hne, h⟩)
        have hhi := ult_10_of_lt_11 h11 hlen_lt
        have hbit_last := CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits.getLsbD_7_beq_of_gt hlast
        conv => arg 4; simp only [sepConj_pointsToBytes_cons, ← pointsToBytes_cons]; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne]
        wp_steps_sync_pool $slowTarget
        simp only [State.setMem_setMem]
        conv => arg 4; simp only [sepConj_pointsToBytes_split_last ptr (b0 :: bs1) hne hlen_lt]
        wp_call hSlowCall (⟨bufRef, slot, ptr, b0 :: bs1⟩, st)
        have hsp_sf : sf.sp = s0.sp - 64#64 := by
          refine Eq.trans ‹sf.sp = _› ?_; wp_norm_lhs
        conv => arg 4; simp only [hsp_sf]
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          repeat (apply SepWP.pure_left; intro _)
          wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
          simp only [State.setMem_setMem]
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          dsimp only
          conv => arg 4; simp only [hd, sepConj_assoc, arm64_norm]
          repeat (apply SepWP.pure_left; intro _)
          wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
          simp only [State.setMem_setMem]
          wp_done
))

set_option maxHeartbeats 8000000 in
theorem decodeVarint2_placed_ok_of_prost_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hSlowCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293) (decodeVarintSlowProstSpec A lim)) :
    subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (blkPl_291).base (decodeVarint2Spec A lim) := by
  dsimp only [decodeErrorFromBudgetSpec] at hFromCall
  dsimp only [decodeVarintSlowProstSpec, decodeVarintSlowProstSpecGen, sliceCursorAt] at hSlowCall
  unfold decodeVarint2Spec decodeVarint2SpecGen
  simp only [show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl]
  decode_varint2_budget_body
    (lsmpl.base 261)
    (lsmpl.base 293)
    ((blkPC_291).rebase (blkPl_291).base H)
    decodeVarintSlowStack
    stackAt_decodeVarint2 stackAt_slow_eq_errorHook stackAt_errorHook_entails_slow

set_option maxHeartbeats 8000000 in
theorem decodeVarint2_placed_ok_of_prost_contracts_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX))
    (hSlowCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293) (decodeVarintSlowProstSpecX A lim)) :
    subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (blkPl_291).base (decodeVarint2SpecX A lim) := by
  dsimp only [decodeErrorFromBudgetSpecWithStack] at hFromCall
  dsimp only [decodeVarintSlowProstSpecX, decodeVarintSlowProstSpecGen, sliceCursorAt] at hSlowCall
  unfold decodeVarint2SpecX decodeVarint2SpecGen
  simp only [show 0x40 + (0x40 + decodeErrorHookStackX) = decodeVarint2StackX from rfl]
  decode_varint2_budget_body
    (lsmpl.base 261)
    (lsmpl.base 293)
    ((blkPC_291).rebase (blkPl_291).base H)
    decodeVarintSlowStackX
    stackAt_decodeVarint2X stackAt_slowX_eq_errorHookX stackAt_errorHookX_entails_slowX

theorem decodeVarint2_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hSlowCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293) (decodeVarintSlowBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (blkPl_291).base (decodeVarint2Spec A lim) := by
  rw [← decodeVarintSlowBudgetSpecWithStack_eq_varintSlowStack] at hSlowCall
  exact decodeVarint2_placed_ok_of_prost_contracts hFromCall
    (decodeVarintSlowProstGen_ok_of_session2 hSlowCall)

theorem decodeVarint2_placed_ok_of_contracts_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 261) (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX))
    (hSlowCall : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 293)
      (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + decodeErrorHookStackX))) :
    subroutine_ok ((blkPC_291).rebase (blkPl_291).base H)
      (blkPl_291).base (decodeVarint2SpecX A lim) :=
  decodeVarint2_placed_ok_of_prost_contracts_x hFromCall
    (decodeVarintSlowProstGen_ok_of_session2 hSlowCall)

end LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
