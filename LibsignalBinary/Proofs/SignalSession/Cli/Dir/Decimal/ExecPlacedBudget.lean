/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` `signal_session::stores::decimal` (Block 597)

Defines the deterministic allocator event list `decimalEvents` and verifies `decimal` on Block 597
under `RustCliAllocBudget M` with `FitsEnv M lim st (DecimalEnv x.n)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget fitsEvents_append)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Varint (sp_sub_80_aligned)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost decimalText)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_597 lsProg_597)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (satisfies_lscro_pre stk_le_pow64_of_roLoaded)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon.SepWPp (call_lscro)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers
  (cap_beq_len_false cap_beq_len_true decimalText_digit decimalText_ge10 decimalText_length_le
   digit_byte_eq div10_trunc32 memRegion_24_cells stack_slot_empty_vecU8At stack_slot_eq_header_rest
   stack_slot_of_header_rest stack_slot_open_one ule_nine_false ule_nine_true vecU8At_snoc_sret)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (pushByteStep_of_eq pushByteStep_of_lt)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (decimalSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (lift_stk_lscro_budget)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Deterministic `decimal` Allocator Events, Envelope, and Final Capacity -/

/-- Final `Vec<u8>` capacity after pushing `m` bytes one-by-one starting at `(cap, len)`. -/
def pushBytesCap : Nat → Nat → Nat → Nat
  | 0, cap, _ => cap
  | m + 1, cap, len => pushBytesCap m (pushByteStep cap len).1 (len + 1)

theorem pushBytesCap_snoc :
    ∀ (m cap len : Nat),
      pushBytesCap (m + 1) cap len = (pushByteStep (pushBytesCap m cap len) (len + m)).1
  | 0, cap, len => by simp [pushBytesCap]
  | m + 1, cap, len => by
    change pushBytesCap (m + 1) (pushByteStep cap len).1 (len + 1) =
      (pushByteStep (pushBytesCap m (pushByteStep cap len).1 (len + 1)) (len + (m + 1))).1
    rw [pushBytesCap_snoc m (pushByteStep cap len).1 (len + 1)]
    rw [show len + 1 + m = len + (m + 1) by omega]

theorem pushBytesEvents_snoc :
    ∀ (m cap len : Nat),
      pushBytesEvents (m + 1) cap len =
        pushBytesEvents m cap len ++ (pushByteStep (pushBytesCap m cap len) (len + m)).2
  | 0, cap, len => by simp [pushBytesEvents, pushBytesCap]
  | m + 1, cap, len => by
    change (pushByteStep cap len).2 ++ pushBytesEvents (m + 1) (pushByteStep cap len).1 (len + 1) =
      ((pushByteStep cap len).2 ++ pushBytesEvents m (pushByteStep cap len).1 (len + 1)) ++
        (pushByteStep (pushBytesCap m (pushByteStep cap len).1 (len + 1)) (len + (m + 1))).2
    rw [pushBytesEvents_snoc m (pushByteStep cap len).1 (len + 1), List.append_assoc]
    rw [show len + 1 + m = len + (m + 1) by omega]

private theorem pushBytesCap_zero_lt_pow63 (m : Nat) (hm : m ≤ 10) :
    pushBytesCap m 0 0 < 2 ^ 63 := by
  match m with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | _ + 11 => omega

/-- Deterministic `AllocEvent` list emitted by `signal_session::stores::decimal` on `n`. -/
def decimalEvents (n : BitVec 32) : List AllocEvent :=
  pushBytesEvents (decimalText n.toNat).length 0 0

/-- Callee-fixed allocator event envelope of `signal_session::stores::decimal`. -/
def DecimalEnv (n : BitVec 32) (evs : List AllocEvent) : Prop :=
  evs = decimalEvents n

theorem decimalEnv_events (n : BitVec 32) : DecimalEnv n (decimalEvents n) := rfl

/-- Deterministic final `Vec<u8>` capacity produced by `signal_session::stores::decimal` on `n`. -/
def decimalCap (n : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (pushBytesCap (decimalText n.toNat).length 0 0)

private theorem decimalCap_toNat (n : BitVec 32) :
    (decimalCap n).toNat = pushBytesCap (decimalText n.toNat).length 0 0 := by
  have hn32 : n.toNat < 2 ^ 32 := n.isLt
  have hlen10 : (decimalText n.toNat).length ≤ 10 :=
    decimalText_length_le 10 n.toNat (by omega) (by omega)
  have hlt := pushBytesCap_zero_lt_pow63 (decimalText n.toNat).length hlen10
  dsimp only [decimalCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## 2. Depth-Bounded Contract & Local Frame / Callee-Saved Helpers -/

def decimalBoundedRawSpecP {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (k resStack : Nat) : Spec (DecimalGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ k ∧
      FitsEnv M lim st (DecimalEnv x.n)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp (k * 0x50 + resStack) ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ ptr : BitVec 64,
        vecU8At A.repAlloc x.ret (decimalCap x.n) ptr (decimalText x.n.toNat)) ∗
      stackAt s0.sp (k * 0x50 + resStack) ∗
      A.pool lim (M.stepEvents (decimalEvents x.n) st) sf

def decimalBoundedSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (k resStack : Nat) :
    Spec (DecimalGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (decimalBoundedRawSpecP A lim k resStack)

private def DecimalCalleeSavedP (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem DecimalCalleeSavedP.refl (s0 : State) : DecimalCalleeSavedP s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem DecimalCalleeSavedP.trans {s0 s1 s2 : State}
    (h01 : DecimalCalleeSavedP s0 s1) (h12 : DecimalCalleeSavedP s1 s2) :
    DecimalCalleeSavedP s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

private theorem sepWPp_let_state {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post onPanic : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog target_pc sc P post onPanic) :
    SepWPp prog target_pc s P post onPanic := h

private theorem DecimalCalleeSavedP.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) :
    DecimalCalleeSavedP s1 s2 :=
  ⟨hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.1, hcs.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
   hcs.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem stackAt_decimal_frame_p {m : Nat} (hm : m + 0x50 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (m + 0x50) =
      stackAt (sp - 80#64) m ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
         ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
          ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
          ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
          ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
          ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp m 10 (by omega)
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by
    cells_unfold
  rw [show m + 0x50 = m + 8 * 10 by omega, h1, hc10]

/-! ## 3. Shared Push Epilogue (`+76`) and Reserve-and-Finish (`+168`) -/

private theorem step_push_epilogue_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {k resStack : Nat}
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {st st_cur : M.σ} {R : SepProp} {s0 s : State}
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hcap_eq_dec : cap = decimalCap x.n)
    (hst_eq : M.stepEvents (decimalEvents x.n) st = st_cur)
    (hlt : bs.length < cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hpc : s.pc = (blkPl_597).base + 76#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (_halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSavedP s0 s) :
    SepWPp (lsProg_597 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc (s0.sp - 72#64) cap ptr bs ∗
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
        stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) ∗ A.pool lim st_cur s)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (decimalBoundedSpecPlaced A lim k resStack).post (x, st) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (decimalBoundedSpecPlaced A lim k resStack).onPanic (x, st) s0 sf ∗ R)) := by
  subst hcap_eq_dec; subst hst_eq
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  rw [stack_slot_open_one A.repAlloc s0.sp _ ptr bs hlt hcap hptr]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun b0 => ?_
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWPp.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
  refine ⟨?_, by simp only [arm64_norm, wp_norm, *],
    by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, *]⟩
  intro hPR
  rw [digit_byte_eq x.n] at hPR
  have hsnoc := vecU8At_snoc_sret A.repAlloc x.ret _ ptr bs (BitVec.ofNat 8 (0x30 + x.n.toNat % 10))
    hlt hcap hptr
  have hframe := stackAt_decimal_frame_p (m := (k - 1) * 0x50 + resStack) (by omega) s0.sp
  have hstk_eq : (k - 1) * 0x50 + resStack + 0x50 = k * 0x50 + resStack := by omega
  rw [hstk_eq] at hframe
  dsimp only [decimalBoundedSpecPlaced, withLsCodeRoLoaded, decimalBoundedRawSpecP]
  rw [hframe, ← hbs]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v0, decimalCap x.n, ptr, BitVec.ofNat 64 bs.length,
    s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x21, v7,
    s0.readReg64 .x20, s0.readReg64 .x19, ptr, by simp only [arm64_norm, wp_norm, *], ?_⟩
  rw [← hsnoc]
  convert hPR using 1
  sep_ac_rfl

private theorem step_reserve_and_finish_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {k resStack : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hk : 1 ≤ k) (hstk64 : k * 0x50 + resStack ≤ 2 ^ 64)
    {x : DecimalGhost} {st st_pre : M.σ} {R : SepProp} {s0 s : State}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (cap ptr v0 v7 o0 o1 o2 : BitVec 64) (bs : List (BitVec 8))
    (hcap_eq : cap.toNat = bs.length)
    (hlen9 : bs.length ≤ 9)
    (hbs : bs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] = decimalText x.n.toNat)
    (hfits_res : FitsEvents M lim st_pre
      (doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) cap ptr bs 1)))
    (hnewCap_eq : BitVec.ofNat 64 (reserveCap cap.toNat bs.length 1) = decimalCap x.n)
    (hst_after :
      M.stepEvents (decimalEvents x.n) st =
        M.stepEvents (doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) cap ptr bs 1)) st_pre)
    (hpc : s.pc = (blkPl_597).base + 168#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.zeroExtend 64 x.n)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs.length)
    (hcs : DecimalCalleeSavedP s0 s) :
    SepWPp (lsProg_597 H) (s0.readReg64 .lr) s
      (vecU8At A.repAlloc (s0.sp - 72#64) cap ptr bs ∗
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
        stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) ∗ A.pool lim st_pre s)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (decimalBoundedSpecPlaced A lim k resStack).post (x, st) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (decimalBoundedSpecPlaced A lim k resStack).onPanic (x, st) s0 sf ∗ R)) := by
  apply sepWPp_seq_lscro hcrl (mid := lsmpl.base 561)
  wp_steps_sync_pool (lsmpl.base 561)
  apply SepWP.done (by wp_norm_goal) (by simp only [arm64_norm, wp_norm, *])
  intro hcrl_sc
  apply sepWPp_let_state; intro sc
  have hcs_call : DecimalCalleeSavedP s0 sc :=
    hcs.trans ⟨by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm]⟩
  have hsp_sc : sc.sp = s0.sp - 80#64 := by simp only [sc, arm64_norm, wp_norm, *]
  have htr_sc : sc.trace = s0.trace := by simp only [sc, arm64_norm, wp_norm, *]
  have hsp_aligned : sc.spAligned = true := by
    simp only [State.spAligned, hsp_sc, beq_iff_eq]
    exact sp_sub_80_aligned halign
  have hsplit_bot : stackAt (s0.sp - 80#64) ((k - 1) * 0x50 + resStack) =
      memRegion (s0.sp - 80#64 - BitVec.ofNat 64 ((k - 1) * 0x50 + resStack)) ((k - 1) * 0x50) ∗
        stackAt (s0.sp - 80#64) resStack := by
    have h1 := ProofLib.stackAt_split_bottom (s0.sp - 80#64) resStack ((k - 1) * 0x50) (by omega)
    simpa only [Nat.add_comm resStack ((k - 1) * 0x50)] using h1
  set F_res : SepProp :=
    ((s0.sp - 80#64) ↦₆₄ v0) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 24#64) ↦₆₄ v7) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2) ∗
    memRegion (s0.sp - 80#64 - BitVec.ofNat 64 ((k - 1) * 0x50 + resStack)) ((k - 1) * 0x50)
  refine call_lscro
    (x := (DoReserveCall.mk (s0.sp - 72#64) cap ptr bs 1, st_pre))
    (ret_pc := (blkPl_597).base + 188#64)
    (F := F_res)
    hRes hcrl_sc
    (by simp only [sc]; wp_norm_goal)
    (by simp only [sc, arm64_norm, wp_norm, *])
    hsp_aligned
    (by simp only [sc, arm64_norm, wp_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit_bot] at hm
    simp only [doReserveSpecOf, sepConj_assoc, satisfies_pure_sepConj]
    have hx1_sc : (sc.readReg64 .x1).toNat = bs.length := by
      have : sc.readReg64 .x1 = BitVec.ofNat 64 bs.length := by simp only [sc, arm64_norm, wp_norm, *]
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx2_sc : (sc.readReg64 .x2).toNat = 1 := by
      have : sc.readReg64 .x2 = 1#64 := by simp only [sc, arm64_norm, wp_norm]
      rw [this]; rfl
    refine ⟨⟨by simp only [sc, arm64_norm, wp_norm, *], hx1_sc, hx2_sc,
      by simp only [sc, arm64_norm, wp_norm], by simp only [sc, arm64_norm, wp_norm],
      by dsimp [reserveCap]; omega, (fitsEnv_doReserve_iff _).mpr hfits_res⟩, ?_⟩
    simp only [hsp_sc]
    dsimp only [F_res]
    convert hm using 1
    sep_ac_rfl
  · intro _ _ _ _ hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro _ _ hm
    dsimp only [doReserveSpecOf] at hm
    rw [sepConj_assoc] at hm
    exact (not_satisfies_false_sepConj hm).elim
  · intro sm hpcm hrunm hspm hcsm _hcrl_sm
    rw [hsp_sc] at hspm
    dsimp only [doReserveSpecOf]
    rw [hsp_sc]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    set newCap := BitVec.ofNat 64 (reserveCap cap.toNat bs.length 1)
    rw [stack_slot_eq_header_rest A.repAlloc s0.sp newCap newPtr bs]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hle_new, hcap_new, hptr_new⟩ => ?_
    have hlt_new : bs.length < newCap.toNat := by
      dsimp only [newCap, reserveCap]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have htrm' : sm.trace = s0.trace := htrm.trans htr_sc
    have hcs_sm : DecimalCalleeSavedP s0 sm :=
      hcs_call.trans (DecimalCalleeSavedP.of_calleeSavedPreserved hcsm)
    have hx19m : sm.readReg64 .x19 = x.ret := by
      rw [hcsm.1]; simp only [sc, arm64_norm, wp_norm, *]
    have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
      rw [hcsm.2.1]; simp only [sc, arm64_norm, wp_norm, *]
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 bs.length := by
      rw [hcsm.2.2.1]; simp only [sc, arm64_norm, wp_norm, *]
    wp_steps_sync_pool ((blkPl_597).base + 76#64)
    refine SepWPp.weaken_pre ?_
      (step_push_epilogue_p hk hstk64 newCap newPtr v0 v7 o0 o1 o2 bs
        hnewCap_eq hst_after hlt_new hcap_new hptr_new hbs
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) halign (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
        (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
    dsimp only [F_res]
    rw [← stack_slot_of_header_rest A.repAlloc s0.sp newCap newPtr bs hle_new hcap_new hptr_new,
      hsplit_bot]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 4. Inductive Depth-Bounded Proof & Top-Level `decimal_placed_ok_main` -/

theorem decimal_bounded_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim))) :
    ∀ k : Nat, 1 ≤ k →
      subroutine_ok (lsProg_597 H) (blkPl_597).base
        (decimalBoundedSpecPlaced A lim k resStack) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    apply subroutine_ok_of_sepWPp
    intro ⟨x, st⟩ R s0 hpc hrun hpre halign
    obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
    refine ⟨(decimalBoundedRawSpecP A lim (k + 1) resStack).pre (x, st) s0, R, hpre, ?_⟩
    have hstk64 : (k + 1) * 0x50 + resStack ≤ 2 ^ 64 := by
      have hm_sub : s0.mem ⊨ stackAt s0.sp ((k + 1) * 0x50 + resStack) ∗
          (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg32 .x1 = x.n ∧ x.n.toNat < 10 ^ (k + 1) ∧
              FitsEnv M lim st (DecimalEnv x.n)⌝ ∗
            memRegion x.ret 24 ∗ A.pool lim st s0 ∗ R) := by
        dsimp only [decimalBoundedRawSpecP] at hpre
        convert hpre using 1
        sep_ac_rfl
      exact stk_le_pow64_of_roLoaded hcrl0.2 hm_sub
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    dsimp only [decimalBoundedRawSpecP]
    refine SepWPp.pure_elim fun ⟨hx0, hx1, hn_lt, hfits_env⟩ => ?_
    have hfits0 : FitsEvents M lim st (decimalEvents x.n) := FitsEnv.eq_iff.mp hfits_env
    have hx1' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 1#5)) = x.n := hx1
    have hframe0 := stackAt_decimal_frame_p (m := k * 0x50 + resStack) (by omega) s0.sp
    have hstk_eq0 : k * 0x50 + resStack + 0x50 = (k + 1) * 0x50 + resStack := by omega
    rw [hstk_eq0] at hframe0
    rw [memRegion_24_cells x.ret, hframe0]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => ?_
    refine SepWPp.exists_elim fun v1 => ?_
    refine SepWPp.exists_elim fun v2 => ?_
    refine SepWPp.exists_elim fun v3 => ?_
    refine SepWPp.exists_elim fun v4 => ?_
    refine SepWPp.exists_elim fun v5 => ?_
    refine SepWPp.exists_elim fun v6 => ?_
    refine SepWPp.exists_elim fun v7 => ?_
    refine SepWPp.exists_elim fun v8 => ?_
    refine SepWPp.exists_elim fun v9 => ?_
    refine SepWPp.exists_elim fun o2 => ?_
    refine SepWPp.exists_elim fun o1 => ?_
    refine SepWPp.exists_elim fun o0 => ?_
    by_cases hle9 : x.n.toNat ≤ 9
    · have hule := ule_nine_true hle9
      apply sepWPp_seq_lscro hcrl0 (mid := (blkPl_597).base + 168#64)
      wp_steps_sync_pool ((blkPl_597).base + 168#64)
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl_pro
      have hbs0 : ([] : List (BitVec 8)) ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
          decimalText x.n.toNat := by
        rw [List.nil_append, Nat.mod_eq_of_lt (by omega), decimalText_digit x.n.toNat (by omega)]
      have hlen1 : (decimalText x.n.toNat).length = 1 := by
        rw [← hbs0]; rfl
      have hstep0 := pushByteStep_of_eq (s0.sp - 72#64) 0#64 1#64 [] rfl
      have hevs0 : decimalEvents x.n =
          doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) 0#64 1#64 [] 1) := by
        unfold decimalEvents
        rw [hlen1]
        dsimp only [pushBytesEvents, List.length_nil]
        rw [List.append_nil]
        exact congrArg Prod.snd hstep0
      have hcap0_eq : BitVec.ofNat 64 (reserveCap (0#64).toNat ([] : List (BitVec 8)).length 1) =
          decimalCap x.n := by
        unfold decimalCap
        rw [hlen1]
        dsimp only [pushBytesCap, List.length_nil]
        rw [show (0#64).toNat = 0 from rfl]
        exact (congrArg (BitVec.ofNat 64 ∘ Prod.fst) hstep0).symm
      have hfits_res0 : FitsEvents M lim st
          (doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) 0#64 1#64 [] 1)) := by
        rwa [← hevs0]
      refine SepWPp.weaken_pre ?_
        (step_reserve_and_finish_p (k := k + 1) hRes (by omega) hstk64 hcrl_pro
          0#64 1#64 v0 v7 o0 o1 o2 [] rfl (by decide) hbs0 hfits_res0 hcap0_eq (by rw [hevs0])
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          ((DecimalCalleeSavedP.refl s0).trans ⟨by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
            by simp only [arm64_norm, wp_norm]⟩))
      rw [← stack_slot_empty_vecU8At A.repAlloc s0.sp]
      exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; sep_ac_rfl)
    · have hge10 : 10 ≤ x.n.toNat := by omega
      have hk1 : 1 ≤ k := by
        rcases k with _ | k'
        · exfalso; omega
        · omega
      have hdiv_lt : (x.n.toNat / 10) < 10 ^ k := by
        have hp : 10 ^ (k + 1) = 10 ^ k * 10 := rfl
        omega
      have hih : subroutine_ok (lsProg_597 H) (blkPl_597).base
          (withLsCodeRoLoaded lsmpl (decimalBoundedRawSpecP A lim k resStack)) := ih hk1
      set subN : BitVec 32 := BitVec.ofNat 32 (x.n.toNat / 10)
      have hq_nat : subN.toNat = x.n.toNat / 10 := by
        have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
        dsimp only [subN]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      set subBs := decimalText (x.n.toNat / 10)
      have hbs_rec : subBs ++ [BitVec.ofNat 8 (0x30 + x.n.toNat % 10)] =
          decimalText x.n.toNat :=
        (decimalText_ge10 x.n.toNat hge10).symm
      have hlen_rec : (decimalText x.n.toNat).length = subBs.length + 1 := by
        rw [← hbs_rec, List.length_append, List.length_singleton]
      have hevs_split :
          decimalEvents x.n =
            decimalEvents subN ++
              (pushByteStep (pushBytesCap subBs.length 0 0) subBs.length).2 := by
        unfold decimalEvents
        rw [hlen_rec, hq_nat, pushBytesEvents_snoc subBs.length 0 0, Nat.zero_add]
      have hcap_rec_nat :
          pushBytesCap (decimalText x.n.toNat).length 0 0 =
            (pushByteStep (pushBytesCap subBs.length 0 0) subBs.length).1 := by
        rw [hlen_rec, pushBytesCap_snoc subBs.length 0 0, Nat.zero_add]
      have hfits_pair :
          FitsEvents M lim st (decimalEvents subN) ∧
            FitsEvents M lim (M.stepEvents (decimalEvents subN) st)
              (pushByteStep (pushBytesCap subBs.length 0 0) subBs.length).2 := by
        rwa [hevs_split, fitsEvents_append] at hfits0
      have hule := ule_nine_false hge10
      apply sepWPp_seq_lscro hcrl0 (mid := (blkPl_597).base)
      wp_steps_sync_pool (blkPl_597).base
      apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hcrl_sr
      apply sepWPp_let_state; intro sr
      have hcs_sr : DecimalCalleeSavedP s0 sr :=
        (DecimalCalleeSavedP.refl s0).trans ⟨by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm], by simp only [sr, arm64_norm, wp_norm],
          by simp only [sr, arm64_norm, wp_norm]⟩
      have hsp_sr : sr.sp = s0.sp - 80#64 := by simp only [sr, arm64_norm, wp_norm]
      have htr_sr : sr.trace = s0.trace := by simp only [sr, arm64_norm, wp_norm]
      have hsp_sr_aligned : sr.spAligned = true := by
        simp only [State.spAligned, hsp_sr, beq_iff_eq]
        exact sp_sub_80_aligned halign64
      set F_rec : SepProp :=
        ((s0.sp - 80#64) ↦₆₄ v0) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 24#64) ↦₆₄ v7) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.ret ↦₆₄ o0) ∗ ((x.ret + 8#64) ↦₆₄ o1) ∗ ((x.ret + 16#64) ↦₆₄ o2)
      refine call_lscro
        (x := (DecimalGhost.mk subN (s0.sp - 72#64), st))
        (ret_pc := (blkPl_597).base + 60#64)
        (F := F_rec)
        hih hcrl_sr
        (by simp only [sr, arm64_norm, wp_norm])
        (by simp only [sr, arm64_norm, wp_norm, *])
        hsp_sr_aligned
        (by simp only [sr, arm64_norm, wp_norm])
        ?_ ?_ ?_ ?_
      · intro R' hm
        have hm' : sr.mem ⊨
            memRegion (s0.sp - 72#64) 24 ∗ stackAt (s0.sp - 80#64) (k * 0x50 + resStack) ∗
              A.pool lim st sr ∗ F_rec ∗ R' := by
          have hv8 : s0.sp - 72#64 + 8#64 = s0.sp - 64#64 := by bv_omega
          have hv16 : s0.sp - 72#64 + 16#64 = s0.sp - 56#64 := by bv_omega
          rw [memRegion_24_cells (s0.sp - 72#64), hv8, hv16]
          simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨v3, v2, v1, ?_⟩
          dsimp only [F_rec]
          convert hm using 1
          sep_ac_rfl
        simp only [decimalBoundedRawSpecP, hsp_sr, sepConj_assoc, satisfies_pure_sepConj]
        have hx1_sr : sr.readReg32 .x1 = subN := by
          change BitVec.truncate 32 (sr.readReg64 (Reg.gpr 1#5)) = _
          simp only [sr, arm64_norm, wp_norm]
          exact div10_trunc32 x.n
        have hn_sub_lt : subN.toNat < 10 ^ k := by
          rw [hq_nat]; exact hdiv_lt
        exact ⟨⟨by simp only [sr, arm64_norm, wp_norm], hx1_sr, hn_sub_lt,
          FitsEnv.eq_iff.mpr hfits_pair.1⟩, hm'⟩
      · intro _ _ _ _ hm
        exact (not_satisfies_false_sepConj hm).elim
      · intro _ _ hm
        dsimp only [decimalBoundedRawSpecP] at hm
        rw [sepConj_assoc] at hm
        exact (not_satisfies_false_sepConj hm).elim
      · intro sm hpcm hrunm hspm hcsm hcrl_sm
        rw [hsp_sr] at hspm
        conv =>
          arg 4
          dsimp only [decimalBoundedRawSpecP]
          rw [hsp_sr, hq_nat]
          simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun htrm => ?_
        conv =>
          arg 4
          simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun subPtr => ?_
        set subCap := decimalCap subN
        have hsubCap_nat : subCap.toNat = pushBytesCap subBs.length 0 0 := by
          dsimp only [subCap, subBs]
          rw [decimalCap_toNat subN, hq_nat]
        conv =>
          arg 4
          rw [stack_slot_eq_header_rest A.repAlloc s0.sp subCap subPtr subBs]
          simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hle_sub, hcap_sub, hptr_sub⟩ => ?_
        have htrm' : sm.trace = s0.trace := htrm.trans htr_sr
        have hcs_sm : DecimalCalleeSavedP s0 sm :=
          hcs_sr.trans (DecimalCalleeSavedP.of_calleeSavedPreserved hcsm)
        have hx19m : sm.readReg64 .x19 = x.ret := by
          rw [hcsm.1]; simp only [sr, arm64_norm, wp_norm]
        have hx20m : sm.readReg64 .x20 = BitVec.zeroExtend 64 x.n := by
          rw [hcsm.2.1]; simp only [sr, arm64_norm, wp_norm]
        have hlen_sub9 : subBs.length ≤ 9 := by
          have hn32 : x.n.toNat < 2 ^ 32 := x.n.isLt
          exact decimalText_length_le 9 (x.n.toNat / 10) (by omega) (by omega)
        by_cases hlt_sub : subBs.length < subCap.toNat
        · have hbeq_f := cap_beq_len_false hlt_sub
          have hlt_nat : subBs.length < pushBytesCap subBs.length 0 0 := by
            rwa [← hsubCap_nat]
          have hstep_lt := pushByteStep_of_lt hlt_nat
          have hcap_same : subCap = decimalCap x.n := by
            dsimp only [subCap, decimalCap]
            rw [hq_nat, hcap_rec_nat, hstep_lt]
          have hst_same :
              M.stepEvents (decimalEvents x.n) st = M.stepEvents (decimalEvents subN) st := by
            rw [hevs_split, hstep_lt, List.append_nil]
          have hbeq_f' : (decimalCap x.n == BitVec.ofNat 64 subBs.length) = false :=
            hcap_same ▸ hbeq_f
          wp_steps_sync_pool ((blkPl_597).base + 76#64)
          refine SepWPp.weaken_pre ?_
            (step_push_epilogue_p (A := A) (lim := lim) (k := k + 1) (R := R) (by omega) hstk64
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hcap_same hst_same hlt_sub hcap_sub hptr_sub hbs_rec
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A.repAlloc s0.sp subCap subPtr subBs
            hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; sep_ac_rfl)
        · have hcap_eq_sub : subCap.toNat = subBs.length := by omega
          have hbeq_t := cap_beq_len_true hcap_eq_sub
          have hstep_eq := pushByteStep_of_eq (s0.sp - 72#64) subCap subPtr subBs hcap_eq_sub
          have hfits_res_sub :
              FitsEvents M lim (M.stepEvents (decimalEvents subN) st)
                (doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) subCap subPtr subBs 1)) := by
            have hf := hfits_pair.2
            rw [← hsubCap_nat, hstep_eq] at hf
            exact hf
          have hnewCap_sub :
              BitVec.ofNat 64 (reserveCap subCap.toNat subBs.length 1) = decimalCap x.n := by
            unfold decimalCap
            rw [hcap_rec_nat, ← hsubCap_nat, hstep_eq, hcap_eq_sub]
          have hst_after_sub :
              M.stepEvents (decimalEvents x.n) st =
                M.stepEvents
                  (doReserveEvents (DoReserveCall.mk (s0.sp - 72#64) subCap subPtr subBs 1))
                  (M.stepEvents (decimalEvents subN) st) := by
            rw [hevs_split, ← hsubCap_nat, hstep_eq, M.stepEvents_append]
          apply sepWPp_seq_lscro hcrl_sm (mid := (blkPl_597).base + 168#64)
          wp_steps_sync_pool ((blkPl_597).base + 168#64)
          apply SepWP.done (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hcrl_chk
          refine SepWPp.weaken_pre ?_
            (step_reserve_and_finish_p (k := k + 1) (R := R) hRes (by omega) hstk64 hcrl_chk
              subCap subPtr v0 v7 o0 o1 o2 subBs
              hcap_eq_sub hlen_sub9 hbs_rec hfits_res_sub hnewCap_sub hst_after_sub
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) halign64 (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm]; exact beq_iff_eq.mp hbeq_t)
              (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (hcs_sm.trans ⟨by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
                by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩))
          dsimp only [F_rec]
          rw [← stack_slot_of_header_rest A.repAlloc s0.sp subCap subPtr subBs
            hle_sub hcap_sub hptr_sub]
          exact Entails.of_eq (by simp only [Nat.add_sub_cancel]; sep_ac_rfl)

theorem decimal_placed_ok_main [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack stk : Nat}
    (hRes : subroutine_ok (lsProg_597 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hstk : 10 * 0x50 + resStack ≤ stk) :
    subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecimalEnv stk) := by
  have h10 : subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalBoundedSpecPlaced A lim 10 resStack) :=
    decimal_bounded_placed_ok hRes 10 (by omega)
  have h10_spec : subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecimalEnv (10 * 0x50 + resStack)) := by
    refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre halign _ => ?_
    obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hn10 : x.n.toNat < 10 ^ 10 := by
      have := x.n.isLt
      omega
    have hpre' : s0.mem ⊨ (decimalBoundedSpecPlaced A lim 10 resStack).pre (x, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl0 ?_
      dsimp only [decimalSpecPlaced, decimalBoundedRawSpecP] at hpre0 ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hn10, hpre0.1.2.2⟩, hpre0.2⟩
    refine h10.mono_outcome (x, st) R s0 hpc hrun hpre' halign fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [decimalSpecPlaced, decimalBoundedSpecPlaced, withLsCodeRoLoaded,
        decimalBoundedRawSpecP] at hpost ⊢
      rw [vecU8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      obtain ⟨ptr, htr, hm⟩ := hpost
      exact ⟨decimalEvents x.n, decimalCap x.n, ptr, ⟨htr, rfl⟩, hm⟩
    · exact (not_satisfies_false_sepConj hpan).elim
    · exact (not_satisfies_false_sepConj hex).elim
    · exact (not_satisfies_false_sepConj hoom).elim
  exact lift_stk_lscro_budget h10_spec hstk
    (P := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n ∧ FitsEnv M lim st (DecimalEnv x.n)⌝ ∗
        memRegion x.ret 24 ∗ A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜sf.trace = s0.trace ∧ DecimalEnv x.n evs⌝ ∗
          vecU8 A.repAlloc x.ret (decimalText x.n.toNat) ∗
          A.pool lim (M.stepEvents evs st) sf)
    (fun _ _ _ => by dsimp only [decimalSpecPlaced, withLsCodeRoLoaded]; sep_ac_rfl)
    (fun _ _ _ _ => by
      dsimp only [decimalSpecPlaced, withLsCodeRoLoaded]
      rw [sepExists_sepConj_left]
      exact congrArg sepExists (funext fun evs => by sep_ac_rfl))

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
