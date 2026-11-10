/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.Repr
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap

/-!
# Shared Representation Predicates and Helpers for SPQR V1 Drop Glue

Stack frame budgets (`dropStack32`, `dropStack48`, `dropStack80`), callee-saved register
preservation predicates, stride-112 arithmetic, `Vec<u8>` / `ChainEpoch` / `proto::chain::Epoch`
deallocation entailments, and `VecDeque` ring-buffer exposure lemmas.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem sub_ok_of_addr_eq {α : Type} {prog : Program} {a₁ a₂ : BitVec 64} {spec : Spec α}
    (heq : a₁ = a₂) (h : subroutine_ok prog a₁ spec) : subroutine_ok prog a₂ spec :=
  heq ▸ h

/-! ## Stack Budgets and Frame Split / Restore Helpers -/

/-- Stack budget for a 32-byte (`0x20`) frame calling `__rust_dealloc`. -/
abbrev dropStack32 : Nat := allocHookStack + 32

/-- Stack budget for a 48-byte (`0x30`) frame calling `__rust_dealloc`. -/
abbrev dropStack48 : Nat := allocHookStack + 48

/-- Stack budget for a 48-byte (`0x30`) frame calling a `dropStack32` subroutine. -/
abbrev dropStack80 : Nat := dropStack32 + 48

theorem stackAt_dropStack32_split (sp : BitVec 64) :
    stackAt sp dropStack32 =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp allocHookStack 4 (by decide)

theorem stackAt_dropStack48_split (sp : BitVec 64) :
    stackAt sp dropStack48 =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp allocHookStack 6 (by decide)

/-- Split the 48-byte frame off the bottom of `dropStack48`, leaving the `__rust_dealloc` hook budget on top. -/
theorem stackAt_dropStack48_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack48 = memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 48 (by decide)

theorem stackAt_dropStack80_split (sp : BitVec 64) :
    stackAt sp dropStack80 =
      stackAt (sp - 48#64) dropStack32 ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp dropStack32 6 (by decide)

theorem cells4_sub32_entails (sp fp lr x20 x19 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    cells (sp - 32#64) 4 := by
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

theorem cells6_sub48_entails (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    cells (sp - 48#64) 6 := by
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x22 (Entails.sepExists_right x21
      (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))

theorem stack_restore_32_allocHook (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack32 := by
  rw [stackAt_dropStack32_split sp]
  exact sepConj_mono_right (cells4_sub32_entails sp fp lr x20 x19)

theorem stack_restore_48_allocHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) allocHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack48 := by
  rw [stackAt_dropStack48_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem stack_restore_48_dropStack80 (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropStack32 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack80 := by
  rw [stackAt_dropStack80_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem tail_stack_48_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom sp allocHookStack 48 (by decide),
      show allocHookStack + 48 = dropStack48 from rfl,
      ← stackAt_dropStack48_split sp]

theorem tail_stack_48_from_dropStack80_bottom (sp : BitVec 64) :
    memRegion (sp - 4176#64) 80 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropStack32 ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom sp allocHookStack 80 (by decide),
      show allocHookStack + 80 = dropStack80 from rfl,
      ← stackAt_dropStack80_split sp]

theorem stackAt_dropStack32_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack32 = memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 32 (by decide)

theorem stackAt_dropStack80_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack80 = memRegion (sp - 4176#64) 80 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 80 (by decide)

/-! ### 16 KiB (`16384`) hook-budget stack helpers -/

abbrev dropStack32X : Nat := 16384 + 32

abbrev dropStack48X : Nat := 16384 + 48

abbrev dropStack80X : Nat := dropStack32X + 48

theorem stackAt_dropStack32X_split (sp : BitVec 64) :
    stackAt sp dropStack32X =
      stackAt (sp - 32#64) 16384 ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp 16384 4 (by decide)

theorem stackAt_dropStack48X_split (sp : BitVec 64) :
    stackAt sp dropStack48X =
      stackAt (sp - 48#64) 16384 ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp 16384 6 (by decide)

theorem stackAt_dropStack48X_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack48X = memRegion (sp - 16432#64) 48 ∗ stackAt sp 16384 :=
  stackAt_split_bottom sp 16384 48 (by decide)

theorem stackAt_dropStack80X_split (sp : BitVec 64) :
    stackAt sp dropStack80X =
      stackAt (sp - 48#64) dropStack32X ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp dropStack32X 6 (by decide)

theorem stack_restore_32_extHook (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) 16384 ∗
      (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack32X := by
  rw [stackAt_dropStack32X_split sp]
  exact sepConj_mono_right (cells4_sub32_entails sp fp lr x20 x19)

theorem stack_restore_48_extHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) 16384 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack48X := by
  rw [stackAt_dropStack48X_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem stack_restore_48_dropStack80X (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropStack32X ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack80X := by
  rw [stackAt_dropStack80X_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem stackAt_dropStack32X_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack32X = memRegion (sp - 16416#64) 32 ∗ stackAt sp 16384 :=
  stackAt_split_bottom sp 16384 32 (by decide)

theorem stackAt_dropStack80X_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack80X = memRegion (sp - 16464#64) 80 ∗ stackAt sp 16384 :=
  stackAt_split_bottom sp 16384 80 (by decide)

theorem tail_stack_48_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16432#64) 48 ∗ stackAt sp 16384 =
      stackAt (sp - 48#64) 16384 ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_dropStack48X_split_bottom sp, ← stackAt_dropStack48X_split sp]

theorem tail_stack_48_from_dropStack80X_bottom (sp : BitVec 64) :
    memRegion (sp - 16464#64) 80 ∗ stackAt sp 16384 =
      stackAt (sp - 48#64) dropStack32X ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_dropStack80X_split_bottom sp, ← stackAt_dropStack80X_split sp]

/-- Callee-saved registers not saved in `[sp..sp+32]` when `x19, x20, x29, x30` ARE saved in `[sp..sp+32]`. -/
@[reducible]
def Saved32x20Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-- Callee-saved registers not saved in `[sp..sp+48]` when `x19..x22, x29, x30` ARE saved in `[sp..sp+48]`. -/
@[reducible]
def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-! ## `SepWP` and Stride-112 Arithmetic Helpers -/

theorem seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

theorem SepWP.exists_left {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ x : α, SepWP prog target_pc s (P x) post) :
    SepWP prog target_pc s (∃∗ x, P x) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx

theorem SepWP.exists_sepConj_left {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ x : α, SepWP prog target_pc s (P x ∗ Rest) post) :
    SepWP prog target_pc s ((∃∗ x, P x) ∗ Rest) post := by
  rw [sepExists_sepConj_left]
  exact SepWP.exists_left h

theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

theorem ofNat_ne_zero_of_pos_112 {n : Nat} (hpos : 0 < n) (hlt : n * 112 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

theorem ofNat_beq_zero_false_112 {n : Nat} (hpos : 0 < n) (hlt : n * 112 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos_112 hpos hlt

theorem ofNat_add_one_beq_one_false_112 {n : Nat} (hpos : 0 < n) (hlt : n * 112 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos_112 hpos hlt h0

theorem tail_len_mul_lt {α : Type} {x : α} {xs : List α} {k m : Nat}
    (h : (x :: xs).length * k < m) : xs.length * k < m := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega

theorem cons_len_mul {α : Type} (x : α) (xs : List α) (k : Nat) :
    (x :: xs).length * k = k + xs.length * k := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

theorem add_112_add_56 (cur : BitVec 64) : cur + 112#64 + 56#64 = cur + 168#64 := by
  bv_omega

theorem sep_pull_body (M Arr Pool Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by ac_rfl

theorem sep_push_body (M Arr Pool Stk Frame : SepProp) :
    M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Pool ∗ Stk ∗ (M ∗ Frame) := by ac_rfl

theorem sep_rejoin_loop (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by ac_rfl

theorem cap_lsl7_sub_lsl4 {cap : BitVec 64} (h : cap.toNat * 112 < 2 ^ 63) :
    ((cap <<< 7#64) - (cap <<< 4#64)).toNat = cap.toNat * 112 := by
  have h7 : (cap <<< 7#64).toNat = cap.toNat * 128 := by
    have h1 : (cap <<< 7#64).toNat = (cap.toNat <<< 7) % 2 ^ 64 := by
      simp [BitVec.toNat_shiftLeft]
    have h2 : cap.toNat <<< 7 = cap.toNat * 128 := Nat.shiftLeft_eq cap.toNat 7
    rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
  have h4 : (cap <<< 4#64).toNat = cap.toNat * 16 := by
    have h1 : (cap <<< 4#64).toNat = (cap.toNat <<< 4) % 2 ^ 64 := by
      simp [BitVec.toNat_shiftLeft]
    have h2 : cap.toNat <<< 4 = cap.toNat * 16 := Nat.shiftLeft_eq cap.toNat 4
    rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
  have hsub : ((cap <<< 7#64) - (cap <<< 4#64)).toNat = (cap <<< 7#64).toNat - (cap <<< 4#64).toNat := by
    apply BitVec.toNat_sub_of_le
    rw [BitVec.le_def, h7, h4]
    omega
  rw [hsub, h7, h4]
  omega

@[simp, arm64_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ¬((cap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have hmax : cap = 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
  subst hmax
  revert h
  decide

theorem ult_of_toNat_lt {a b : BitVec 64} (h : a.toNat < b.toNat) : a.ult b = true := by
  rw [BitVec.ult_iff_toNat_lt]
  exact h

theorem ule_sub_of_le {cap head : BitVec 64} {len : Nat}
    (hcap : cap.toNat < 2 ^ 63) (hhead : head.toNat < cap.toNat)
    (hle : len ≤ cap.toNat - head.toNat) :
    (BitVec.ofNat 64 len).ule (cap - head) = true := by
  rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  exact hle

theorem not_ule_sub_of_gt {cap head : BitVec 64} {len : Nat}
    (hcap : cap.toNat < 2 ^ 63) (hhead : head.toNat < cap.toNat)
    (hlen : len ≤ cap.toNat) (hgt : cap.toNat - head.toNat < len) :
    ¬((BitVec.ofNat 64 len).ule (cap - head) = true) := by
  rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
  omega

theorem add_sub_cancel_left_bv (a b : BitVec 64) : a + b - a = b := by
  bv_omega

theorem mul_112_add_ptr (head ptr : BitVec 64) :
    head * 112#64 + ptr = ptr + BitVec.ofNat 64 (head.toNat * 112) := by
  have hmul : head * 112#64 = BitVec.ofNat 64 (head.toNat * 112) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  rw [hmul, BitVec.add_comm]

theorem sub_eq_ofNat_sub {cap head : BitVec 64} (hhead : head.toNat ≤ cap.toNat) :
    cap - head = BitVec.ofNat 64 (cap.toNat - head.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : cap.toNat - head.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hhead),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem ofNat_sub_sub_eq {cap head : BitVec 64} {len : Nat}
    (hcap : cap.toNat < 2 ^ 63) (hhead : head.toNat < cap.toNat)
    (hgt : cap.toNat - head.toNat ≤ len) (hlen : len ≤ cap.toNat) :
    BitVec.ofNat 64 len - (cap - head) = BitVec.ofNat 64 (len - (cap.toNat - head.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have hsub : (cap - head).toNat = cap.toNat - head.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hsub, hlen_bv]; exact hgt),
      hlen_bv, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]


/-! ## Deallocation Entailments for `Vec<u8>`, `ChainEpoch`, and `proto::chain::Epoch` -/

theorem pointsTo64_entails_memRegion (a v : BitVec 64) : (a ↦₆₄ v) ⊢ memRegion a 8 :=
  IsBlock.entails (IsBlock.pointsTo64 a v) (IsBlock.memRegion a 8) fun _ _ => trivial

theorem pointsTo32_entails_memRegion (a : BitVec 64) (v : BitVec 32) : (a ↦₃₂ v) ⊢ memRegion a 4 :=
  IsBlock.entails (IsBlock.pointsTo32 a v) (IsBlock.memRegion a 4) fun _ _ => trivial

theorem vecU8At_entails_dealloc (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8At
  apply sepConj_mono_right
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  refine Entails.pure_right ⟨hle, hcap_lt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · simp [hcap]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    have hbound : bs.length + (cap.toNat - bs.length) ≤ 2 ^ 64 := by omega
    conv_rhs => arg 2; rw [hsplit, ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) hbound]
    exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))

def vecCapPtrDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if (cap == 0#64) = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem header_cells_entails_memRegion_24 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem header_cells_entails_memRegion_32 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16) ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem vecU8At_entails_capPtr_dealloc (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecCapPtrDealloc A cap ptr := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader vecCapPtrDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro _
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem vecU8At_entails_capPtr_dealloc_bound (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecCapPtrDealloc A cap ptr := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader vecCapPtrDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  refine Entails.pure_right hcap_lt ?_
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem vecU8_entails_capPtr_dealloc (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
        vecCapPtrDealloc A cap ptr := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (vecU8At_entails_capPtr_dealloc A a cap ptr bs))

theorem vecU8_entails_capPtr_dealloc_bound (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
        vecCapPtrDealloc A cap ptr := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (vecU8At_entails_capPtr_dealloc_bound A a cap ptr bs))

@[reducible]
def chainEpochHeadersAt (cur : BitVec 64) (g : ChainEpochGhost) : SepProp :=
  (cur ↦₆₄ g.send.next.cap) ∗ ((cur + 8#64) ↦₆₄ g.send.next.ptr) ∗ memRegion (cur + 16#64) 8 ∗
  ((cur + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((cur + 32#64) ↦₆₄ g.send.prev.ptr) ∗ memRegion (cur + 40#64) 16 ∗
  ((cur + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((cur + 64#64) ↦₆₄ g.recv.next.ptr) ∗ memRegion (cur + 72#64) 8 ∗
  ((cur + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((cur + 88#64) ↦₆₄ g.recv.prev.ptr) ∗ memRegion (cur + 96#64) 16

theorem chainEpochHeadersAt_entails_memRegion_112 (cur : BitVec 64) (g : ChainEpochGhost) :
    chainEpochHeadersAt cur g ⊢ memRegion cur 112 := by
  unfold chainEpochHeadersAt
  have h1 := header_cells_entails_memRegion_24 cur g.send.next.cap g.send.next.ptr
  have h2 := header_cells_entails_memRegion_32 (cur + 24#64) g.send.prev.cap g.send.prev.ptr
  have h3 := header_cells_entails_memRegion_24 (cur + 56#64) g.recv.next.cap g.recv.next.ptr
  have h4 := header_cells_entails_memRegion_32 (cur + 80#64) g.recv.prev.cap g.recv.prev.ptr
  have ha1 : (cur + 24#64) + 8#64 = cur + 32#64 := by bv_omega
  have ha2 : (cur + 24#64) + 16#64 = cur + 40#64 := by bv_omega
  have hb1 : (cur + 56#64) + 8#64 = cur + 64#64 := by bv_omega
  have hb2 : (cur + 56#64) + 16#64 = cur + 72#64 := by bv_omega
  have hc1 : (cur + 80#64) + 8#64 = cur + 88#64 := by bv_omega
  have hc2 : (cur + 80#64) + 16#64 = cur + 96#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  have hgroup :
      ((cur ↦₆₄ g.send.next.cap) ∗ ((cur + 8#64) ↦₆₄ g.send.next.ptr) ∗ memRegion (cur + 16#64) 8 ∗
        ((cur + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((cur + 32#64) ↦₆₄ g.send.prev.ptr) ∗ memRegion (cur + 40#64) 16 ∗
        ((cur + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((cur + 64#64) ↦₆₄ g.recv.next.ptr) ∗ memRegion (cur + 72#64) 8 ∗
        ((cur + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((cur + 88#64) ↦₆₄ g.recv.prev.ptr) ∗ memRegion (cur + 96#64) 16) =
      (((cur ↦₆₄ g.send.next.cap) ∗ ((cur + 8#64) ↦₆₄ g.send.next.ptr) ∗ memRegion (cur + 16#64) 8) ∗
       (((cur + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((cur + 32#64) ↦₆₄ g.send.prev.ptr) ∗ memRegion (cur + 40#64) 16) ∗
       (((cur + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((cur + 64#64) ↦₆₄ g.recv.next.ptr) ∗ memRegion (cur + 72#64) 8) ∗
       (((cur + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((cur + 88#64) ↦₆₄ g.recv.prev.ptr) ∗ memRegion (cur + 96#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := cur) (n := 24) (k := 88) (b' := cur + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := cur + 24#64) (n := 32) (k := 56) (b' := cur + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := cur + 56#64) (n := 24) (k := 32) (b' := cur + 80#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))

theorem chainEpochDirectionAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) :
    chainEpochDirectionAt A a g ced ⊢
      (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ memRegion (a + 16#64) 8 ∗
      ((a + 24#64) ↦₆₄ g.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.prev.ptr) ∗ memRegion (a + 40#64) 16 ∗
      vecCapPtrDealloc A g.next.cap g.next.ptr ∗
      vecCapPtrDealloc A g.prev.cap g.prev.ptr := by
  unfold chainEpochDirectionAt keyHistoryAt
  have h1 := vecU8At_entails_capPtr_dealloc A a g.next.cap g.next.ptr ced.next
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) g.prev.cap g.prev.ptr ced.prev.data
  have h3 : ((a + 48#64) ↦₃₂ ced.ctr) ∗ memRegion (a + 52#64) 4 ⊢ memRegion (a + 48#64) 8 := by
    rw [ProofLib.memRegion_split' (b := a + 48#64) (n := 4) (k := 4)
          (b' := a + 52#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  have h16 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 8 = memRegion (a + 40#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8)
          (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  rw [← h16]
  exact Entails.of_eq (by ac_rfl)

theorem chainEpochAt_entails_dealloc (A : RustAlloc) (cur : BitVec 64)
    (g : ChainEpochGhost) (ce : ChainEpoch) :
    chainEpochAt A (g, ce) cur ⊢
      chainEpochHeadersAt cur g ∗
      vecCapPtrDealloc A g.send.next.cap g.send.next.ptr ∗
      vecCapPtrDealloc A g.send.prev.cap g.send.prev.ptr ∗
      vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
      vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr := by
  unfold chainEpochAt chainEpochHeadersAt
  have h1 := chainEpochDirectionAt_entails_dealloc A cur g.send ce.send
  have h2 := chainEpochDirectionAt_entails_dealloc A (cur + 56#64) g.recv ce.recv
  have hb1 : (cur + 56#64) + 8#64 = cur + 64#64 := by bv_omega
  have hb2 : (cur + 56#64) + 16#64 = cur + 72#64 := by bv_omega
  have hb3 : (cur + 56#64) + 24#64 = cur + 80#64 := by bv_omega
  have hb4 : (cur + 56#64) + 32#64 = cur + 88#64 := by bv_omega
  have hb5 : (cur + 56#64) + 40#64 = cur + 96#64 := by bv_omega
  rw [hb1, hb2, hb3, hb4, hb5] at h2
  refine Entails.trans (sepConj_mono h1 h2) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## `VecDeque` Physical Slot Splitting and Exposure Lemmas -/

theorem vecDequeSlotsAt_occupied_entails_arrayAt {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (m : Nat) :
    ∀ (s : Nat),
      (∀ k < m, vecDequeLogIdx head cap (s + k) < xs.length) →
      ∃ ys : List α, ys.length = m ∧
        (vecDequeSlotsAt elem stride cap head ptr xs s m ⊢
          arrayAt elem stride (ptr + BitVec.ofNat 64 (s * stride)) ys) := by
  induction m with
  | zero =>
    intro s _
    exact ⟨[], rfl, Entails.refl _⟩
  | succ m ih =>
    intro s hocc
    have h0 : vecDequeLogIdx head cap s < xs.length := by
      simpa using hocc 0 (by omega)
    have htl : ∀ k < m, vecDequeLogIdx head cap ((s + 1) + k) < xs.length := by
      intro k hk
      have hk' : (s + 1) + k = s + (k + 1) := by omega
      rw [hk']
      exact hocc (k + 1) (by omega)
    obtain ⟨ys, hlen, hent⟩ := ih (s + 1) htl
    refine ⟨xs[vecDequeLogIdx head cap s]'h0 :: ys, by simp [hlen], ?_⟩
    simp only [vecDequeSlotsAt, h0, ↓reduceDIte, arrayAt]
    have haddr : ptr + BitVec.ofNat 64 (s * stride) + BitVec.ofNat 64 stride =
        ptr + BitVec.ofNat 64 ((s + 1) * stride) := by
      rw [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [haddr]
    exact sepConj_mono_right hent

theorem vecDequeSlotsAt_unoccupied_entails_memRegion {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α) (m : Nat) :
    ∀ (s : Nat),
      (s + m) * stride ≤ 2 ^ 64 →
      (∀ k < m, ¬(vecDequeLogIdx head cap (s + k) < xs.length)) →
      vecDequeSlotsAt elem stride cap head ptr xs s m ⊢
        memRegion (ptr + BitVec.ofNat 64 (s * stride)) (m * stride) := by
  induction m with
  | zero =>
    intro s _ _
    simp only [vecDequeSlotsAt, Nat.zero_mul, memRegion_zero]
    exact Entails.refl _
  | succ m ih =>
    intro s hbound hunocc
    have h0 : ¬(vecDequeLogIdx head cap s < xs.length) := by
      simpa using hunocc 0 (by omega)
    have htl : ∀ k < m, ¬(vecDequeLogIdx head cap ((s + 1) + k) < xs.length) := by
      intro k hk
      have hk' : (s + 1) + k = s + (k + 1) := by omega
      rw [hk']
      exact hunocc (k + 1) (by omega)
    have hbound_tl : (s + 1 + m) * stride ≤ 2 ^ 64 := by
      have heq : s + 1 + m = s + (m + 1) := by omega
      rwa [heq]
    have hent := ih (s + 1) hbound_tl htl
    simp only [vecDequeSlotsAt, h0, ↓reduceDIte]
    have hsplit : (m + 1) * stride = stride + m * stride := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hsplit_bound : stride + m * stride ≤ 2 ^ 64 := by
      have : (m + 1) * stride ≤ (s + (m + 1)) * stride :=
        Nat.mul_le_mul_right stride (by omega)
      omega
    have haddr : ptr + BitVec.ofNat 64 (s * stride) + BitVec.ofNat 64 stride =
        ptr + BitVec.ofNat 64 ((s + 1) * stride) := by
      rw [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [hsplit, ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (s * stride)) stride (m * stride) hsplit_bound, haddr]
    exact sepConj_mono_right hent

/-! ## `VecDeque` Exposure / Rejoin and `Chain` / `ChainPB` Deallocation Lemmas -/

theorem vecU8At_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢ vecU8 A a bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem chainEpochDirectionAt_entails_chainEpochDirection (A : RustAlloc) (a : BitVec 64)
    (g : ChainEpochDirectionGhost) (ced : ChainEpochDirection) :
    chainEpochDirectionAt A a g ced ⊢ chainEpochDirection A a ced := by
  unfold chainEpochDirectionAt chainEpochDirection keyHistoryAt keyHistory
  exact sepConj_mono (vecU8At_entails_vecU8 A a g.next.cap g.next.ptr ced.next)
    (sepConj_mono_left (vecU8At_entails_vecU8 A (a + 24#64) g.prev.cap g.prev.ptr ced.prev.data))

theorem chainEpochAt_entails_chainEpoch (A : RustAlloc) (gce : ChainEpochGhost × ChainEpoch)
    (a : BitVec 64) :
    chainEpochAt A gce a ⊢ chainEpoch A gce.2 a := by
  unfold chainEpochAt chainEpoch
  exact sepConj_mono (chainEpochDirectionAt_entails_chainEpochDirection A a gce.1.send gce.2.send)
    (chainEpochDirectionAt_entails_chainEpochDirection A (a + 56#64) gce.1.recv gce.2.recv)

theorem arrayAt_chainEpochAt_entails_chainEpoch (A : RustAlloc) :
    ∀ (ptr : BitVec 64) (gxs : List (ChainEpochGhost × ChainEpoch)),
      arrayAt (chainEpochAt A) 112 ptr gxs ⊢
        arrayAt (fun ce a => chainEpoch A ce a) 112 ptr (gxs.map Prod.snd)
  | _, [] => Entails.refl _
  | ptr, gce :: gxs =>
    sepConj_mono (chainEpochAt_entails_chainEpoch A gce ptr)
      (arrayAt_chainEpochAt_entails_chainEpoch A (ptr + 112#64) gxs)

theorem chainEpochDirection_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (ced : ChainEpochDirection) :
    chainEpochDirection A a ced ⊢
      ∃∗ g : ChainEpochDirectionGhost,
        (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.prev.ptr) ∗ memRegion (a + 40#64) 16 ∗
        vecCapPtrDealloc A g.next.cap g.next.ptr ∗
        vecCapPtrDealloc A g.prev.cap g.prev.ptr := by
  unfold chainEpochDirection keyHistory vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro nCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro nPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pPtr
  refine Entails.sepExists_right ⟨⟨nCap, nPtr⟩, ⟨pCap, pPtr⟩⟩ ?_
  exact chainEpochDirectionAt_entails_dealloc A a ⟨⟨nCap, nPtr⟩, ⟨pCap, pPtr⟩⟩ ced

theorem chainEpoch_entails_dealloc (A : RustAlloc) (cur : BitVec 64) (ce : ChainEpoch) :
    chainEpoch A ce cur ⊢
      ∃∗ g : ChainEpochGhost,
        chainEpochHeadersAt cur g ∗
        vecCapPtrDealloc A g.send.next.cap g.send.next.ptr ∗
        vecCapPtrDealloc A g.send.prev.cap g.send.prev.ptr ∗
        vecCapPtrDealloc A g.recv.next.cap g.recv.next.ptr ∗
        vecCapPtrDealloc A g.recv.prev.cap g.recv.prev.ptr := by
  unfold chainEpoch
  refine Entails.trans (sepConj_mono (chainEpochDirection_entails_dealloc A cur ce.send)
    (chainEpochDirection_entails_dealloc A (cur + 56#64) ce.recv)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro gs
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro gr
  refine Entails.sepExists_right ⟨gs, gr⟩ ?_
  unfold chainEpochHeadersAt
  dsimp only
  have hb1 : (cur + 56#64) + 8#64 = cur + 64#64 := by bv_omega
  have hb2 : (cur + 56#64) + 16#64 = cur + 72#64 := by bv_omega
  have hb3 : (cur + 56#64) + 24#64 = cur + 80#64 := by bv_omega
  have hb4 : (cur + 56#64) + 32#64 = cur + 88#64 := by bv_omega
  have hb5 : (cur + 56#64) + 40#64 = cur + 96#64 := by bv_omega
  rw [hb1, hb2, hb3, hb4, hb5]
  exact Entails.of_eq (by ac_rfl)

theorem vecDequeSlotsAt_nil_entails_memRegion {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat) (ptr : BitVec 64)
    (hbound : cap * stride < 2 ^ 63) :
    vecDequeSlotsAt elem stride cap head ptr [] 0 cap ⊢ memRegion ptr (cap * stride) := by
  have h := vecDequeSlotsAt_unoccupied_entails_memRegion elem stride cap head ptr [] cap 0
    (by rw [Nat.zero_add]; omega) (fun _ _ => by simp)
  simpa using h

theorem vecDequeSlotsAt_nonwrap_entails {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α)
    (hcap_lt : cap * stride < 2 ^ 63)
    (hhead_lt : head < cap)
    (hlen_le : xs.length ≤ cap - head) :
    ∃ ys : List α, ys.length = xs.length ∧
      (vecDequeSlotsAt elem stride cap head ptr xs 0 cap ⊢
        arrayAt elem stride (ptr + BitVec.ofNat 64 (head * stride)) ys ∗
        memRegion ptr (head * stride) ∗
        memRegion (ptr + BitVec.ofNat 64 ((head + xs.length) * stride)) ((cap - head - xs.length) * stride)) := by
  have hsplit1 : cap = head + (xs.length + (cap - head - xs.length)) := by omega
  have hocc : ∀ k < xs.length, vecDequeLogIdx head cap (head + k) < xs.length := by
    intro k hk
    unfold vecDequeLogIdx
    have hle : head ≤ head + k := by omega
    simp only [hle, ↓reduceIte]
    omega
  obtain ⟨ys, hys_len, hys_ent⟩ :=
    vecDequeSlotsAt_occupied_entails_arrayAt elem stride cap head ptr xs xs.length head hocc
  refine ⟨ys, hys_len, ?_⟩
  have hunocc1 : ∀ k < head, ¬(vecDequeLogIdx head cap (0 + k) < xs.length) := by
    intro k hk
    unfold vecDequeLogIdx
    have hnle : ¬(head ≤ 0 + k) := by omega
    simp only [hnle, ↓reduceIte]
    omega
  have hunocc2 : ∀ k < cap - head - xs.length,
      ¬(vecDequeLogIdx head cap ((head + xs.length) + k) < xs.length) := by
    intro k hk
    unfold vecDequeLogIdx
    have hle : head ≤ (head + xs.length) + k := by omega
    simp only [hle, ↓reduceIte]
    omega
  have hbound1 : (0 + head) * stride ≤ 2 ^ 64 := by
    rw [Nat.zero_add]
    have : head * stride ≤ cap * stride := Nat.mul_le_mul_right stride (by omega)
    omega
  have hbound3 : (head + xs.length + (cap - head - xs.length)) * stride ≤ 2 ^ 64 := by
    have heq : head + xs.length + (cap - head - xs.length) = cap := by omega
    rw [heq]
    omega
  have h1 := vecDequeSlotsAt_unoccupied_entails_memRegion elem stride cap head ptr xs head 0
    hbound1 hunocc1
  have h3 := vecDequeSlotsAt_unoccupied_entails_memRegion elem stride cap head ptr xs
    (cap - head - xs.length) (head + xs.length) hbound3 hunocc2
  simp only [Nat.zero_mul, BitVec.add_zero] at h1
  conv_lhs => arg 8; rw [hsplit1]
  rw [vecDequeSlotsAt_add elem stride cap head ptr xs 0 head (xs.length + (cap - head - xs.length)),
      Nat.zero_add,
      vecDequeSlotsAt_add elem stride cap head ptr xs head xs.length (cap - head - xs.length)]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono hys_ent h3)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecDequeSlotsAt_nonwrap_rejoin (stride cap head len : Nat) (ptr : BitVec 64)
    (hcap_lt : cap * stride < 2 ^ 63) (hhead_lt : head < cap) (hlen_le : len ≤ cap - head) :
    memRegion (ptr + BitVec.ofNat 64 (head * stride)) (len * stride) ∗
      memRegion ptr (head * stride) ∗
      memRegion (ptr + BitVec.ofNat 64 ((head + len) * stride)) ((cap - head - len) * stride) ⊢
    memRegion ptr (cap * stride) := by
  have h1 : cap * stride = head * stride + (len * stride + (cap - head - len) * stride) := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    congr 1
    omega
  have hbound1 : head * stride + (len * stride + (cap - head - len) * stride) ≤ 2 ^ 64 := by omega
  have hbound2 : len * stride + (cap - head - len) * stride ≤ 2 ^ 64 := by omega
  have haddr : ptr + BitVec.ofNat 64 (head * stride) + BitVec.ofNat 64 (len * stride) =
      ptr + BitVec.ofNat 64 ((head + len) * stride) := by
    rw [Nat.add_mul, BitVec.ofNat_add, ← BitVec.add_assoc]
  rw [h1,
      ProofLib.memRegion_split ptr (head * stride) (len * stride + (cap - head - len) * stride) hbound1,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (head * stride)) (len * stride) ((cap - head - len) * stride) hbound2,
      haddr]
  exact Entails.of_eq (by ac_rfl)

theorem vecDequeSlotsAt_wrap_entails {α : Type}
    (elem : α → BitVec 64 → SepProp) (stride cap head : Nat)
    (ptr : BitVec 64) (xs : List α)
    (hcap_lt : cap * stride < 2 ^ 63)
    (hhead_lt : head < cap)
    (hlen_le : xs.length ≤ cap)
    (hlen_gt : cap - head < xs.length) :
    ∃ ys₁ ys₂ : List α,
      ys₁.length = cap - head ∧
      ys₂.length = xs.length - (cap - head) ∧
      (vecDequeSlotsAt elem stride cap head ptr xs 0 cap ⊢
        arrayAt elem stride (ptr + BitVec.ofNat 64 (head * stride)) ys₁ ∗
        arrayAt elem stride ptr ys₂ ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length - (cap - head)) * stride))
          ((head - (xs.length - (cap - head))) * stride)) := by
  let m₂ := xs.length - (cap - head)
  have hm2_le : m₂ ≤ head := by omega
  have hsplit : cap = m₂ + ((head - m₂) + (cap - head)) := by omega
  have hocc1 : ∀ k < cap - head, vecDequeLogIdx head cap (head + k) < xs.length := by
    intro k hk
    unfold vecDequeLogIdx
    have hle : head ≤ head + k := by omega
    simp only [hle, ↓reduceIte]
    omega
  have hocc2 : ∀ k < m₂, vecDequeLogIdx head cap (0 + k) < xs.length := by
    intro k hk
    unfold vecDequeLogIdx
    have hnle : ¬(head ≤ 0 + k) := by omega
    simp only [hnle, ↓reduceIte]
    omega
  have hunocc : ∀ k < head - m₂, ¬(vecDequeLogIdx head cap (m₂ + k) < xs.length) := by
    intro k hk
    unfold vecDequeLogIdx
    have hnle : ¬(head ≤ m₂ + k) := by omega
    simp only [hnle, ↓reduceIte]
    omega
  obtain ⟨ys₁, hlen₁, hent₁⟩ :=
    vecDequeSlotsAt_occupied_entails_arrayAt elem stride cap head ptr xs (cap - head) head hocc1
  obtain ⟨ys₂, hlen₂, hent₂⟩ :=
    vecDequeSlotsAt_occupied_entails_arrayAt elem stride cap head ptr xs m₂ 0 hocc2
  simp only [Nat.zero_mul, BitVec.add_zero] at hent₂
  have hbound_mid : (m₂ + (head - m₂)) * stride ≤ 2 ^ 64 := by
    have : (m₂ + (head - m₂)) * stride ≤ cap * stride := Nat.mul_le_mul_right stride (by omega)
    omega
  have hmid := vecDequeSlotsAt_unoccupied_entails_memRegion elem stride cap head ptr xs
    (head - m₂) m₂ hbound_mid hunocc
  refine ⟨ys₁, ys₂, hlen₁, hlen₂, ?_⟩
  conv_lhs => arg 8; rw [hsplit]
  rw [vecDequeSlotsAt_add elem stride cap head ptr xs 0 m₂ ((head - m₂) + (cap - head)),
      Nat.zero_add,
      vecDequeSlotsAt_add elem stride cap head ptr xs m₂ (head - m₂) (cap - head),
      show m₂ + (head - m₂) = head by omega]
  refine Entails.trans (sepConj_mono hent₂ (sepConj_mono hmid hent₁)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecDequeSlotsAt_wrap_rejoin (stride cap head len : Nat) (ptr : BitVec 64)
    (hcap_lt : cap * stride < 2 ^ 63) (hhead_lt : head < cap)
    (hlen_le : len ≤ cap) (hlen_gt : cap - head < len) :
    memRegion (ptr + BitVec.ofNat 64 (head * stride)) ((cap - head) * stride) ∗
      memRegion ptr ((len - (cap - head)) * stride) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len - (cap - head)) * stride))
        ((head - (len - (cap - head))) * stride) ⊢
    memRegion ptr (cap * stride) := by
  let m₂ := len - (cap - head)
  have h1 : cap * stride = m₂ * stride + ((head - m₂) * stride + (cap - head) * stride) := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    congr 1
    omega
  have hbound1 : m₂ * stride + ((head - m₂) * stride + (cap - head) * stride) ≤ 2 ^ 64 := by omega
  have hbound2 : (head - m₂) * stride + (cap - head) * stride ≤ 2 ^ 64 := by omega
  have haddr : ptr + BitVec.ofNat 64 (m₂ * stride) + BitVec.ofNat 64 ((head - m₂) * stride) =
      ptr + BitVec.ofNat 64 (head * stride) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_mul, show m₂ + (head - m₂) = head by omega]
  rw [h1,
      ProofLib.memRegion_split ptr (m₂ * stride) ((head - m₂) * stride + (cap - head) * stride) hbound1,
      ProofLib.memRegion_split (ptr + BitVec.ofNat 64 (m₂ * stride)) ((head - m₂) * stride) ((cap - head) * stride) hbound2,
      haddr]
  exact Entails.of_eq (by ac_rfl)

theorem vecDequeHeader_entails_memRegion_32 (v cap ptr head len : BitVec 64) :
    vecDequeHeader v cap ptr head len ⊢ memRegion v 32 := by
  unfold vecDequeHeader
  rw [ProofLib.memRegion_split' (b := v) (n := 8) (k := 24) (b' := v + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := v + 8#64) (n := 8) (k := 16) (b' := v + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := v + 16#64) (n := 8) (k := 8) (b' := v + 24#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

theorem chainTail_entails_memRegion_32 (a : BitVec 64) (c : Chain) :
    ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗
      memRegion (a + 84#64) 4 ⊢
    memRegion (a + 56#64) 32 := by
  unfold chainParamsAt directionAt
  have hp : (a + 72#64) + 4#64 = a + 76#64 := by bv_omega
  rw [hp, sepConj_assoc ((a + 72#64) ↦₃₂ c.params.maxJump),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 24) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 16) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 4) (k := 12) (b' := a + 76#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 76#64) (n := 4) (k := 8) (b' := a + 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 80#64) (n := 4) (k := 4) (b' := a + 84#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo32_entails_memRegion _ _)))))

theorem chainAt_entails_dealloc (A : RustAlloc) (a : BitVec 64) (G : ChainProofs.ChainGhost) (c : Chain) :
    ChainProofs.chainAt A a G c ⊢
      vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
        a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
      ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      memRegion (a + 48#64) 40 ∗
      vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr := by
  unfold ChainProofs.chainAt
  apply Entails.pure_left; intro _
  have hnr := vecU8At_entails_capPtr_dealloc A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot
  have ha1 : (a + 32#64) + 8#64 = a + 40#64 := by bv_omega
  have ha2 : (a + 32#64) + 16#64 = a + 48#64 := by bv_omega
  rw [ha1, ha2] at hnr
  have htl := chainTail_entails_memRegion_32 a c
  have hgroup :
      (vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
        a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
        vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
        ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
        chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗
        memRegion (a + 84#64) 4) =
      (vecDequeAt A chainEpochSize chainEpochAlign (chainEpochAt A)
        a G.linksCap G.linksPtr G.linksHead (G.epochs.zip c.links) ∗
        vecU8At A (a + 32#64) G.nextRoot.cap G.nextRoot.ptr c.nextRoot ∗
        (((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
         chainParamsAt (a + 72#64) c.params ∗ directionAt (a + 80#64) c.dir ∗
         memRegion (a + 84#64) 4)) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono hnr htl)) ?_
  have h40 : memRegion (a + 48#64) 8 ∗ memRegion (a + 56#64) 32 = memRegion (a + 48#64) 40 := by
    rw [← ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 32)
          (b' := a + 56#64) rfl (by bv_omega) (by decide)]
  rw [← h40]
  exact Entails.of_eq (by ac_rfl)

theorem chainHeaders_entails_memRegion_88 (a cap ptr head len nrCap nrPtr : BitVec 64) :
    vecDequeHeader a cap ptr head len ∗
      ((a + 32#64) ↦₆₄ nrCap) ∗ ((a + 40#64) ↦₆₄ nrPtr) ∗ memRegion (a + 48#64) 40 ⊢
    memRegion a 88 := by
  have h1 := vecDequeHeader_entails_memRegion_32 a cap ptr head len
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 56) (b' := a + 32#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 48) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 40) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

end CryptoVerification.SpqrV1.Drop
