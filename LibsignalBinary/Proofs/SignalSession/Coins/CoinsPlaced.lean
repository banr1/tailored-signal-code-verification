/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsCodeSym
public import ProofLib.SepLogic.WP.Apply
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Proof of `signal_session_coins_fill`

Defines relocatable coins-tape predicates (`coinsAtPlaced`, `coinsAfterPlaced`) and proves
`coinsFillPlaced_ok` and `coinsFillPlaced_ok_cl` for block `618` (`signal_session_coins_fill`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Coins

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Coins.Placed

/-! ## 1. Relocatable Coins Statics & Tape Predicates -/

abbrev coinsNextSym : String := "libsignal_cli::coins::NEXT.0"
abbrev coinsLeftSym : String := "libsignal_cli::coins::LEFT.0"

/-- `signal_session::coins::NEXT` (the cursor, `.data`) under `[LibsignalPlacement]`. -/
abbrev coinsNextPlaced [LibsignalPlacement] : BitVec 64 := lsρ coinsNextSym

/-- `signal_session::coins::LEFT` (the remaining count, `.bss`) under `[LibsignalPlacement]`. -/
abbrev coinsLeftPlaced [LibsignalPlacement] : BitVec 64 := lsρ coinsLeftSym

/-- The coins tape under `[LibsignalPlacement]`. -/
abbrev coinsAtPlaced [LibsignalPlacement] (cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  tapeAt2 coinsNextPlaced coinsLeftPlaced cur rest

/-- The coins tape after `k` draws under `[LibsignalPlacement]`. -/
abbrev coinsAfterPlaced [LibsignalPlacement] (cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) :
    SepProp :=
  tapeAfter2 coinsNextPlaced coinsLeftPlaced cur rest k

/-! ## 2. Relocatable Callee Specifications -/

/-- Spec of `signal_session_coins_fill` (Block `618`) from `coinsAfterPlaced cur rest 0`:
fill `dst[0, len)` with the next `min len rest.length` tape bytes, then zeros; advance the tape.
`stk` free stack bytes below entry `sp` (`0x50 ≤ stk`) are lent and returned. -/
def coinsFillSpecPlaced [LibsignalPlacement] (stk : Nat) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, len, cur, rest) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ coinsAfterPlaced cur rest 0 ∗ stackAt s.sp stk
  post := fun (dst, len, cur, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      coinsAfterPlaced cur rest (min len rest.length) ∗ stackAt s0.sp stk

/-- `coinsFillSpecPlaced` with the tape ghost `(cur, rest)` fixed (ghost: `(dst, len)`). -/
def coinsFillAtSpecPlaced [LibsignalPlacement] (stk : Nat) (cur : BitVec 64)
    (rest : List (BitVec 8)) : Spec (BitVec 64 × Nat) where
  pre := fun (dst, len) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len ∗ coinsAfterPlaced cur rest 0 ∗ stackAt s.sp stk
  post := fun (dst, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      coinsAfterPlaced cur rest (min len rest.length) ∗ stackAt s0.sp stk

theorem coinsFillAtPlaced_of_after0 [LibsignalPlacement] {P : Program} {addr cur : BitVec 64}
    {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (coinsFillSpecPlaced stk)) :
    subroutine_ok P addr (coinsFillAtSpecPlaced stk cur rest) := by
  intro ⟨dst, len⟩ R s0 hpc hrun hpre hsp
  exact h (dst, len, cur, rest) R s0 hpc hrun hpre hsp

theorem coinsFillAtPlaced_of_after0_cl [LibsignalPlacement] {P : Program} {addr cur : BitVec 64}
    {stk : Nat} {rest : List (BitVec 8)}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (coinsFillSpecPlaced stk))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (coinsFillAtSpecPlaced stk cur rest)) := by
  intro ⟨dst, len⟩ R s0 hpc hrun hpre hsp
  exact h (dst, len, cur, rest) R s0 hpc hrun hpre hsp

/-! ## 3. Private Byte & Stack Lemmas -/

private theorem csel_min_eq_placed (rem len : Nat) (x1 : BitVec 64)
    (hrem : rem < 2 ^ 64) (hx1 : x1.toNat = len) :
    (if (BitVec.ofNat 64 rem).ult x1 = true then BitVec.ofNat 64 rem else x1) =
      BitVec.ofNat 64 (min len rem) := by
  have hx1_bv : x1 = BitVec.ofNat 64 len := by rw [← hx1]; simp
  split
  · rename_i hult
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, hx1, decide_eq_true_eq] at hult
    have hmin : min len rem = rem := by omega
    rw [hmin]
  · rename_i hult
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, hx1, decide_eq_true_eq] at hult
    have hmin : min len rem = len := by omega
    rw [hmin, hx1_bv]

private theorem bv_sub_of_le_placed {a k : Nat} (hk : k ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  have ha : a = (a - k) + k := (Nat.sub_add_cancel hk).symm
  conv_lhs => rw [ha, BitVec.ofNat_add]
  bv_arith

private theorem reg_sub_of_le_placed {x1 : BitVec 64} {len k : Nat}
    (hx1 : x1.toNat = len) (hk : k ≤ len) :
    x1 - BitVec.ofNat 64 k = BitVec.ofNat 64 (len - k) := by
  have hx1_bv : x1 = BitVec.ofNat 64 len := by rw [← hx1]; simp
  rw [hx1_bv]
  exact bv_sub_of_le_placed hk

private theorem fill_bytes_eq_placed (rest : List (BitVec 8)) (len : Nat) :
    rest.take (min len rest.length) ++ List.replicate (len - min len rest.length) 0#8 =
      (rest ++ List.replicate len 0#8).take len := by
  rw [List.take_append]
  by_cases hle : len ≤ rest.length
  · have hmin : min len rest.length = len := Nat.min_eq_left hle
    have hsub1 : len - min len rest.length = 0 := by omega
    have hsub2 : len - rest.length = 0 := by omega
    rw [hsub1, hmin, hsub2]
    simp
  · have hge : rest.length ≤ len := by omega
    have hmin : min len rest.length = rest.length := Nat.min_eq_right hge
    have hmin2 : min (len - rest.length) len = len - rest.length := by omega
    rw [hmin, List.take_length, List.take_of_length_le hge, List.take_replicate, hmin2]

private theorem dst_bytes_merge_placed (dst : BitVec 64) (len : Nat) (rest : List (BitVec 8)) :
    (dst ↦ₛ rest.take (min len rest.length)) ∗
      ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.replicate (len - min len rest.length) 0#8) =
    (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) := by
  have htake_len : (rest.take (min len rest.length)).length = min len rest.length :=
    List.length_take_of_le (Nat.min_le_right len rest.length)
  rw [← fill_bytes_eq_placed rest len, pointsToBytes_append, htake_len]

private theorem post_merge_placed (dst cur nx lf : BitVec 64) (len : Nat) (rest : List (BitVec 8)) :
    (dst ↦ₛ List.take (min len rest.length) rest) ∗
      ((dst + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.replicate (len - min len rest.length) 0#8) ∗
      (cur ↦ₛ List.take (min len rest.length) rest) ∗
      ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
        List.drop (min len rest.length) rest) ∗
      (nx ↦₆₄ (cur + BitVec.ofNat 64 (min len rest.length))) ∗
      (lf ↦₆₄ BitVec.ofNat 64 (rest.length - min len rest.length)) ⊢
    (dst ↦ₛ List.take len (rest ++ List.replicate len 0#8)) ∗
      tapeAfter2 nx lf cur rest (min len rest.length) := by
  apply Entails.of_eq
  have htake_len : (rest.take (min len rest.length)).length = min len rest.length :=
    List.length_take_of_le (Nat.min_le_right len rest.length)
  have hcur : (cur ↦ₛ rest) =
      (cur ↦ₛ List.take (min len rest.length) rest) ∗
        ((cur + BitVec.ofNat 64 (min len rest.length)) ↦ₛ
          List.drop (min len rest.length) rest) := by
    conv_lhs => rw [(List.take_append_drop (min len rest.length) rest).symm]
    rw [pointsToBytes_append, htake_len]
  unfold tapeAfter2
  rw [← dst_bytes_merge_placed dst len rest, hcur]
  sep_ac_rfl

private theorem stackAt_split_bottom_coins_placed (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

private theorem memRegion_80_words_placed (sp : BitVec 64) :
    memRegion (sp - 80#64) 80 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗
        ((sp - 56#64) ↦₆₄ u6) ∗ ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗
        ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗
        ((sp - 8#64) ↦₆₄ u0)) := by
  rw [memRegion_split (sp - 80#64) 8 72 (by decide),
    memRegion_split (sp - 80#64 + 8#64) 8 64 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64) 8 56 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 80#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  have h72 : sp - 80#64 + 8#64 = sp - 72#64 := by bv_arith
  have h64 : sp - 72#64 + 8#64 = sp - 64#64 := by bv_arith
  have h56 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_arith
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 48#64 + 8#64 = sp - 40#64 := by bv_arith
  have h32 : sp - 40#64 + 8#64 = sp - 32#64 := by bv_arith
  have h24 : sp - 32#64 + 8#64 = sp - 24#64 := by bv_arith
  have h16 : sp - 24#64 + 8#64 = sp - 16#64 := by bv_arith
  have h8 : sp - 16#64 + 8#64 = sp - 8#64 := by bv_arith
  simp only [h72, h64, h56, h48, h40, h32, h24, h16, h8,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_80_words_fold_placed (sp : BitVec 64)
    (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 : BitVec 64) :
    (((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 64#64) ↦₆₄ v7) ∗
      ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 40#64) ↦₆₄ v4) ∗
      ((sp - 32#64) ↦₆₄ v3) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 16#64) ↦₆₄ v1) ∗
      ((sp - 8#64) ↦₆₄ v0)) ⊢
    memRegion (sp - 80#64) 80 := by
  rw [memRegion_80_words_placed sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.refl _))))))))))

private theorem stackAt_coinsFill_split_placed (sp : BitVec 64) (stk : Nat)
    (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ∃∗ u8 : BitVec 64, ∃∗ u9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ u9) ∗ ((sp - 72#64) ↦₆₄ u8) ∗ ((sp - 64#64) ↦₆₄ u7) ∗
        ((sp - 56#64) ↦₆₄ u6) ∗ ((sp - 48#64) ↦₆₄ u5) ∗ ((sp - 40#64) ↦₆₄ u4) ∗
        ((sp - 32#64) ↦₆₄ u3) ∗ ((sp - 24#64) ↦₆₄ u2) ∗ ((sp - 16#64) ↦₆₄ u1) ∗
        ((sp - 8#64) ↦₆₄ u0)) := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_lhs => rw [heq]
  rw [stackAt_split_bottom_coins_placed sp 80 (stk - 80) (by omega), ← heq]
  simp only [stackAt, memRegion_80_words_placed]

private theorem stackAt_coinsFill_merge_placed (sp : BitVec 64) (stk : Nat)
    (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63)
    (v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 stk) (stk - 80) ∗
      (((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 64#64) ↦₆₄ v7) ∗
        ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 40#64) ↦₆₄ v4) ∗
        ((sp - 32#64) ↦₆₄ v3) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 16#64) ↦₆₄ v1) ∗
        ((sp - 8#64) ↦₆₄ v0)) ⊢
    stackAt sp stk := by
  have heq : stk = 80 + (stk - 80) := by omega
  conv_rhs => rw [heq]
  rw [stackAt_split_bottom_coins_placed sp 80 (stk - 80) (by omega), ← heq]
  simp only [stackAt]
  exact sepConj_mono_right (memRegion_80_words_fold_placed sp v9 v8 v7 v6 v5 v4 v3 v2 v1 v0)

/-! ## 4. Block `618` Proof (`coinsFillPlaced_ok`) -/

section CoinsFillProof

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem coinsFillPlaced_ok_of_mem [LibsignalPlacement]
    {H : LibsignalHooks}
    (hmemcpy : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H)
      (lsρ memcpyName) sessionMemcpyRegionSpec)
    (hmemset : subroutine_ok ((blkPC_618).rebase (blkPl_618).base H)
      (lsρ memsetName) sessionMemsetRegionSpec)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base
      (coinsFillSpecPlaced stk) := by
  simp only [coinsFillSpecPlaced, coinsAfterPlaced, tapeAfter2_zero_eq,
    coinsNextPlaced, coinsLeftPlaced, coinsNextSym, coinsLeftSym]
  wp_init x s0
  obtain ⟨dst, len, cur, rest⟩ := x
  dsimp only at *
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ cur) ∗
          ((cur ↦ₛ rest) ∗
            (memRegion dst len ∗
              (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ BitVec.ofNat 64 rest.length) ∗
              stackAt s0.sp stk ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpre
        sep_ac_rfl
      have hdisj := IsBlock.disjoint
        (IsBlock.pointsTo64 (lsρ "libsignal_cli::coins::NEXT.0") cur)
        (IsBlock.pointsToBytes cur rest) (by decide) hpos hmem_disj
      have h2 := hdisj.2
      have hlt : (lsρ "libsignal_cli::coins::NEXT.0" - cur).toNat < 2 ^ 64 :=
        (lsρ "libsignal_cli::coins::NEXT.0" - cur).isLt
      omega
    · omega
  set k := min len rest.length
  have hx1 : (s0.readReg64 (Reg.gpr 1#5)).toNat = len := by assumption
  have hlen_lt64 : len < 2 ^ 64 := hx1 ▸ (s0.readReg64 (Reg.gpr 1#5)).isLt
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hcsel :
      (if (BitVec.ofNat 64 rest.length).ult (s0.readReg64 (Reg.gpr 1#5)) = true then
        BitVec.ofNat 64 rest.length
      else s0.readReg64 (Reg.gpr 1#5)) = BitVec.ofNat 64 k :=
    csel_min_eq_placed rest.length len (s0.readReg64 (Reg.gpr 1#5)) hrest_lt64 hx1
  have hrem_sub : BitVec.ofNat 64 rest.length - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (rest.length - k) := bv_sub_of_le_placed hk_le_rest
  have hlen_sub : s0.readReg64 (Reg.gpr 1#5) - BitVec.ofNat 64 k =
      BitVec.ofNat 64 (len - k) := reg_sub_of_le_placed hx1 hk_le_len
  have hk_toNat : (BitVec.ofNat 64 k).toNat = (List.take k rest).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hk_le_len hlen_lt64), htake_len]
  have hrem_len_toNat : (BitVec.ofNat 64 (len - k)).toNat = len - k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len - k < 2 ^ 64)]
  have hlen_sub_le : len - k ≤ 2 ^ 64 := by omega
  have hdst_split : memRegion dst len =
      memRegion dst (rest.take k).length ∗ memRegion (dst + BitVec.ofNat 64 k) (len - k) := by
    have hlen_eq : len = k + (len - k) := by omega
    conv_lhs => rw [hlen_eq]
    rw [memRegion_split dst k (len - k) (by omega), htake_len]
  have hcur_split : (cur ↦ₛ rest) =
      (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
    conv_lhs => rw [(List.take_append_drop k rest).symm]
    rw [pointsToBytes_append, htake_len]
  wp_conv_pre =>
    rw [stackAt_coinsFill_split_placed s0.sp stk hstk hstk']
  wp_pull_exists
  wp_conv_pre =>
    rw [hdst_split, hcur_split]
    simp only [sepConj_assoc]
  wp_steps
  wp_call hmemcpy
  wp_steps
  wp_call hmemset
  wp_steps
  have htr2 := hpost_1.trans hpost
  apply SepWP.fold (stackAt_coinsFill_merge_placed s0.sp stk hstk hstk' _ _ _ _ _ _ _ _ _ _)
    (by sep_focus)
  apply SepWP.fold
    (post_merge_placed dst cur (lsρ "libsignal_cli::coins::NEXT.0")
      (lsρ "libsignal_cli::coins::LEFT.0") len rest)
    (by sep_focus)
  wp_done

/-- Block `618` (`signal_session_coins_fill`) meets `coinsFillSpecPlaced stk` under `[LibsignalPlacement]`. -/
theorem coinsFillPlaced_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H memcpyName sessionMemcpyRegionSpec)
    (hmemset : HookSat H memsetName sessionMemsetRegionSpec)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base
      (coinsFillSpecPlaced stk) :=
  coinsFillPlaced_ok_of_mem
    (ls_hook_ok_ultra_of_mem hmemcpy)
    (ls_hook_ok_ultra_of_mem hmemset)
    stk hstk hstk'

/-- `withLsCodeLoaded` corollary of `coinsFillPlaced_ok` for `lscall_blk_cl` callers. -/
theorem coinsFillPlaced_ok_cl [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H memcpyName sessionMemcpyRegionSpec)
    (hmemset : HookSat H memsetName sessionMemsetRegionSpec)
    (stk : Nat) (hstk : 0x50 ≤ stk) (hstk' : stk ≤ 2 ^ 63) :
    subroutine_ok ((blkPC_618).rebase (blkPl_618).base H) (blkPl_618).base
      (withLsCodeLoaded lsmpl (coinsFillSpecPlaced stk)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (coinsFillPlaced_ok hmemcpy hmemset stk hstk hstk')

end CoinsFillProof

end CryptoVerification.SignalSession.Coins
