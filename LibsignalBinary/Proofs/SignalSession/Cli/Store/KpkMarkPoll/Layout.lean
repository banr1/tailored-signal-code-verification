/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.KpkMark
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Specifications.AsmConstants

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

/-- Linter-safe state/register/PC/SP normalizer that never triggers `unusedSimpArgs` or `whnf` hangs. -/
macro "kpk_norm" : tactic =>
  `(tactic|
    ((try with_reducible rfl)
     (try simp +zetaDelta only [wp_norm])
     (try simp +zetaDelta only [arm64_norm])
     (try simp +zetaDelta only [*])
     try with_reducible rfl))

/-- Linter-safe separation-logic normalizer applying one lemma per step. -/
macro "kpk_sep_norm" : tactic =>
  `(tactic| repeat first
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepConj_assoc])

/-- Goal-closing separation-logic normalizer + `sep_focus`. -/
macro "kpk_sep_focus" : tactic =>
  `(tactic|
    ((repeat first
       | simp only [sepExists_sepConj_left]
       | simp only [sepExists_sepConj_right]
       | simp only [BitVec.add_assoc]
       | simp only [BitVec.reduceAdd]
       | simp only [sepConj_assoc])
     sep_focus))

/-- Maximum sub-callee stack budget needed below `mark_kyber_pre_key_used::{closure#0}`'s `0xf0` frame.
`doReserveStackX` (`112 + extHookStack`) already dominates `extHookStack`, `publicKeySerializeStackX`
(`32 + extHookStack`), and `cliConcatStack` (`96 + extHookStack`). -/
abbrev kpkSubMax (decStk getStk putStk : Nat) : Nat :=
  max (max decStk getStk) (max putStk doReserveStackX)

/-- Minimum stack budget of `mark_kyber_pre_key_used::{closure#0}` (`0xf0` frame + `kpkSubMax`). -/
abbrev kpkMinStk (decStk getStk putStk : Nat) : Nat :=
  0xf0 + kpkSubMax decStk getStk putStk

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {k m : Nat} (hle : k ≤ m) (hm : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  have heq : m = k + (m - k) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp k (m - k) (by omega), ← heq]

theorem subStack_split (sp : BitVec 64) {decStk getStk putStk K : Nat}
    (hK : K ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) :
    stackAt (sp - 0xf0#64) (kpkSubMax decStk getStk putStk) =
      memRegion (sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - K) ∗
      stackAt (sp - 0xf0#64) K :=
  stackAt_sub_split (sp - 0xf0#64) hK (by unfold kpkMinStk at hhi; omega)

theorem memRegion_two_16 (a : BitVec 64) :
    memRegion a 2 = (∃∗ u : BitVec 16, a ↦₁₆ u) := by
  apply sepProp_ext
  · rw [show (2 : Nat) = 1 + 1 by rfl,
        memRegion_split a 1 1 (by decide),
        memRegion_one, memRegion_one]
    kpk_sep_norm
    refine Entails.sepExists_elim fun b0 => Entails.sepExists_elim fun b1 => ?_
    let u : BitVec 16 := b0.setWidth 16 ||| (b1.setWidth 16 <<< 8)
    have hu : unpack16 u = [b0, b1] := by
      have e0 : u.extractLsb' 0 8 = b0 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      have e1 : u.extractLsb' 8 8 = b1 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      simp [unpack16, e0, e1]
    refine Entails.sepExists_right u ?_
    rw [pointsTo16_eq_pointsToBytes, hu]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun u => ?_
    rw [pointsTo16_eq_pointsToBytes]
    exact (unpack16_length u) ▸ pointsToBytes_entails_memRegion a (unpack16 u)

theorem memRegion_four_32 (a : BitVec 64) :
    memRegion a 4 = (∃∗ u : BitVec 32, a ↦₃₂ u) := by
  apply sepProp_ext
  · rw [show (4 : Nat) = 1 + (1 + (1 + 1)) by rfl,
        memRegion_split a 1 (1 + (1 + 1)) (by decide),
        memRegion_split (a + 1#64) 1 (1 + 1) (by decide),
        memRegion_split (a + 1#64 + 1#64) 1 1 (by decide),
        memRegion_one, memRegion_one, memRegion_one, memRegion_one]
    kpk_sep_norm
    refine Entails.sepExists_elim fun b0 => Entails.sepExists_elim fun b1 =>
      Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun b3 => ?_
    let u : BitVec 32 :=
      b0.setWidth 32 ||| (b1.setWidth 32 <<< 8) |||
        (b2.setWidth 32 <<< 16) ||| (b3.setWidth 32 <<< 24)
    have hu : unpack32 u = [b0, b1, b2, b3] := by
      have e0 : u.extractLsb' 0 8 = b0 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      have e1 : u.extractLsb' 8 8 = b1 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      have e2 : u.extractLsb' 16 8 = b2 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      have e3 : u.extractLsb' 24 8 = b3 := by
        ext i hi
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
        all_goals simp [u]
      simp [unpack32, e0, e1, e2, e3]
    refine Entails.sepExists_right u ?_
    rw [pointsTo32_eq_pointsToBytes, hu]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    kpk_sep_norm
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun u => ?_
    rw [pointsTo32_eq_pointsToBytes]
    exact (unpack32_length u) ▸ pointsToBytes_entails_memRegion a (unpack32 u)

/-! ## Unaligned `1 + 4 + 2 + 1 = 8` Word Split (`word1421At`) -/

/-- Exact 4-atom decomposition of an 8-byte word matching `ldrb [a]`, `ldur w [a+1]`,
`ldurh [a+5]`, `ldrb [a+7]` and the epilogue stores `strb [a]`, `stur w [a+1]`,
`sturh [a+5]`, `strb [a+7]`. -/
def word1421At (a : BitVec 64) (b0 : BitVec 8) (b14 : BitVec 32)
    (b56 : BitVec 16) (b7 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ b14) ∗ ((a + 5#64) ↦₁₆ b56) ∗ ((a + 7#64) ↦₈ b7)

private theorem unpack64_eq_1421 (w : BitVec 64) :
    unpack64 w =
      [w.extractLsb' 0 8] ++ unpack32 (w.extractLsb' 8 32) ++
        unpack16 (w.extractLsb' 40 16) ++ [w.extractLsb' 56 8] := by
  have hb1 : (w.extractLsb' 8 32).extractLsb' 0 8 = w.extractLsb' 8 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  have hb2 : (w.extractLsb' 8 32).extractLsb' 8 8 = w.extractLsb' 16 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  have hb3 : (w.extractLsb' 8 32).extractLsb' 16 8 = w.extractLsb' 24 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  have hb4 : (w.extractLsb' 8 32).extractLsb' 24 8 = w.extractLsb' 32 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  have hb5 : (w.extractLsb' 40 16).extractLsb' 0 8 = w.extractLsb' 40 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  have hb6 : (w.extractLsb' 40 16).extractLsb' 8 8 = w.extractLsb' 48 8 := by
    ext i hi; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try omega
    all_goals simp
  simp only [unpack64, unpack32, unpack16, hb1, hb2, hb3, hb4, hb5, hb6,
    List.cons_append, List.nil_append]

theorem pointsTo64_eq_word1421At (a w : BitVec 64) :
    (a ↦₆₄ w) =
      word1421At a (w.extractLsb' 0 8) (w.extractLsb' 8 32)
        (w.extractLsb' 40 16) (w.extractLsb' 56 8) := by
  unfold word1421At
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo16_eq_pointsToBytes,
      unpack64_eq_1421 w]
  have h1 : ([w.extractLsb' 0 8]).length = 1 := rfl
  have h4 : (unpack32 (w.extractLsb' 8 32)).length = 4 := unpack32_length _
  have h2 : (unpack16 (w.extractLsb' 40 16)).length = 2 := unpack16_length _
  simp only [List.append_assoc, pointsToBytes_append, h1, h4, h2]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  kpk_sep_norm

theorem word1421At_entails_memRegion8 (a : BitVec 64)
    (b0 : BitVec 8) (b14 : BitVec 32) (b56 : BitVec 16) (b7 : BitVec 8) :
    word1421At a b0 b14 b56 b7 ⊢ memRegion a 8 := by
  unfold word1421At
  rw [pointsTo32_eq_pointsToBytes, pointsTo16_eq_pointsToBytes]
  have h0 : (a ↦₈ b0) ⊢ memRegion a 1 := by
    have : (a ↦₈ b0) = (a ↦ₛ [b0]) := by simp [pointsToBytes_cons, pointsToBytes_nil]
    rw [this]; exact pointsToBytes_entails_memRegion a [b0]
  have h7 : ((a + 7#64) ↦₈ b7) ⊢ memRegion (a + 7#64) 1 := by
    have : ((a + 7#64) ↦₈ b7) = ((a + 7#64) ↦ₛ [b7]) := by
      simp [pointsToBytes_cons, pointsToBytes_nil]
    rw [this]; exact pointsToBytes_entails_memRegion (a + 7#64) [b7]
  have h4 : ((a + 1#64) ↦ₛ unpack32 b14) ⊢ memRegion (a + 1#64) 4 :=
    (unpack32_length b14) ▸ pointsToBytes_entails_memRegion _ _
  have h2 : ((a + 5#64) ↦ₛ unpack16 b56) ⊢ memRegion (a + 5#64) 2 :=
    (unpack16_length b56) ▸ pointsToBytes_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h4 (sepConj_mono h2 h7))) ?_
  rw [← ProofLib.memRegion_split' (b := a + 5#64) (n := 2) (k := 1)
        (b' := a + 7#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := a + 1#64) (n := 4) (k := 3)
        (b' := a + 5#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := a) (n := 1) (k := 7)
        (b' := a + 1#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem memRegion_8_eq_word1421At (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ b0 : BitVec 8, ∃∗ b14 : BitVec 32, ∃∗ b56 : BitVec 16, ∃∗ b7 : BitVec 8,
        word1421At a b0 b14 b56 b7) := by
  apply sepProp_ext
  · rw [ProofLib.memRegion_eight]
    refine Entails.sepExists_elim fun w => ?_
    rw [pointsTo64_eq_word1421At a w]
    exact Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))))
  · refine Entails.sepExists_elim fun b0 => Entails.sepExists_elim fun b14 =>
      Entails.sepExists_elim fun b56 => Entails.sepExists_elim fun b7 =>
        word1421At_entails_memRegion8 a b0 b14 b56 b7

/-! ## `0xf0` Stack Frame & `48`-Byte `sret` Decomposition -/

/-- Exact 240-byte (`0xf0`) stack-frame decomposition of `mark_kyber_pre_key_used::{closure#0}`. -/
def kpkFrameSlots (sp : BitVec 64) (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) : SepProp :=
  memRegion (sp - 0xf0#64) 8 ∗
  ((sp - 0xe8#64) ↦₆₄ f0) ∗ ((sp - 0xe0#64) ↦₆₄ f1) ∗
  ((sp - 0xd8#64) ↦₆₄ f2) ∗ ((sp - 0xd0#64) ↦₆₄ f3) ∗
  memRegion (sp - 0xc8#64) 24 ∗
  memRegion (sp - 0xb0#64) 48 ∗
  memRegion (sp - 0x80#64) 24 ∗
  memRegion (sp - 0x68#64) 4 ∗
  ((sp - 0x64#64) ↦₃₂ tmp32) ∗
  ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗
  ((sp - 0x50#64) ↦₆₄ c2) ∗ ((sp - 0x48#64) ↦₆₄ c3) ∗
  ((sp - 0x40#64) ↦₆₄ c4) ∗ ((sp - 0x38#64) ↦₆₄ c5) ∗
  ((sp - 0x30#64) ↦₆₄ c6) ∗ ((sp - 0x28#64) ↦₆₄ c7) ∗
  ((sp - 0x20#64) ↦₆₄ c8) ∗ ((sp - 0x18#64) ↦₆₄ c9) ∗
  ((sp - 0x10#64) ↦₆₄ c10) ∗ ((sp - 0x08#64) ↦₆₄ c11)

theorem stackAt_kpkMark_eq (sp : BitVec 64) {sub : Nat} (hsub : 0xf0 + sub ≤ 2 ^ 64) :
    stackAt sp (0xf0 + sub) =
      stackAt (sp - 0xf0#64) sub ∗
      (∃∗ f0 : BitVec 64, ∃∗ f1 : BitVec 64, ∃∗ f2 : BitVec 64, ∃∗ f3 : BitVec 64,
       ∃∗ tmp32 : BitVec 32,
       ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        kpkFrameSlots sp f0 f1 f2 f3 tmp32 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) := by
  have htop : stackAt sp (sub + 240) = stackAt (sp - 0xf0#64) sub ∗ memRegion (sp - 0xf0#64) 240 := by
    simp only [stackAt]
    have hbv : sp - BitVec.ofNat 64 (sub + 240) = sp - 0xf0#64 - BitVec.ofNat 64 sub := by bv_omega
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (sub + 240))
          (n := sub) (k := 240) (b' := sp - 0xf0#64)
          (by omega) (by bv_omega) (by omega), hbv]
  have hm32 : memRegion (sp - 0xe8#64) 32 = cells (sp - 0xe8#64) 4 :=
    ProofLib.memRegion_cells (sp - 0xe8#64) 4 (by decide)
  have hm96 : memRegion (sp - 0x60#64) 96 = cells (sp - 0x60#64) 12 :=
    ProofLib.memRegion_cells (sp - 0x60#64) 12 (by decide)
  rw [show 0xf0 + sub = sub + 240 by omega, htop,
      ProofLib.memRegion_split' (b := sp - 0xf0#64) (n := 8) (k := 232)
        (b' := sp - 0xe8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xe8#64) (n := 32) (k := 200)
        (b' := sp - 0xc8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xc8#64) (n := 24) (k := 176)
        (b' := sp - 0xb0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 48) (k := 128)
        (b' := sp - 0x80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x80#64) (n := 24) (k := 104)
        (b' := sp - 0x68#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x68#64) (n := 4) (k := 100)
        (b' := sp - 0x64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x64#64) (n := 4) (k := 96)
        (b' := sp - 0x60#64) rfl (by bv_omega) (by decide),
      memRegion_four_32 (sp - 0x64#64), hm32, hm96]
  have hc4 : cells (sp - 0xe8#64) 4 =
      (∃∗ f0 : BitVec 64, ∃∗ f1 : BitVec 64, ∃∗ f2 : BitVec 64, ∃∗ f3 : BitVec 64,
        ((sp - 0xe8#64) ↦₆₄ f0) ∗ ((sp - 0xe0#64) ↦₆₄ f1) ∗
        ((sp - 0xd8#64) ↦₆₄ f2) ∗ ((sp - 0xd0#64) ↦₆₄ f3)) := by
    cells_unfold
  have hc12 : cells (sp - 0x60#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗
        ((sp - 0x50#64) ↦₆₄ c2) ∗ ((sp - 0x48#64) ↦₆₄ c3) ∗
        ((sp - 0x40#64) ↦₆₄ c4) ∗ ((sp - 0x38#64) ↦₆₄ c5) ∗
        ((sp - 0x30#64) ↦₆₄ c6) ∗ ((sp - 0x28#64) ↦₆₄ c7) ∗
        ((sp - 0x20#64) ↦₆₄ c8) ∗ ((sp - 0x18#64) ↦₆₄ c9) ∗
        ((sp - 0x10#64) ↦₆₄ c10) ∗ ((sp - 0x08#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hc4, hc12]
  unfold kpkFrameSlots
  kpk_sep_norm

theorem stackAt_kpkMark_of_parts (sp : BitVec 64) {sub : Nat} (hsub : 0xf0 + sub ≤ 2 ^ 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) :
    (stackAt (sp - 0xf0#64) sub ∗
      kpkFrameSlots sp f0 f1 f2 f3 tmp32 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) ⊢
      stackAt sp (0xf0 + sub) := by
  rw [stackAt_kpkMark_eq sp hsub]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right f0 (Entails.sepExists_right f1
    (Entails.sepExists_right f2 (Entails.sepExists_right f3
    (Entails.sepExists_right tmp32
    (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
    (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
    (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11
      (Entails.refl _)))))))))))))))))

def savedCalleeSlots (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

theorem restore_kpkMarkStack (s0 : State) {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32) :
    (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      savedCalleeSlots s0) ⊢
      stackAt s0.sp stk := by
  have hmin : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  rw [stackAt_sub_split s0.sp hstk hhi]
  refine sepConj_mono_right ?_
  refine Entails.trans ?_
    (stackAt_kpkMark_of_parts s0.sp hmin f0 f1 f2 f3 tmp32
      (s0.readReg64 .x29) (s0.readReg64 .lr) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19))
  rw [subStack_split s0.sp hext hmin]
  unfold kpkFrameSlots savedCalleeSlots
  exact Entails.of_eq (by ac_rfl)

theorem sret48_kpk_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
       ∃∗ ob0 : BitVec 8, ∃∗ ob14 : BitVec 32, ∃∗ ob56 : BitVec 16, ∃∗ ob7 : BitVec 8,
       ∃∗ o5 : BitVec 64,
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 0x10#64) ↦₆₄ o2) ∗
        ((out + 0x18#64) ↦₆₄ o3) ∗
        word1421At (out + 0x20#64) ob0 ob14 ob56 ob7 ∗
        ((out + 0x28#64) ↦₆₄ o5)) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40)
        (b' := out + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 32)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24)
        (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
        (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      memRegion_8_eq_word1421At (out + 0x20#64),
      ProofLib.memRegion_eight]
  kpk_sep_norm

def epiloguePre (s0 : State) (x : KpkMarkPollGhost) : SepProp :=
  memRegion x.out 48 ∗
  kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
  savedCalleeSlots s0

def epilogueOut (s0 : State) (x : KpkMarkPollGhost)
    (v21 v27 v25 v22 v28 v23 v26 : BitVec 64) : SepProp :=
  (x.out ↦₆₄ v21) ∗ ((x.out + 8#64) ↦₆₄ v27) ∗
  ((x.out + 0x10#64) ↦₆₄ v25) ∗ ((x.out + 0x18#64) ↦₆₄ v22) ∗
  word1421At (x.out + 0x20#64)
    (v28.setWidth 8) (v23.setWidth 32) ((v23 >>> 32).setWidth 16) ((v23 >>> 48).setWidth 8) ∗
  ((x.out + 0x28#64) ↦₆₄ v26) ∗
  kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
  savedCalleeSlots s0

/-! ## `Vec<u8>` Borrow/Drop & All 4 `kpkMarkOutAt` Reassemblers -/

def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0#64 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8_eq_bytes_tail (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8))
    (v8 v16 : BitVec 64) (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    vecU8 A v bs =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs) := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader vecU8Tail SpqrV1.ChainProofs.bytesAt
  simp only [Bool.false_eq_true, ite_false]
  refine ProofLib.sepExists_congr fun cap => ProofLib.sepExists_congr fun ptr => ?_
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : cap = 0#64
  · subst hc
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
    have hcomm :
        (((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ emp) =
        (⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))) := by
      rw [sepConj_emp]; ac_rfl
    rw [hcomm]
    apply sepProp_ext
    · apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs
      apply Entails.pure_right ⟨hlen, hlt, hptr⟩
      simp only [pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
    · apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs
      apply Entails.pure_right ⟨hlen, hlt, hptr⟩
      simp only [pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
  · simp only [hc, ite_false]
    ac_rfl

theorem vecU8_of_bytes_tail (A : RustAlloc) (v v8 v16 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16)
    (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      vecU8 A v bs := by
  rw [vecU8_eq_bytes_tail A v bs v8 v16 hv8 hv16]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

theorem vecU8_free_zero (A : RustAlloc) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length ≤ (0#64 : BitVec 64).toNat) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A 0#64 ptr bs) ⊢ emp := by
  have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst hbs
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, ite_false, ite_true,
    pointsToBytes_nil, emp_sepConj]
  exact Entails.refl _

theorem vecU8_free_ne (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, hc, ite_false]
  have hpull :
      ((ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
  have hmerge := (ProofLib.memRegion_split (b := ptr) bs.length (cap.toNat - bs.length) (by omega)).symm
  rw [hmerge, show bs.length + (cap.toNat - bs.length) = cap.toNat by omega]
  exact Entails.refl _

theorem vecU8_empty_of_zero_one_zero (A : RustAlloc) (v v8 v16 : BitVec 64)
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    ((v ↦₆₄ 0#64) ∗ (v8 ↦₆₄ 1#64) ∗ (v16 ↦₆₄ 0#64)) ⊢ vecU8 A v [] := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hpure : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by
    decide
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [List.length_nil, hzero, ite_true, sepConj_emp]
  have hcomm :
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) ∗
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64⌝ =
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ 1#64 ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by
    ac_rfl
  rw [hcomm]
  exact Entails.pure_right hpure (Entails.refl _)

theorem header3_entails_memRegion24 (v v8 v16 w0 w1 w2 : BitVec 64)
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    ((v ↦₆₄ w0) ∗ (v8 ↦₆₄ w1) ∗ (v16 ↦₆₄ w2)) ⊢ memRegion v 24 := by
  subst hv8; subst hv16
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion v w0)
      (sepConj_mono (pointsTo64_entails_memRegion (v + 8#64) w1)
        (pointsTo64_entails_memRegion (v + 16#64) w2))) ?_
  rw [show (v + 16#64 : BitVec 64) = (v + 8#64) + 8#64 by bv_omega,
      ← ProofLib.memRegion_split (v + 8#64) 8 8 (by decide),
      ← ProofLib.memRegion_split v 8 16 (by decide)]
  exact Entails.refl _

theorem header4_entails_memRegion32 (v v8 v16 v24 w0 w1 w2 w3 : BitVec 64)
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) (hv24 : v + 24#64 = v24) :
    ((v ↦₆₄ w0) ∗ (v8 ↦₆₄ w1) ∗ (v16 ↦₆₄ w2) ∗ (v24 ↦₆₄ w3)) ⊢ memRegion v 32 := by
  subst hv8; subst hv16; subst hv24
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion v w0)
      (sepConj_mono (pointsTo64_entails_memRegion (v + 8#64) w1)
        (sepConj_mono (pointsTo64_entails_memRegion (v + 16#64) w2)
          (pointsTo64_entails_memRegion (v + 24#64) w3)))) ?_
  rw [show (v + 24#64 : BitVec 64) = (v + 16#64) + 8#64 by bv_omega,
      ← ProofLib.memRegion_split (v + 16#64) 8 8 (by decide),
      show (v + 16#64 : BitVec 64) = (v + 8#64) + 8#64 by bv_omega,
      ← ProofLib.memRegion_split (v + 8#64) 8 16 (by decide),
      ← ProofLib.memRegion_split v 8 24 (by decide)]
  exact Entails.refl _

theorem speWord_one_add_two_ne_zero : (speWord 1 + 2#64 == 0#64) = false := by
  decide +kernel

theorem okTagVec_add_two_eq_zero : (okTagVec + 2#64 == 0#64) = true := by
  decide +kernel

def speReadHeap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr fnPtr : BitVec 64) : SepProp :=
  (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    if cap = 0#64 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
  (fnPtr ↦ᵣ utf8 "read")

theorem speAt_read_invalidState_eq_words (A : RustAlloc)
    (r r8 r10 r18 r20 r28 : BitVec 64)
    (hr8 : r + 8#64 = r8) (hr10 : r8 + 8#64 = r10) (hr18 : r8 + 16#64 = r18)
    (hr20 : r + 0x20#64 = r20) (hr28 : r20 + 8#64 = r28) :
    speAt A (utf8 "read") r .invalidState =
      (∃∗ bs : List (BitVec 8), ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ fnPtr : BitVec 64,
        (r ↦₆₄ speWord 1) ∗ (r8 ↦₆₄ cap) ∗ (r10 ↦₆₄ ptr) ∗
        (r18 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (r20 ↦₆₄ fnPtr) ∗ (r28 ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        speReadHeap A bs cap ptr fnPtr) := by
  subst hr8; subst hr10; subst hr18; subst hr20; subst hr28
  unfold speAt speReadHeap vecU8 vecU8At vecHeader strRefAt
  have e1 : r + asm64% spePayloadOff = r + 8#64 := by bv_omega
  have e4 : r + asm64% speInvalidStateFnOff = r + 0x20#64 := by bv_omega
  rw [e1, e4]
  kpk_sep_norm
  refine ProofLib.sepExists_congr fun bs => ProofLib.sepExists_congr fun cap =>
    ProofLib.sepExists_congr fun ptr => ProofLib.sepExists_congr fun fnPtr => ?_
  ac_rfl

theorem kpkMarkOutAt_ok_reassemble (A : RustAlloc) (out w1 w2 w3 w5 : BitVec 64)
    (b0 : BitVec 8) (b14 : BitVec 32) (b56 : BitVec 16) (b7 : BitVec 8) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗ ((out + 0x18#64) ↦₆₄ w3) ∗
      word1421At (out + 0x20#64) b0 b14 b56 b7 ∗ ((out + 0x28#64) ↦₆₄ w5)) ⊢
      kpkMarkOutAt A out .ok := by
  unfold kpkMarkOutAt
  refine sepConj_mono_right ?_
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (word1421At_entails_memRegion8 _ _ _ _ _)
            (pointsTo64_entails_memRegion _ _))))) ?_
  rw [← ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
        (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24)
        (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 32)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem word1421At_roundtrip_fnPtr (a fnPtr v28 v23 : BitVec 64)
    (hv28 : v28.setWidth 8 = fnPtr.extractLsb' 0 8)
    (hv23_lo : v23.setWidth 32 = fnPtr.extractLsb' 8 32)
    (hv23_mid : (v23 >>> 32).setWidth 16 = fnPtr.extractLsb' 40 16)
    (hv23_hi : (v23 >>> 48).setWidth 8 = fnPtr.extractLsb' 56 8) :
    word1421At a (v28.setWidth 8) (v23.setWidth 32)
      ((v23 >>> 32).setWidth 16) ((v23 >>> 48).setWidth 8) =
    (a ↦₆₄ fnPtr) := by
  rw [hv28, hv23_lo, hv23_mid, hv23_hi, ← pointsTo64_eq_word1421At a fnPtr]

theorem kpkMarkOutAt_readErr_reassemble (A : RustAlloc) (out : BitVec 64)
    (bs : List (BitVec 8)) (cap ptr fnPtr v28 v23 : BitVec 64)
    (hv28 : v28.setWidth 8 = fnPtr.extractLsb' 0 8)
    (hv23_lo : v23.setWidth 32 = fnPtr.extractLsb' 8 32)
    (hv23_mid : (v23 >>> 32).setWidth 16 = fnPtr.extractLsb' 40 16)
    (hv23_hi : (v23 >>> 48).setWidth 8 = fnPtr.extractLsb' 56 8) :
    ((out ↦₆₄ speWord 1) ∗ ((out + 8#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
      ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      word1421At (out + 0x20#64)
        (v28.setWidth 8) (v23.setWidth 32) ((v23 >>> 32).setWidth 16) ((v23 >>> 48).setWidth 8) ∗
      ((out + 0x28#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
      speReadHeap A bs cap ptr fnPtr) ⊢
      kpkMarkOutAt A out .readErr := by
  rw [word1421At_roundtrip_fnPtr (out + 0x20#64) fnPtr v28 v23 hv28 hv23_lo hv23_mid hv23_hi]
  show _ ⊢ speAt A (utf8 "read") out .invalidState
  rw [speAt_read_invalidState_eq_words A out (out + 8#64) (out + 0x10#64) (out + 0x18#64)
        (out + 0x20#64) (out + 0x28#64) rfl (by bv_omega) (by bv_omega) rfl (by bv_omega)]
  exact Entails.sepExists_right bs (Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.sepExists_right fnPtr (Entails.refl _))))

theorem strSpeAt_reassemble (A : RustAlloc) (out buf w5 : BitVec 64)
    (i : Nat) (bs : List (BitVec 8))
    (b0 : BitVec 8) (b14 : BitVec 32) (b56 : BitVec 16) (b7 : BitVec 8)
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hbuf : buf ≠ 0#64) :
    ((out ↦₆₄ speWord i) ∗
      ((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((out + 0x10#64) ↦₆₄ buf) ∗
      ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      word1421At (out + 0x20#64) b0 b14 b56 b7 ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗
      A.live buf bs.length 1 ∗ (buf ↦ₛ bs)) ⊢
      strSpeAt A out i := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht; omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hvec :
      ((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x10#64) ↦₆₄ buf) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
      vecU8 A (out + 8#64) bs := by
    unfold vecU8 vecU8At vecHeader
    refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) (Entails.sepExists_right buf ?_)
    have e10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
    have e18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
    rw [e10, e18]
    simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte, Nat.sub_self, memRegion_zero,
      sepConj_emp, sepConj_assoc]
    rw [show ((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((out + 0x10#64) ↦₆₄ buf) ∗
          ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ buf ≠ 0⌝ ∗
          A.live buf bs.length 1 ∗ (buf ↦ₛ bs) =
        ⌜True ∧ True ∧ buf ≠ 0⌝ ∗ (((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((out + 0x10#64) ↦₆₄ buf) ∗ ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live buf bs.length 1 ∗ (buf ↦ₛ bs)) by ac_rfl]
    exact Entails.pure_right ⟨trivial, trivial, hbuf⟩ (Entails.refl _)
  have htail16 :
      word1421At (out + 0x20#64) b0 b14 b56 b7 ∗ ((out + 0x28#64) ↦₆₄ w5) ⊢
      memRegion (out + 0x20#64) 16 := by
    refine Entails.trans
      (sepConj_mono (word1421At_entails_memRegion8 _ _ _ _ _)
        (pointsTo64_entails_memRegion _ _)) ?_
    rw [← ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  unfold strSpeAt
  have hreord :
      ((out ↦₆₄ speWord i) ∗
        ((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((out + 0x10#64) ↦₆₄ buf) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        word1421At (out + 0x20#64) b0 b14 b56 b7 ∗ ((out + 0x28#64) ↦₆₄ w5) ∗
        A.live buf bs.length 1 ∗ (buf ↦ₛ bs)) =
      ((out ↦₆₄ speWord i) ∗
        (((out + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((out + 0x10#64) ↦₆₄ buf) ∗
          ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ A.live buf bs.length 1 ∗ (buf ↦ₛ bs)) ∗
        (word1421At (out + 0x20#64) b0 b14 b56 b7 ∗ ((out + 0x28#64) ↦₆₄ w5))) := by
    ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono
    (Entails.trans hvec (Entails.sepExists_right bs (Entails.refl _))) htail16)

theorem slot_b0_err_collapse (sp w0 w1 w2 w3 w5 : BitVec 64)
    (b0 : BitVec 8) (b14 : BitVec 32) (b56 : BitVec 16) (b7 : BitVec 8) :
    (((sp - 0xb0#64) ↦₆₄ w0) ∗ ((sp - 0xa8#64) ↦₆₄ w1) ∗
      ((sp - 0xa0#64) ↦₆₄ w2) ∗ ((sp - 0x98#64) ↦₆₄ w3) ∗
      word1421At (sp - 0x90#64) b0 b14 b56 b7 ∗
      ((sp - 0x88#64) ↦₆₄ w5)) ⊢
      memRegion (sp - 0xb0#64) 48 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (word1421At_entails_memRegion8 _ _ _ _ _)
              (pointsTo64_entails_memRegion _ _)))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 8)
        (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 16)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 24)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 8) (k := 32)
        (b' := sp - 0xa0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 8) (k := 40)
        (b' := sp - 0xa8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_b0_ok_collapse (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 0xb0#64) ↦₆₄ w0) ∗ ((sp - 0xa8#64) ↦₆₄ w1) ∗
      ((sp - 0xa0#64) ↦₆₄ w2) ∗ ((sp - 0x98#64) ↦₆₄ w3) ∗
      memRegion (sp - 0x90#64) 16) ⊢
      memRegion (sp - 0xb0#64) 48 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 16)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 24)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 8) (k := 32)
        (b' := sp - 0xa0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 8) (k := 40)
        (b' := sp - 0xa8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_b0_put_collapse (sp w3 : BitVec 64) :
    (memRegion (sp - 0xb0#64) 24 ∗ ((sp - 0x98#64) ↦₆₄ w3) ∗ memRegion (sp - 0x90#64) 16) ⊢
      memRegion (sp - 0xb0#64) 48 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 16)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 24) (k := 24)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_b0_24_24_merge (sp : BitVec 64) :
    (memRegion (sp - 0xb0#64) 24 ∗ memRegion (sp - 0x98#64) 24) ⊢ memRegion (sp - 0xb0#64) 48 := by
  rw [← ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 24) (k := 24)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
