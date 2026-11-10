/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.AsmConstants

/-!
# Frame Layout and Call Helpers for `remove_pre_key::{closure#0}`

Stack-frame decomposition (`0xc0` bytes), `Vec<u8>` borrow-and-drop and empty-header lemmas,
48-byte sret reassembly, relative callee address equations, and panicking call wrappers.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

/-- Maximum sub-callee stack budget needed below `remove_pre_key::{closure#0}`'s `0xc0` frame. -/
abbrev subMax (decStk getStk putStk : Nat) : Nat :=
  max (max decStk getStk) (max putStk extHookStack)

/-- Minimum stack budget of `remove_pre_key::{closure#0}` (`0xc0` frame + `subMax`). -/
abbrev pollMinStk (decStk getStk putStk : Nat) : Nat :=
  0xc0 + subMax decStk getStk putStk

private theorem q128_hi_lo (q : BitVec 128) :
    q.extractLsb' 64 64 ++ q.extractLsb' 0 64 = q := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', Nat.zero_add]
  split
  · rfl
  · show q[64 + (i - 64)] = q[i]
    congr 1; omega

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

private theorem pointsTo64_pair (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  have hlo : (w1 ++ w0).extractLsb' 0 64 = w0 := by ext i _; simp
  have hhi : (w1 ++ w0).extractLsb' 64 64 = w1 := by ext i _; simp
  unfold Arm64.pointsTo128
  rw [hlo, hhi]

theorem memRegion_16_q128 (a : BitVec 64) :
    memRegion a 16 = (∃∗ q : BitVec 128, (a ↦₁₂₈ q)) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right (w1 ++ w0) (Entails.of_eq (pointsTo64_pair a w0 w1))
  · refine Entails.sepExists_elim fun q => ?_
    refine Entails.sepExists_right (q.extractLsb' 64 64)
      (Entails.sepExists_right (q.extractLsb' 0 64) ?_)
    exact Entails.of_eq (by rw [pointsTo64_pair, q128_hi_lo])

theorem q128_entails_memRegion16 (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) ⊢ memRegion a 16 := by
  rw [memRegion_16_q128 a]
  exact Entails.sepExists_right q (Entails.refl _)

/-- Exact 192-byte (`0xc0`) stack-frame decomposition of `remove_pre_key::{closure#0}`. -/
def pkRemoveFrameSlots (sp : BitVec 64) (q_sp0 : BitVec 128)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : BitVec 64) : SepProp :=
  ((sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
  memRegion (sp - 0xb0#64) 8 ∗
  memRegion (sp - 0xa8#64) 48 ∗
  memRegion (sp - 0x78#64) 24 ∗
  ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗ ((sp - 0x50#64) ↦₆₄ c2) ∗
  memRegion (sp - 0x48#64) 8 ∗
  ((sp - 0x40#64) ↦₆₄ c3) ∗ ((sp - 0x38#64) ↦₆₄ c4) ∗
  ((sp - 0x30#64) ↦₆₄ c5) ∗ ((sp - 0x28#64) ↦₆₄ c6) ∗
  ((sp - 0x20#64) ↦₆₄ c7) ∗ ((sp - 0x18#64) ↦₆₄ c8) ∗
  ((sp - 0x10#64) ↦₆₄ c9) ∗ ((sp - 0x08#64) ↦₆₄ c10)

theorem stackAt_pkRemove_eq (sp : BitVec 64) {sub : Nat} (hsub : 0xc0 + sub ≤ 2 ^ 64) :
    stackAt sp (0xc0 + sub) =
      stackAt (sp - 0xc0#64) sub ∗
      (∃∗ q_sp0 : BitVec 128,
       ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
       ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
       ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64,
        pkRemoveFrameSlots sp q_sp0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10) := by
  have htop : stackAt sp (sub + 192) = stackAt (sp - 0xc0#64) sub ∗ memRegion (sp - 0xc0#64) 192 := by
    simp only [stackAt]
    have hbv : sp - BitVec.ofNat 64 (sub + 192) = sp - 0xc0#64 - BitVec.ofNat 64 sub := by bv_omega
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (sub + 192))
          (n := sub) (k := 192) (b' := sp - 0xc0#64)
          (by omega) (by bv_omega) (by omega), hbv]
  have hm24 : memRegion (sp - 0x60#64) 24 = cells (sp - 0x60#64) 3 :=
    ProofLib.memRegion_cells (sp - 0x60#64) 3 (by decide)
  have hm64 : memRegion (sp - 0x40#64) 64 = cells (sp - 0x40#64) 8 :=
    ProofLib.memRegion_cells (sp - 0x40#64) 8 (by decide)
  rw [show 0xc0 + sub = sub + 192 by omega, htop,
      ProofLib.memRegion_split' (b := sp - 0xc0#64) (n := 16) (k := 176)
        (b' := sp - 0xb0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 8) (k := 168)
        (b' := sp - 0xa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 48) (k := 120)
        (b' := sp - 0x78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x78#64) (n := 24) (k := 96)
        (b' := sp - 0x60#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x60#64) (n := 24) (k := 72)
        (b' := sp - 0x48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x48#64) (n := 8) (k := 64)
        (b' := sp - 0x40#64) rfl (by bv_omega) (by decide),
      memRegion_16_q128 (sp - 0xc0#64),
      hm24, hm64]
  have hc3 : cells (sp - 0x60#64) 3 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
        ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗ ((sp - 0x50#64) ↦₆₄ c2)) := by
    cells_unfold
  have hc8 : cells (sp - 0x40#64) 8 =
      (∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
       ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64,
        ((sp - 0x40#64) ↦₆₄ c3) ∗ ((sp - 0x38#64) ↦₆₄ c4) ∗
        ((sp - 0x30#64) ↦₆₄ c5) ∗ ((sp - 0x28#64) ↦₆₄ c6) ∗
        ((sp - 0x20#64) ↦₆₄ c7) ∗ ((sp - 0x18#64) ↦₆₄ c8) ∗
        ((sp - 0x10#64) ↦₆₄ c9) ∗ ((sp - 0x08#64) ↦₆₄ c10)) := by
    cells_unfold
  rw [hc3, hc8]
  simp only [pkRemoveFrameSlots, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c4 =>
      Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c6 =>
      Entails.sepExists_elim fun c7 => Entails.sepExists_elim fun c8 =>
      Entails.sepExists_elim fun c9 => Entails.sepExists_elim fun c10 =>
      Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
      Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun q_sp0 => ?_
    refine Entails.sepExists_right q_sp0
      (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
      (Entails.sepExists_right c9 (Entails.sepExists_right c10
        (Entails.of_eq (by ac_rfl)))))))))))))
  · refine Entails.sepExists_elim fun q_sp0 =>
      Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
      Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
      Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
      Entails.sepExists_elim fun c6 => Entails.sepExists_elim fun c7 =>
      Entails.sepExists_elim fun c8 => Entails.sepExists_elim fun c9 =>
      Entails.sepExists_elim fun c10 => ?_
    refine Entails.sepExists_right c3 (Entails.sepExists_right c4
      (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.sepExists_right c8
      (Entails.sepExists_right c9 (Entails.sepExists_right c10
      (Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right q_sp0
        (Entails.of_eq (by ac_rfl)))))))))))))

theorem stackAt_pkRemove_of_parts (sp : BitVec 64) {sub : Nat} (hsub : 0xc0 + sub ≤ 2 ^ 64)
    (q_sp0 : BitVec 128) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : BitVec 64) :
    (stackAt (sp - 0xc0#64) sub ∗
      pkRemoveFrameSlots sp q_sp0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10) ⊢
      stackAt sp (0xc0 + sub) := by
  rw [stackAt_pkRemove_eq sp hsub]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right q_sp0
    (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
    (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
    (Entails.sepExists_right c9 (Entails.sepExists_right c10
      (Entails.refl _))))))))))))

/-- Split `memRegion out 48` into 4 words + 1 quadword written in the epilogue. -/
theorem sret48_epilogue_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
       ∃∗ oq : BitVec 128,
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 0x10#64) ↦₆₄ o2) ∗
        ((out + 0x18#64) ↦₆₄ o3) ∗ ((out + 0x20#64) ↦₁₂₈ oq)) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 32) (k := 16)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
      memRegion_split out 8 (8 + (8 + 8)) (by decide),
      memRegion_split (out + 8#64) 8 (8 + 8) (by decide),
      memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      memRegion_16_q128 (out + 0x20#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun oq => Entails.sepExists_elim fun o3 =>
      Entails.sepExists_elim fun o2 => Entails.sepExists_elim fun o1 =>
      Entails.sepExists_elim fun o0 => ?_
    refine Entails.sepExists_right o0 (Entails.sepExists_right o1
      (Entails.sepExists_right o2 (Entails.sepExists_right o3
      (Entails.sepExists_right oq (Entails.of_eq (by ac_rfl))))))
  · refine Entails.sepExists_elim fun o0 => Entails.sepExists_elim fun o1 =>
      Entails.sepExists_elim fun o2 => Entails.sepExists_elim fun o3 =>
      Entails.sepExists_elim fun oq => ?_
    refine Entails.sepExists_right oq (Entails.sepExists_right o3
      (Entails.sepExists_right o2 (Entails.sepExists_right o1
      (Entails.sepExists_right o0 (Entails.of_eq (by ac_rfl))))))

/-! ## `Vec<u8>` borrow-and-drop & zero-capacity empty `Vec` lemmas -/

/-- Remaining heap ownership of a `Vec<u8>` after borrowing `SpqrV1.ChainProofs.bytesAt false ptr bs`. -/
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
      rw [sepConj_emp]
      ac_rfl
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

/-- `[cap = 0, ptr = 1, len = 0]` at `v` forms a valid zero-capacity empty `vecU8 A v []`. -/
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

/-! ## Discriminant & sret reassembly lemmas (`Err`, `Ok(())`) -/

theorem speWord_one_add_two_ne_zero : (speWord 1 + 2#64 == 0#64) = false := by
  decide +kernel

theorem okTagVec_add_two_eq_zero : (okTagVec + 2#64 == 0#64) = true := by
  decide +kernel

/-- Exact inline+heap payload of `speAt A (utf8 "read") r .invalidState`. -/
def speReadHeap (A : RustAlloc) (bs : List (BitVec 8)) (cap ptr fnPtr : BitVec 64) : SepProp :=
  (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    if cap = 0#64 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
  (fnPtr ↦ᵣ utf8 "read")

theorem speAt_read_invalidState_eq (A : RustAlloc) (r r8 r10 r18 r20 : BitVec 64)
    (hr8 : r + 8#64 = r8) (hr10 : r8 + 8#64 = r10) (hr18 : r8 + 16#64 = r18)
    (hr20 : r + 0x20#64 = r20) :
    speAt A (utf8 "read") r .invalidState =
      (∃∗ bs : List (BitVec 8), ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ fnPtr : BitVec 64,
        (r ↦₆₄ speWord 1) ∗ (r8 ↦₆₄ cap) ∗ (r10 ↦₆₄ ptr) ∗
        (r18 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (r20 ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        speReadHeap A bs cap ptr fnPtr) := by
  subst hr8; subst hr10; subst hr18; subst hr20
  unfold speAt speReadHeap vecU8 vecU8At vecHeader strRefAt
  have e1 : r + asm64% spePayloadOff = r + 8#64 := by bv_omega
  have e4 : r + asm64% speInvalidStateFnOff = r + 0x20#64 := by bv_omega
  rw [e1, e4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_elim fun bs =>
      Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.sepExists_right bs (Entails.sepExists_right cap
      (Entails.sepExists_right ptr (Entails.sepExists_right fnPtr ?_)))
    rw [← pointsTo64_pair (r + 0x20#64) fnPtr (BitVec.ofNat 64 (utf8 "read").length)]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun bs => Entails.sepExists_elim fun cap =>
      Entails.sepExists_elim fun ptr => Entails.sepExists_elim fun fnPtr => ?_
    refine Entails.sepExists_right fnPtr (Entails.sepExists_right bs
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)))
    rw [← pointsTo64_pair (r + 0x20#64) fnPtr (BitVec.ofNat 64 (utf8 "read").length)]
    exact Entails.of_eq (by ac_rfl)

theorem speAt_read_invalidState_intro (A : RustAlloc) (out : BitVec 64)
    (bs : List (BitVec 8)) (cap ptr fnPtr : BitVec 64) :
    ((out ↦₆₄ speWord 1) ∗ ((out + 8#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
      ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((out + 0x20#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
      speReadHeap A bs cap ptr fnPtr) ⊢
      pkRemoveOutAt A out (.error ()) := by
  show _ ⊢ speAt A (utf8 "read") out .invalidState
  rw [speAt_read_invalidState_eq A out (out + 8#64) (out + 0x10#64) (out + 0x18#64) (out + 0x20#64)
        rfl (by bv_omega) (by bv_omega) rfl]
  exact Entails.sepExists_right bs (Entails.sepExists_right cap
    (Entails.sepExists_right ptr (Entails.sepExists_right fnPtr (Entails.refl _))))

theorem pkRemoveOutAt_ok_reassemble (A : RustAlloc) (out w1 w2 w3 : BitVec 64) (q0 : BitVec 128) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₁₂₈ q0)) ⊢
      pkRemoveOutAt A out (.ok ()) := by
  unfold pkRemoveOutAt
  refine sepConj_mono_right ?_
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (q128_entails_memRegion16 _ _)))) ?_
  rw [← ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24)
        (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 32)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_a8_err_collapse (sp w0 w1 w2 w3 : BitVec 64) (q : BitVec 128) :
    (((sp - 0xa8#64) ↦₆₄ w0) ∗ ((sp - 0xa0#64) ↦₆₄ w1) ∗
      ((sp - 0x98#64) ↦₆₄ w2) ∗ ((sp - 0x90#64) ↦₆₄ w3) ∗
      ((sp - 0x88#64) ↦₁₂₈ q)) ⊢
      memRegion (sp - 0xa8#64) 48 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (q128_entails_memRegion16 _ _))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 16)
        (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 24)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 32)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 8) (k := 40)
        (b' := sp - 0xa0#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_a8_ok_collapse (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 0xa8#64) ↦₆₄ w0) ∗ ((sp - 0xa0#64) ↦₆₄ w1) ∗
      ((sp - 0x98#64) ↦₆₄ w2) ∗ ((sp - 0x90#64) ↦₆₄ w3) ∗
      memRegion (sp - 0x88#64) 16) ⊢
      memRegion (sp - 0xa8#64) 48 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 16)
        (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 24)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 32)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 8) (k := 40)
        (b' := sp - 0xa0#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot_a8_put_collapse (sp w3 : BitVec 64) :
    (memRegion (sp - 0xa8#64) 24 ∗ ((sp - 0x90#64) ↦₆₄ w3) ∗ memRegion (sp - 0x88#64) 16) ⊢
      memRegion (sp - 0xa8#64) 48 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 16)
        (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 24) (k := 24)
        (b' := sp - 0x90#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-! ## Relative callee address equations -/

theorem decimal_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pkRemovePollName +
      bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "libsignal_cli::stores::decimal") =
      (tripleRatchetProgAtExt b ext).fnAddr decimalName := by
  have h1 := pkRemovePoll_fnOff
  have h2 := decimal_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkRemovePollName, decimalName, h1, h2]
  bv_omega

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pkRemovePollName +
      bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "<libsignal_cli::stores::Dir>::get") =
      (tripleRatchetProgAtExt b ext).fnAddr dirGetName := by
  have h1 := pkRemovePoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkRemovePollName, dirGetName, h1, h2]
  bv_omega

theorem dirPut_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pkRemovePollName -
      bv% (ls_rel%
        "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr dirPutName := by
  have h1 := pkRemovePoll_fnOff
  have h2 := dirPut_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkRemovePollName, dirPutName, h1, h2]
  bv_omega

theorem files_eq_of_fsInv_trace_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hinv : FsInv F0 T0 s) (ht : s.trace = T0) : s.fs.files = F0 :=
  files_eq_at_callback hinv (ht.trans (List.append_nil T0).symm) .nil

/-! ## Shared state, stack, epilogue bundle, and call wrappers -/

theorem calleeSavedVRegs_writeVReg128_0 (s : State) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 val (by decide)

theorem setWidth_32_setWidth_64 (v : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  ext i _hi; simp

theorem fs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by cases s; rfl
theorem fs_advancePC (s : State) : s.advancePC.fs = s.fs := by cases s; rfl
theorem fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
theorem fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases w <;> cases s <;> rfl
theorem fs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).fs = s.fs := by cases s; rfl
theorem fs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by cases wb <;> cases s <;> rfl

theorem spAligned_sub_c0 {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 0xc0#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem subStack_split (sp : BitVec 64) {decStk getStk putStk K : Nat}
    (hK : K ≤ subMax decStk getStk putStk)
    (hhi : pollMinStk decStk getStk putStk ≤ 2 ^ 64) :
    stackAt (sp - 0xc0#64) (subMax decStk getStk putStk) =
      memRegion (sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - K) ∗
      stackAt (sp - 0xc0#64) K :=
  stackAt_sub_split (sp - 0xc0#64) hK (by unfold pollMinStk at hhi; omega)

def savedCalleeSlots (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x27) ∗
  memRegion (s0.sp - 0x48#64) 8 ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

def epiloguePre (s0 : State) (x : PkPollGhost) (q_sp0 : BitVec 128) : SepProp :=
  ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
  memRegion x.out 48 ∗
  pkBoxAt x.fut x.self x.id 0#8 ∗
  savedCalleeSlots s0

def epilogueOut (s0 : State) (x : PkPollGhost)
    (w0 w1 w2 w3 : BitVec 64) (q_sp0 : BitVec 128) : SepProp :=
  (x.out ↦₆₄ w0) ∗ ((x.out + 8#64) ↦₆₄ w1) ∗
  ((x.out + 0x10#64) ↦₆₄ w2) ∗ ((x.out + 0x18#64) ↦₆₄ w3) ∗
  ((x.out + 0x20#64) ↦₁₂₈ q_sp0) ∗
  ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
  pkBoxAt x.fut x.self x.id 1#8 ∗
  savedCalleeSlots s0

theorem restore_pollStack (s0 : State) {decStk getStk putStk stk : Nat}
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (q_sp0 : BitVec 128) :
    (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗
      memRegion (s0.sp - 0x78#64) 24 ∗
      savedCalleeSlots s0) ⊢
      stackAt s0.sp stk := by
  have hmin : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  rw [stackAt_sub_split s0.sp hstk hhi]
  refine sepConj_mono_right ?_
  refine Entails.trans ?_
    (stackAt_pkRemove_of_parts s0.sp hmin q_sp0
      (s0.readReg64 .x29) (s0.readReg64 .lr) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
  rw [subStack_split s0.sp hext hmin]
  unfold pkRemoveFrameSlots savedCalleeSlots
  exact Entails.of_eq (by ac_rfl)

theorem layoutOk_u8_of_ne_zero {cap : BitVec 64} (hc : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem pkrm_dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := pkRemovePollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "__rustc::__rust_dealloc"))
    (by rw [pkRemovePoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem sepWPp_conseq {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : P ⊢ P')
    (hw : SepWPp prog ret s P' Q Qp) : SepWPp prog ret s P Q Qp :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_with_stk_bound {prog : Program} {ret : BitVec 64} {s : State}
    {stk : Nat} {a v : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P ⊢ stackAt s.sp stk ∗ (a ↦₆₄ v) ∗ Rest)
    (hw : stk ≤ 2 ^ 64 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  have hm' : s.mem ⊨ memRegion (s.sp - BitVec.ofNat 64 stk) stk ∗ ((a ↦₆₄ v) ∗ (Rest ∗ R)) := by
    have h1 := Satisfies.mono (sepConj_mono_left hfoc) hm
    simpa only [stackAt, sepConj_assoc] using h1
  exact hw (memRegion_bound_of_pointsTo64 hm') R hm hL

/-- Call any `Spec` whose panic implies `allocFailedIn` and whose exit/OOM are `False`, preserving `ImgCallInv img`. -/
theorem pkrm_call_panicking_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ProofLib.SepWPp.call_wpp_frozen hcall (x := x) (F := F) hinv.1 hinv.2
    hpc hrun hsp_align hlr
    (fun R' hm => by
      have hm' := Satisfies.mono (sepConj_mono_left hpre) hm
      rwa [sepConj_assoc] at hm')
    (fun sm code R' _ hex => hexit_imp code sm R' hex)
    (fun sm _ ⟨R', hpost⟩ =>
      hpan sm _ (by simpa [allocFailedIn, htr] using hpan_imp sm R' hpost))
    (fun sm hpcm hrunm hspm hcsm hfz hsym =>
      hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sm R' _ hpost => (hoom_imp sm (F ∗ R') hpost).elim)

theorem pkrm_call_decimal_fs {prog : Program} {img : Obj.Image} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (decimalSpec A img decStk) s0_files s0_trace))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      FsInv s0_files s0_trace sm → sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hfs
      (Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _)))
  · intro sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFsInv, decimalSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfsm htrm)

theorem pkrm_call_decimal {prog : Program} {img : Obj.Image} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (decimalSpec A img decStk))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [decimalSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [decimalSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [decimalSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [decimalSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [decimalSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem pkrm_call_dirGet {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpec rd pathOk A img getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirGetSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hgr)

theorem pkrm_call_dirPut {prog : Program} {img : Obj.Image} {A : RustAlloc} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutSpec A img putStk))
    (xg : DirPutGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ vecU8 A xg.nameV xg.name ∗
      vecU8 A xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((dirAt A xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirPutSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirPutSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirPutSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
