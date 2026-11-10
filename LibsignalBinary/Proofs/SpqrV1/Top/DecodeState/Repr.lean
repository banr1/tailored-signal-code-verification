/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Defs
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs
import ProofLib.SepLogic.WPp

/-!
# Binary Verification of `spqr::decode_state` (`0x5349c`) — Representations & Callee Specs

**Checked by Lean.**

Defines spatial heap predicates for `PqRatchetState`, `ChainPB`, `ChainEpochPB`, and
`VersionNegotiationPB`, error discriminant encodings, and base callee contracts for
`spqr::decode_state`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `BytesMergeCapOk` & Default Initialization Lemmas -/

theorem bytesMergeCapOk_zero (n : Nat) : BytesMergeCapOk 0#64 n :=
  Or.inl rfl

theorem bytesMergeCapOk_mono {cap : BitVec 64} {m n : Nat}
    (h : BytesMergeCapOk cap n) (hle : m ≤ n) : BytesMergeCapOk cap m := by
  rcases h with h0 | hlt
  · exact Or.inl h0
  · exact Or.inr (by omega)

theorem vecU8At_nil_zero_one (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8At A a 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  simp only [List.length_nil, Nat.zero_le, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_lt_succ,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_self, BitVec.ofNat_eq_ofNat, ↓reduceIte,
    sepConj_emp]
  rw [sepConj_comm _ ⌜_⌝]
  apply Entails.pure_right ⟨trivial, by decide, by decide⟩
  exact Entails.refl _

theorem rustBytesVecAt_default_init (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      rustBytesVecAt A a [] := by
  unfold rustBytesVecAt vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (vecU8At_nil_zero_one A a))

theorem chainLinksVecAt_default_init (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      chainLinksVecAt A a [] := by
  unfold chainLinksVecAt vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  simp only [List.length_nil, Nat.zero_le, BitVec.toNat_ofNat, Nat.zero_mul, Nat.reducePow,
    Nat.zero_lt_succ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_self,
    BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm _ ⌜_⌝]
  apply Entails.pure_right ⟨trivial, by decide, by decide⟩
  exact Entails.refl _

theorem pointsTo64_one_split32 (a : BitVec 64) :
    (a ↦₆₄ 1#64) = (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  rw [pointsTo64_split32' a 1#64]
  rfl

theorem pointsTo64_zero_split32 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  rw [pointsTo64_split32' a 0#64]
  rfl

theorem optChainParamsPBAt_none_init (a : BitVec 64) :
    (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 8 ⊢ optChainParamsPBAt a none :=
  Entails.refl _

theorem optChainParamsPBAt_some_default_init (a : BitVec 64) :
    (a ↦₆₄ 1#64) ∗ ((a + 8#64) ↦₃₂ 0#32) ⊢ optChainParamsPBAt a (some default) := by
  rw [chainParamsPB_default_eq]
  unfold optChainParamsPBAt chainParamsPBAt
  dsimp only
  rw [pointsTo64_one_split32 a]
  have ha : (a + 4#64) + 4#64 = a + 8#64 := by bv_omega
  rw [ha]
  exact Entails.of_eq (by ac_rfl)

theorem epochDirectionPBAt_default_init (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      ((a + 48#64) ↦₃₂ 0#32) ∗ memRegion (a + 52#64) 4 ⊢
    epochDirectionPBAt A a default := by
  rw [epochDirectionPB_default_eq]
  unfold epochDirectionPBAt
  dsimp only
  have h1 := rustBytesVecAt_default_init A a
  have h2 := rustBytesVecAt_default_init A (a + 24#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  exact sepConj_mono h1 (sepConj_mono_left h2)

theorem versionNegotiationPBAt_default_init (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      ((a + 24#64) ↦₃₂ 0#32) ∗ memRegion (a + 28#64) 8 ∗
      ((a + 36#64) ↦₆₄ 0#64) ∗ memRegion (a + 44#64) 4 ⊢
    versionNegotiationPBAt A a default := by
  rw [versionNegotiationPB_default_eq]
  unfold versionNegotiationPBAt optChainParamsPBAt
  dsimp only
  have h1 := rustBytesVecAt_default_init A a
  have h36 : ((a + 36#64) ↦₆₄ 0#64) = ((a + 36#64) ↦₃₂ 0#32) ∗ ((a + 40#64) ↦₃₂ 0#32) := by
    rw [pointsTo64_zero_split32 (a + 36#64)]
    have : (a + 36#64) + 4#64 = a + 40#64 := by bv_omega
    rw [this]
  have ha28 : (a + 24#64) + 4#64 = a + 28#64 := by bv_omega
  rw [h36, ha28]
  refine Entails.trans (sepConj_mono_left h1) ?_
  exact Entails.of_eq (by ac_rfl)

theorem chainPBAt_default_init (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 0#64) ∗
      ((a + 64#64) ↦₃₂ 0#32) ∗ memRegion (a + 68#64) 8 ∗
      ((a + 76#64) ↦₃₂ 0#32) ⊢
    chainPBAt A a default := by
  rw [chainPB_default_eq]
  unfold chainPBAt optChainParamsPBAt
  dsimp only
  have h1 := chainLinksVecAt_default_init A a
  have h2 := rustBytesVecAt_default_init A (a + 24#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have ha68 : (a + 64#64) + 4#64 = a + 68#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [ha68]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. `PqRatchetState` Representation (`352`B) & `Quads` Helpers -/

/-- Size of `Option<V1State.InnerState>` (`V1State` / `Option<PqRatchetState.Inner>`): `224` bytes (`0xe0`). -/
def optProtoInnerStateSize : Nat := 224

/-- Size of `PqRatchetState` and `Result<PqRatchetState, spqr::Error>`: `352` bytes (`0x160`). -/
def protoPqRatchetStateSize : Nat := 352

theorem sepExists_prod {α β : Type} (P : α × β → SepProp) :
    (∃∗ x : α × β, P x) = ∃∗ a : α, ∃∗ b : β, P (a, b) :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun ⟨a, b⟩ =>
      Entails.sepExists_right a (Entails.sepExists_right b (Entails.refl _)))
    (Entails.sepExists_elim fun a =>
      Entails.sepExists_elim fun b =>
        Entails.sepExists_right (a, b) (Entails.refl _))

theorem sepExists_sepConj_prod {α β : Type} (P : α → SepProp) (Q : β → SepProp) :
    ((∃∗ a : α, P a) ∗ (∃∗ b : β, Q b)) = ∃∗ x : α × β, P x.1 ∗ Q x.2 := by
  rw [sepExists_prod]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun b =>
      Entails.sepExists_elim fun a =>
        Entails.sepExists_right a (Entails.sepExists_right b (Entails.refl _)))
    (Entails.sepExists_elim fun a =>
      Entails.sepExists_elim fun b =>
        Entails.sepExists_right b (Entails.sepExists_right a (Entails.refl _)))

/-- 7 quadwords (`56` bytes = `0x38`) at base address `a`. -/
abbrev Quads7 : Type :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

/-- 14 quadwords (`112` bytes = `0x70`) at base address `a`, factored as two `Quads7` halves (`+0` and `+56`). -/
abbrev Quads14 : Type := Quads7 × Quads7

/-- 28 quadwords (`224` bytes = `0xe0`) at base address `a`, factored as two `Quads14` halves (`+0` and `+112`). -/
abbrev Quads28 : Type := Quads14 × Quads14

def quads7At (a : BitVec 64) (q : Quads7) : SepProp :=
  let (w0, w1, w2, w3, w4, w5, w6) := q
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
  ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
  ((a + 48#64) ↦₆₄ w6)

def quads14At (a : BitVec 64) (q : Quads14) : SepProp :=
  quads7At a q.1 ∗ quads7At (a + 56#64) q.2

def quads28At (a : BitVec 64) (q : Quads28) : SepProp :=
  quads14At a q.1 ∗ quads14At (a + 112#64) q.2

abbrev Quads7.head (q : Quads7) : BitVec 64 := q.1
abbrev Quads14.head (q : Quads14) : BitVec 64 := q.1.1
abbrev Quads28.head (q : Quads28) : BitVec 64 := q.1.1.1

theorem memRegion_56_eq_quads7At (a : BitVec 64) :
    memRegion a 56 = ∃∗ q : Quads7, quads7At a q := by
  rw [ProofLib.memRegion_cells a 7 (by decide)]
  unfold Quads7 quads7At
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_prod, sepExists_sepConj_left, sepExists_sepConj_right]

theorem quads7At_entails_memRegion_56 (a : BitVec 64) (q : Quads7) :
    quads7At a q ⊢ memRegion a 56 := by
  rw [memRegion_56_eq_quads7At a]
  exact Entails.sepExists_intro q

theorem memRegion_112_eq_quads14At (a : BitVec 64) :
    memRegion a 112 = ∃∗ q : Quads14, quads14At a q := by
  rw [ProofLib.memRegion_split' (b := a) (n := 56) (k := 56) (b' := a + 56#64) rfl rfl (by decide),
      memRegion_56_eq_quads7At a, memRegion_56_eq_quads7At (a + 56#64)]
  exact sepExists_sepConj_prod (quads7At a) (quads7At (a + 56#64))

theorem quads14At_entails_memRegion_112 (a : BitVec 64) (q : Quads14) :
    quads14At a q ⊢ memRegion a 112 := by
  rw [memRegion_112_eq_quads14At a]
  exact Entails.sepExists_intro q

theorem memRegion_224_eq_quads28At (a : BitVec 64) :
    memRegion a 224 = ∃∗ q : Quads28, quads28At a q := by
  rw [ProofLib.memRegion_split' (b := a) (n := 112) (k := 112) (b' := a + 112#64) rfl rfl (by decide),
      memRegion_112_eq_quads14At a, memRegion_112_eq_quads14At (a + 112#64)]
  exact sepExists_sepConj_prod (quads14At a) (quads14At (a + 112#64))

theorem quads28At_entails_memRegion_224 (a : BitVec 64) (q : Quads28) :
    quads28At a q ⊢ memRegion a 224 := by
  rw [memRegion_224_eq_quads28At a]
  exact Entails.sepExists_intro q

/-! ## 3. Address-Independent Heap Factorization for `ChainEpochPB` (`112`B) -/

/-- Address-independent heap portion of `vecU8At A a cap ptr bs`. -/
def vecU8Heap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
     memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_heap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Heap A cap ptr bs := rfl

/-- Address-independent heap predicate for `optEpochDirectionPBAt A a opt` (`56`B) given its 7 inline quadwords `q`. -/
def optEpochDirectionPBHeap (A : RustAlloc) (q : Quads7) : Option EpochDirectionPB → SepProp
  | none =>
    ⌜q.1 = noneCap⌝
  | some d =>
    let (w0, w1, w2, w3, w4, w5, w6) := q
    ⌜w2 = BitVec.ofNat 64 d.next.length ∧ w5 = BitVec.ofNat 64 d.prev.length ∧ w6.truncate 32 = d.ctr⌝ ∗
    vecU8Heap A w0 w1 d.next ∗
    vecU8Heap A w3 w4 d.prev

/-- Address-independent heap predicate for `chainEpochPBAt A a ep` (`112`B) given its 14 inline quadwords `q`. -/
def chainEpochPBHeap (A : RustAlloc) (q : Quads14) (ep : ChainEpochPB) : SepProp :=
  optEpochDirectionPBHeap A q.1 ep.send ∗
    optEpochDirectionPBHeap A q.2 ep.recv

theorem truncate32_append32 (hi lo : BitVec 32) : (hi ++ lo).truncate 32 = lo := by
  bv_bits

theorem optEpochDirectionPBAt_entails_quads7 (A : RustAlloc) (a : BitVec 64)
    (opt : Option EpochDirectionPB) :
    optEpochDirectionPBAt A a opt ⊢
      ∃∗ q : Quads7, quads7At a q ∗ optEpochDirectionPBHeap A q opt := by
  cases opt with
  | none =>
    unfold optEpochDirectionPBAt optEpochDirectionPBHeap
    rw [ProofLib.memRegion_cells (a + 8#64) 6 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    refine Entails.sepExists_right (noneCap, w1, w2, w3, w4, w5, w6) ?_
    unfold quads7At
    dsimp only
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_right rfl
    exact Entails.of_eq (by ac_rfl)
  | some d =>
    unfold optEpochDirectionPBAt epochDirectionPBAt rustBytesVecAt vecU8
    rw [ProofLib.memRegion_four (a + 52#64)]
    simp only [vecU8At_eq_header_heap, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pad
    apply Entails.sepExists_elim; intro cap2
    apply Entails.sepExists_elim; intro ptr2
    apply Entails.sepExists_elim; intro cap1
    apply Entails.sepExists_elim; intro ptr1
    refine Entails.sepExists_right
      (cap1, ptr1, BitVec.ofNat 64 d.next.length, cap2, ptr2, BitVec.ofNat 64 d.prev.length, pad ++ d.ctr) ?_
    have h48 : ((a + 48#64) ↦₃₂ d.ctr) ∗ ((a + 52#64) ↦₃₂ pad) =
        ((a + 48#64) ↦₆₄ (pad ++ d.ctr)) := by
      have ha : a + 52#64 = a + 48#64 + 4#64 := by bv_omega
      rw [ha, pointsTo32_pair (a + 48#64) d.ctr pad]
    have hpure : ⌜BitVec.ofNat 64 d.next.length = BitVec.ofNat 64 d.next.length ∧
        BitVec.ofNat 64 d.prev.length = BitVec.ofNat 64 d.prev.length ∧
        (pad ++ d.ctr).truncate 32 = d.ctr⌝ = emp := by
      simp [truncate32_append32]
    unfold quads7At optEpochDirectionPBHeap
    dsimp only
    rw [hpure, emp_sepConj, ← h48]
    exact Entails.of_eq (by ac_rfl)

theorem quads7_entails_optEpochDirectionPBAt (A : RustAlloc) (a : BitVec 64)
    (q : Quads7) (opt : Option EpochDirectionPB) :
    quads7At a q ∗ optEpochDirectionPBHeap A q opt ⊢
      optEpochDirectionPBAt A a opt := by
  rcases q with ⟨w0, w1, w2, w3, w4, w5, w6⟩
  cases opt with
  | none =>
    unfold optEpochDirectionPBAt optEpochDirectionPBHeap quads7At
    dsimp only
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_left; intro hw0; subst hw0
    have h48 :
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ⊢
        memRegion (a + 8#64) 48 := by
      rw [ProofLib.memRegion_cells (a + 8#64) 6 (by decide)]
      simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
        BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
      exact Entails.sepExists_right w1 (Entails.sepExists_right w2
        (Entails.sepExists_right w3 (Entails.sepExists_right w4
          (Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))))))
    have hgroup :
        ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
          ((a + 48#64) ↦₆₄ w6)) =
        ((a ↦₆₄ noneCap) ∗
          (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
           ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6))) := by ac_rfl
    rw [hgroup]
    exact sepConj_mono_right h48
  | some d =>
    unfold optEpochDirectionPBAt epochDirectionPBAt optEpochDirectionPBHeap quads7At
    dsimp only
    rw [← sepConj_assoc, sepConj_comm _ ⌜_⌝, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨rfl, rfl, hctr⟩
    unfold rustBytesVecAt vecU8
    simp only [vecU8At_eq_header_heap, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_)))
    have h48 : ((a + 48#64) ↦₆₄ w6) ⊢
        ((a + 48#64) ↦₃₂ d.ctr) ∗ memRegion (a + 52#64) 4 := by
      rw [pointsTo64_split32' (a + 48#64) w6, hctr]
      have ha : a + 48#64 + 4#64 = a + 52#64 := by bv_omega
      rw [ha]
      exact sepConj_mono_right (ProofLib.pointsTo32_entails_memRegion _ _)
    have hgroup :
        (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
          ((a + 48#64) ↦₆₄ w6)) ∗
         (vecU8Heap A w0 w1 d.next ∗ vecU8Heap A w3 w4 d.prev)) =
        (((a + 48#64) ↦₆₄ w6) ∗
         (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
           vecU8Heap A w0 w1 d.next) ∗
          (((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
           vecU8Heap A w3 w4 d.prev))) := by ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left h48) ?_
    exact Entails.of_eq (by ac_rfl)

theorem chainEpochPBAt_entails_quads14 (A : RustAlloc) (a : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A a ep ⊢
      ∃∗ q : Quads14, quads14At a q ∗ chainEpochPBHeap A q ep := by
  unfold chainEpochPBAt
  refine Entails.trans
    (sepConj_mono (optEpochDirectionPBAt_entails_quads7 A a ep.send)
      (optEpochDirectionPBAt_entails_quads7 A (a + 56#64) ep.recv)) ?_
  rw [sepExists_sepConj_prod]
  apply Entails.sepExists_elim; intro q
  refine Entails.sepExists_right q ?_
  unfold quads14At chainEpochPBHeap
  exact Entails.of_eq (by ac_rfl)

theorem quads14_entails_chainEpochPBAt (A : RustAlloc) (a : BitVec 64)
    (q : Quads14) (ep : ChainEpochPB) :
    quads14At a q ∗ chainEpochPBHeap A q ep ⊢
      chainEpochPBAt A a ep := by
  unfold quads14At chainEpochPBHeap chainEpochPBAt
  have hgroup :
      (quads7At a q.1 ∗ quads7At (a + 56#64) q.2) ∗
        (optEpochDirectionPBHeap A q.1 ep.send ∗ optEpochDirectionPBHeap A q.2 ep.recv) =
      (quads7At a q.1 ∗ optEpochDirectionPBHeap A q.1 ep.send) ∗
        (quads7At (a + 56#64) q.2 ∗ optEpochDirectionPBHeap A q.2 ep.recv) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono
    (quads7_entails_optEpochDirectionPBAt A a q.1 ep.send)
    (quads7_entails_optEpochDirectionPBAt A (a + 56#64) q.2 ep.recv)

/-! ## 4. `V1State` (`224`B) & `PqRatchetState` (`352`B) Representation Predicates -/

/-- Address-independent heap predicate for `V1State.InnerState` parameterized by its 28 inline
    quadwords (`224` bytes = `0xe0`). -/
abbrev V1InnerHeapPred := RustAlloc → Quads28 → V1State.InnerState → SepProp

/-- `Option<spqr::proto::pq_ratchet::v1_state::InnerState>` (`V1State`) at `a` (`224` bytes = `0xe0`):
    * `none`: `(a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216` (`-2` niche at `+0x00`)
    * `some is`: `∃∗ q : Quads28, ⌜q.head ≠ none3Cap⌝ ∗ quads28At a q ∗ H_inner A q is` -/
def optProtoInnerStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64) :
    Option V1State.InnerState → SepProp
  | none => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216
  | some is =>
    ∃∗ q : Quads28,
      ⌜q.head ≠ none3Cap⌝ ∗
      quads28At a q ∗
      H_inner A q is

/-- Address-independent heap predicate for `optProtoInnerStateAt H_inner A a opt` given its 28 inline quadwords `q`. -/
def optProtoInnerStateHeap (H_inner : V1InnerHeapPred) (A : RustAlloc) (q : Quads28) :
    Option V1State.InnerState → SepProp
  | none => ⌜q.head = none2Cap⌝
  | some is => ⌜q.head ≠ none3Cap⌝ ∗ H_inner A q is

/-- `Option<spqr::proto::pq_ratchet::pq_ratchet_state::Inner>` at `a` (`224` bytes = `0xe0`):
    * `none`: `(a ↦₆₄ none3Cap) ∗ memRegion (a + 8#64) 216` (`-3` niche at `+0x00`)
    * `some (.v1 v1)`: `optProtoInnerStateAt H_inner A a v1.innerState` -/
def optProtoPqRatchetInnerAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64) :
    Option PqRatchetState.Inner → SepProp
  | none => (a ↦₆₄ none3Cap) ∗ memRegion (a + 8#64) 216
  | some (.v1 v1) => optProtoInnerStateAt H_inner A a v1.innerState

/-- Representation predicate for `spqr::proto::pq_ratchet::PqRatchetState` at `a` (`352` bytes = `0x160`):
    * `a + 0x00`: `version_negotiation: Option<VersionNegotiation>` (`48`B, tag 1)
    * `a + 0x30` (`+48`): `chain: Option<Chain>` (`80`B, tag 2)
    * `a + 0x80` (`+128`): `inner: Option<PqRatchetState.Inner>` (`224`B, tag 3) -/
def protoPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64)
    (st : PqRatchetState) : SepProp :=
  optVersionNegotiationPBAt A a st.versionNegotiation ∗
    optChainPBAt A (a + 48#64) st.chain ∗
    optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner

/-- Discriminant byte written at `out + 8` of `Result<_, spqr::Error>`:
`0#8` encodes `Error::StateDecode`. -/
def spqrErrorTag : Error → BitVec 8
  | .stateDecode => 0#8
  | .notImplemented => 1#8
  | .msgDecode => 2#8
  | .macVerifyFailed => 3#8
  | .epochOutOfRange _ => 4#8
  | .encodingDecoding => 5#8
  | .serialization => 6#8
  | .versionMismatch => 7#8
  | .minimumVersion => 8#8
  | .keyJump _ _ => 9#8
  | .keyTrimmed _ => 10#8
  | .keyAlreadyRequested _ => 11#8
  | .erroneousDataReceived => 12#8
  | .sendKeyEpochDecreased _ _ => 13#8
  | .invalidParams _ => 14#8
  | .chainNotAvailable => 15#8

/-- Representation predicate for `Result<PqRatchetState, spqr::Error>` at `outPtr` (`352` bytes = `0x160`):
    * `Ok(st)`: `protoPqRatchetStateAt H_inner A outPtr st`
    * `Err(e)`: `(outPtr ↦₆₄ none2Cap) ∗ ((outPtr + 8#64) ↦₈ spqrErrorTag e) ∗ memRegion (outPtr + 9#64) 343`
      (`0xfffffffffffffffe` `-2` niche at `+0x00`, 1-byte `spqr::Error` discriminant at `+0x08`, `0#8` for `StateDecode`). -/
def decodeStateResultAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (outPtr : BitVec 64) :
    Except Error PqRatchetState → SepProp
  | .ok st => protoPqRatchetStateAt H_inner A outPtr st
  | .error e =>
    (outPtr ↦₆₄ none2Cap) ∗
      ((outPtr + 8#64) ↦₈ spqrErrorTag e) ∗
      memRegion (outPtr + 9#64) 343

theorem quads7At_split_head (a : BitVec 64) (q : Quads7) :
    quads7At a q =
      (a ↦₆₄ q.1) ∗
      (((a + 8#64) ↦₆₄ q.2.1) ∗ ((a + 16#64) ↦₆₄ q.2.2.1) ∗ ((a + 24#64) ↦₆₄ q.2.2.2.1) ∗
       ((a + 32#64) ↦₆₄ q.2.2.2.2.1) ∗ ((a + 40#64) ↦₆₄ q.2.2.2.2.2.1) ∗
       ((a + 48#64) ↦₆₄ q.2.2.2.2.2.2)) := by
  rcases q with ⟨w0, w1, w2, w3, w4, w5, w6⟩
  unfold quads7At
  dsimp only

theorem memRegion_48_eq_six_cells (b : BitVec 64) :
    memRegion b 48 =
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        (b ↦₆₄ w1) ∗ ((b + 8#64) ↦₆₄ w2) ∗ ((b + 16#64) ↦₆₄ w3) ∗
        ((b + 24#64) ↦₆₄ w4) ∗ ((b + 32#64) ↦₆₄ w5) ∗ ((b + 40#64) ↦₆₄ w6) := by
  rw [ProofLib.memRegion_cells b 6 (by decide)]
  simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]

theorem head_and_memRegion_48_entails_quads7 (a w0 : BitVec 64) :
    (a ↦₆₄ w0) ∗ memRegion (a + 8#64) 48 ⊢
      ∃∗ q : Quads7, ⌜q.head = w0⌝ ∗ quads7At a q := by
  rw [memRegion_48_eq_six_cells (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  refine Entails.sepExists_right (w0, w1, w2, w3, w4, w5, w6) ?_
  unfold quads7At Quads7.head
  dsimp only
  apply Entails.pure_right rfl
  exact Entails.of_eq (by ac_rfl)

theorem quads7_entails_head_and_memRegion_48 (a : BitVec 64) (q : Quads7) :
    quads7At a q ⊢ (a ↦₆₄ q.head) ∗ memRegion (a + 8#64) 48 := by
  rcases q with ⟨w0, w1, w2, w3, w4, w5, w6⟩
  rw [quads7At_split_head, memRegion_48_eq_six_cells (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  unfold Quads7.head
  dsimp only
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))))))

theorem head_and_memRegion_216_entails_quads28 (a w0 : BitVec 64) :
    (a ↦₆₄ w0) ∗ memRegion (a + 8#64) 216 ⊢
      ∃∗ q : Quads28, ⌜q.head = w0⌝ ∗ quads28At a q := by
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 168) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 56) (k := 112) (b' := a + 112#64) rfl (by bv_omega) (by decide),
      memRegion_56_eq_quads7At (a + 56#64), memRegion_112_eq_quads14At (a + 112#64)]
  rw [← sepConj_assoc ((a ↦₆₄ w0))]
  refine Entails.trans (sepConj_mono_left (head_and_memRegion_48_entails_quads7 a w0)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro q2
  apply Entails.sepExists_elim; intro q12
  apply Entails.sepExists_elim; intro q11
  refine Entails.sepExists_right ((q11, q12), q2) ?_
  unfold quads28At quads14At Quads28.head
  dsimp only
  exact Entails.of_eq (by ac_rfl)

theorem quads28_entails_head_and_memRegion_216 (a : BitVec 64) (q : Quads28) :
    quads28At a q ⊢ (a ↦₆₄ q.head) ∗ memRegion (a + 8#64) 216 := by
  rcases q with ⟨⟨q11, q12⟩, q2⟩
  unfold quads28At quads14At Quads28.head
  dsimp only
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 168) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 56) (k := 112) (b' := a + 112#64) rfl (by bv_omega) (by decide)]
  have h1 := quads7_entails_head_and_memRegion_48 a q11
  have h2 := quads7At_entails_memRegion_56 (a + 56#64) q12
  have h3 := quads14At_entails_memRegion_112 (a + 112#64) q2
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) h3) ?_
  exact Entails.of_eq (by ac_rfl)

theorem optProtoInnerStateAt_entails_quads28 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (opt : Option V1State.InnerState) :
    optProtoInnerStateAt H_inner A a opt ⊢
      ∃∗ q : Quads28, quads28At a q ∗ optProtoInnerStateHeap H_inner A q opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateAt optProtoInnerStateHeap
    dsimp only
    refine Entails.trans (head_and_memRegion_216_entails_quads28 a none2Cap) ?_
    apply Entails.sepExists_elim; intro q
    refine Entails.sepExists_right q ?_
    exact Entails.of_eq (by ac_rfl)
  | some is =>
    unfold optProtoInnerStateAt optProtoInnerStateHeap
    dsimp only
    apply Entails.sepExists_elim; intro q
    refine Entails.sepExists_right q ?_
    exact Entails.of_eq (by ac_rfl)

theorem quads28_entails_optProtoInnerStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (q : Quads28) (opt : Option V1State.InnerState) :
    quads28At a q ∗ optProtoInnerStateHeap H_inner A q opt ⊢
      optProtoInnerStateAt H_inner A a opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateAt optProtoInnerStateHeap
    dsimp only
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_left; intro hhead
    rw [← hhead]
    exact quads28_entails_head_and_memRegion_216 a q
  | some is =>
    unfold optProtoInnerStateAt optProtoInnerStateHeap
    dsimp only
    refine Entails.sepExists_right q ?_
    exact Entails.of_eq (by ac_rfl)

/-- Address-independent heap predicate for `optProtoInnerStateCapOkAt H_inner A a remLen opt`
    given its 28 inline quadwords `q`. -/
def optProtoInnerStateCapOkHeap (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (remLen : Nat) (q : Quads28) : Option V1State.InnerState → SepProp
  | none => ⌜remLen < 2 ^ 56 ∧ q.head = none2Cap⌝
  | some is =>
    ⌜OptInnerStatePolyBound remLen (some is) ∧ q.head ≠ none3Cap⌝ ∗
    ∃∗ H : SepProp,
      ⌜(∀ a' : BitVec 64, quads28At a' q ∗ H ⊢
          Prost.MessageMerge.optProtoInnerStateCapAt A a' remLen (some is)) ∧
       (H ⊢ H_inner A q is)⌝ ∗
      H

/-- `Option<V1State.InnerState>` at `a` (`224` bytes) with `OptInnerStatePolyBound remLen`
    and `Prost.MessageMerge.optProtoInnerStateCapAt` (factored via `Quads28` for 224B copies). -/
def optProtoInnerStateCapOkAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) : Option V1State.InnerState → SepProp
  | none =>
    ⌜remLen < 2 ^ 56⌝ ∗ (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 216
  | some is =>
    ∃∗ q : Quads28,
      quads28At a q ∗
      optProtoInnerStateCapOkHeap H_inner A remLen q (some is)

theorem optProtoInnerStateCapOkAt_entails_quads28 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢
      ∃∗ q : Quads28, quads28At a q ∗ optProtoInnerStateCapOkHeap H_inner A remLen q opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkAt optProtoInnerStateCapOkHeap
    dsimp only
    apply Entails.pure_left; intro hrem
    refine Entails.trans (head_and_memRegion_216_entails_quads28 a none2Cap) ?_
    apply Entails.sepExists_elim; intro q
    apply Entails.pure_left; intro hhead
    refine Entails.sepExists_right q ?_
    rw [sepConj_comm]
    exact Entails.pure_right ⟨hrem, hhead⟩ (Entails.refl _)
  | some is =>
    exact Entails.refl _

theorem quads28_entails_optProtoInnerStateCapOkAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (q : Quads28) (opt : Option V1State.InnerState) :
    quads28At a q ∗ optProtoInnerStateCapOkHeap H_inner A remLen q opt ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkAt optProtoInnerStateCapOkHeap
    dsimp only
    rw [sepConj_comm]
    apply Entails.pure_left; rintro ⟨hrem, hhead⟩
    apply Entails.pure_right hrem
    rw [← hhead]
    exact quads28_entails_head_and_memRegion_216 a q
  | some is =>
    unfold optProtoInnerStateCapOkAt
    exact Entails.sepExists_right q (Entails.refl _)

theorem optProtoInnerStateCapOkHeap_mono {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {rem1 rem2 : Nat} {q : Quads28} {opt : Option V1State.InnerState} (hle : rem2 ≤ rem1) :
    optProtoInnerStateCapOkHeap H_inner A rem1 q opt ⊢
      optProtoInnerStateCapOkHeap H_inner A rem2 q opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkHeap
    dsimp only
    rw [← sepConj_emp ⌜rem1 < 2 ^ 56 ∧ q.head = none2Cap⌝,
        ← sepConj_emp ⌜rem2 < 2 ^ 56 ∧ q.head = none2Cap⌝]
    apply Entails.pure_left; rintro ⟨hrem, hhead⟩
    exact Entails.pure_right ⟨by omega, hhead⟩ (Entails.refl _)
  | some is =>
    unfold optProtoInnerStateCapOkHeap
    dsimp only
    apply Entails.pure_left; rintro ⟨hpoly, hhead⟩
    apply Entails.sepExists_elim; intro H
    apply Entails.pure_left; rintro ⟨hcap, hH⟩
    apply Entails.pure_right ⟨optInnerStatePolyBound_mono hpoly hle, hhead⟩
    refine Entails.sepExists_right H ?_
    refine Entails.pure_right ⟨fun a' => Entails.trans (hcap a')
      (Prost.MessageMerge.optProtoInnerStateCapAt_mono A a' (some is) hle), hH⟩ (Entails.refl _)

theorem optProtoInnerStateCapOkAt_mono {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {a : BitVec 64} {rem1 rem2 : Nat} {opt : Option V1State.InnerState} (hle : rem2 ≤ rem1) :
    optProtoInnerStateCapOkAt H_inner A a rem1 opt ⊢
      optProtoInnerStateCapOkAt H_inner A a rem2 opt := by
  refine Entails.trans (optProtoInnerStateCapOkAt_entails_quads28 H_inner A a rem1 opt) ?_
  apply Entails.sepExists_elim; intro q
  refine Entails.trans (sepConj_mono_right (optProtoInnerStateCapOkHeap_mono hle)) ?_
  exact quads28_entails_optProtoInnerStateCapOkAt H_inner A a rem2 q opt

theorem optProtoInnerStateCapOkAt_entails_optProtoInnerStateAt (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢ optProtoInnerStateAt H_inner A a opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkAt optProtoInnerStateAt
    dsimp only
    apply Entails.pure_left; intro _
    exact Entails.refl _
  | some is =>
    unfold optProtoInnerStateCapOkAt optProtoInnerStateCapOkHeap optProtoInnerStateAt
    dsimp only
    apply Entails.sepExists_elim; intro q
    rw [sepConj_comm (quads28At a q), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨_, hhead⟩
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨_, hH⟩
    refine Entails.sepExists_right q ?_
    apply Entails.pure_right hhead
    rw [sepConj_comm H]
    exact sepConj_mono_right hH

theorem optProtoInnerStateCapOkAt_entails_capAt (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢
      ⌜OptInnerStatePolyBound remLen opt⌝ ∗
        Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt := by
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkAt OptInnerStatePolyBound
      Prost.MessageMerge.optProtoInnerStateCapAt
    dsimp only
    exact Entails.refl _
  | some is =>
    unfold optProtoInnerStateCapOkAt optProtoInnerStateCapOkHeap
    dsimp only
    apply Entails.sepExists_elim; intro q
    rw [sepConj_comm (quads28At a q), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hpoly, _⟩
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro H
    rw [sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hcap, _⟩
    apply Entails.pure_right hpoly
    rw [sepConj_comm H]
    exact hcap a

/-- `Option<PqRatchetState.Inner>` at `a` (`224` bytes) with `CapOk` on `some (.v1 v1)`. -/
def optProtoPqRatchetInnerCapOkAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64)
    (remLen : Nat) : Option PqRatchetState.Inner → SepProp
  | none => (a ↦₆₄ none3Cap) ∗ memRegion (a + 8#64) 216
  | some (.v1 v1) => optProtoInnerStateCapOkAt H_inner A a remLen v1.innerState

theorem optProtoPqRatchetInnerCapOkAt_mono {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {a : BitVec 64} {rem1 rem2 : Nat} {opt : Option PqRatchetState.Inner} (hle : rem2 ≤ rem1) :
    optProtoPqRatchetInnerCapOkAt H_inner A a rem1 opt ⊢
      optProtoPqRatchetInnerCapOkAt H_inner A a rem2 opt := by
  cases opt with
  | none => exact Entails.refl _
  | some inner =>
    cases inner with
    | v1 v1 => exact optProtoInnerStateCapOkAt_mono hle

theorem optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (opt : Option PqRatchetState.Inner) :
    optProtoPqRatchetInnerCapOkAt H_inner A a remLen opt ⊢
      optProtoPqRatchetInnerAt H_inner A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some inner =>
    cases inner with
    | v1 v1 => exact optProtoInnerStateCapOkAt_entails_optProtoInnerStateAt H_inner A a remLen v1.innerState

end CryptoVerification.SpqrV1.Top.DecodeState
