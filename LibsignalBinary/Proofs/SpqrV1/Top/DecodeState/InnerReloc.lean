/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Repr

/-!
# Canonical `V1InnerHeapPred` Instantiation and 224-Byte Relocation Bridge

Instantiates `V1InnerHeapPred` to `canonicalV1InnerHeap` via compositional `8 * k`-byte
relocation (`RelocQuads k F`), proving 28-quadword relocation for `V1State.InnerState` and
equating the `DecodeState`, `Drop`, and `ProtoRepr` spatial predicates for `V1State` and
`PqRatchetState`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. `quadListAt` and Conversion to `Quads7` / `Quads14` / `Quads28` -/

/-- Contiguous list of 64-bit quadwords starting at base address `a`. -/
def quadListAt (a : BitVec 64) : List (BitVec 64) → SepProp
  | [] => emp
  | w :: ws => (a ↦₆₄ w) ∗ quadListAt (a + 8#64) ws

@[simp] theorem quadListAt_nil (a : BitVec 64) : quadListAt a [] = emp := rfl

@[simp] theorem quadListAt_cons (a w : BitVec 64) (ws : List (BitVec 64)) :
    quadListAt a (w :: ws) = (a ↦₆₄ w) ∗ quadListAt (a + 8#64) ws := rfl

theorem quadListAt_append (a : BitVec 64) (ws1 ws2 : List (BitVec 64)) :
    quadListAt a (ws1 ++ ws2) =
      quadListAt a ws1 ∗ quadListAt (a + BitVec.ofNat 64 (8 * ws1.length)) ws2 := by
  induction ws1 generalizing a with
  | nil =>
    simp only [List.nil_append, quadListAt_nil, emp_sepConj, List.length_nil,
      Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  | cons w ws1 ih =>
    simp only [List.cons_append, quadListAt_cons, List.length_cons, ih (a + 8#64), sepConj_assoc]
    congr 2
    have hmul : 8 * (ws1.length + 1) = 8 + 8 * ws1.length := by omega
    rw [hmul, BitVec.ofNat_add, ← BitVec.add_assoc]

theorem exists_quads7_of_len7 (ws : List (BitVec 64)) (hlen : ws.length = 7) :
    ∃ q : Quads7, (ws.head? = some q.head) ∧ ∀ a : BitVec 64, quads7At a q = quadListAt a ws := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩
  · nomatch hlen
  · nomatch hlen
  · nomatch hlen
  · nomatch hlen
  · nomatch hlen
  · nomatch hlen
  · nomatch hlen
  · refine ⟨(w0, w1, w2, w3, w4, w5, w6), rfl, fun a => ?_⟩
    simp only [quads7At, quadListAt_cons, quadListAt_nil, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepConj_assoc]
  · nomatch hlen

theorem exists_quads14_of_len14 (ws : List (BitVec 64)) (hlen : ws.length = 14) :
    ∃ q : Quads14, (ws.head? = some q.head) ∧ ∀ a : BitVec 64, quads14At a q = quadListAt a ws := by
  have hsplit : ws = ws.take 7 ++ ws.drop 7 := (List.take_append_drop 7 ws).symm
  have hlen1 : (ws.take 7).length = 7 := by rw [List.length_take, hlen]; omega
  have hlen2 : (ws.drop 7).length = 7 := by rw [List.length_drop, hlen]
  obtain ⟨q1, hhead1, hq1⟩ := exists_quads7_of_len7 (ws.take 7) hlen1
  obtain ⟨q2, _, hq2⟩ := exists_quads7_of_len7 (ws.drop 7) hlen2
  have hhead : ws.head? = (ws.take 7).head? := by
    rcases ws with _ | ⟨w0, _⟩; · nomatch hlen
    rfl
  refine ⟨(q1, q2), hhead.trans hhead1, fun a => ?_⟩
  conv_rhs => rw [hsplit, quadListAt_append]
  rw [hlen1]
  change quads7At a q1 ∗ quads7At (a + 56#64) q2 =
    quadListAt a (ws.take 7) ∗ quadListAt (a + 56#64) (ws.drop 7)
  rw [hq1 a, hq2 (a + 56#64)]

theorem exists_quads28_of_head_tail27 (w0 : BitVec 64) (ws : List (BitVec 64))
    (hlen : ws.length = 27) :
    ∃ q : Quads28, q.head = w0 ∧
      ∀ a : BitVec 64, quads28At a q = (a ↦₆₄ w0) ∗ quadListAt (a + 8#64) ws := by
  let full := w0 :: ws
  have hfull_len : full.length = 28 := by simp [full, hlen]
  have hsplit : full = full.take 14 ++ full.drop 14 := (List.take_append_drop 14 full).symm
  have hlen1 : (full.take 14).length = 14 := by rw [List.length_take, hfull_len]; omega
  have hlen2 : (full.drop 14).length = 14 := by rw [List.length_drop, hfull_len]
  obtain ⟨q1, hhead1, hq1⟩ := exists_quads14_of_len14 (full.take 14) hlen1
  obtain ⟨q2, _, hq2⟩ := exists_quads14_of_len14 (full.drop 14) hlen2
  have hhead_full : (full.take 14).head? = some w0 := rfl
  have hq1_head : q1.head = w0 := Option.some.inj (hhead1.symm.trans hhead_full)
  refine ⟨(q1, q2), hq1_head, fun a => ?_⟩
  change quads14At a q1 ∗ quads14At (a + 112#64) q2 = quadListAt a full
  conv_rhs => rw [hsplit, quadListAt_append]
  rw [hlen1]
  change quads14At a q1 ∗ quads14At (a + 112#64) q2 =
    quadListAt a (full.take 14) ∗ quadListAt (a + 112#64) (full.drop 14)
  rw [hq1 a, hq2 (a + 112#64)]

/-! ## 2. Compositional Relocation Predicate `RelocQuads k F` -/

/-- A predicate family `F : BitVec 64 → SepProp` is relocatable of size `k` quadwords (`8 * k` bytes)
    if at any address `a`, `F a` factors into `quadListAt a ws` (`ws.length = k`) and an
    address-independent heap remainder `H` that reassembles `F a'` at any `a'`. -/
def RelocQuads (k : Nat) (F : BitVec 64 → SepProp) : Prop :=
  ∀ a : BitVec 64, F a ⊢
    ∃∗ ws : List (BitVec 64), ⌜ws.length = k⌝ ∗ quadListAt a ws ∗
      ∃∗ H : SepProp, ⌜∀ a' : BitVec 64, quadListAt a' ws ∗ H ⊢ F a'⌝ ∗ H

theorem RelocQuads.of_witness {k : Nat} {F : BitVec 64 → SepProp} {a : BitVec 64}
    (ws : List (BitVec 64)) (hlen : ws.length = k) (H : SepProp)
    (hreasm : ∀ a' : BitVec 64, quadListAt a' ws ∗ H ⊢ F a') :
    quadListAt a ws ∗ H ⊢
      ∃∗ ws : List (BitVec 64), ⌜ws.length = k⌝ ∗ quadListAt a ws ∗
        ∃∗ H : SepProp, ⌜∀ a' : BitVec 64, quadListAt a' ws ∗ H ⊢ F a'⌝ ∗ H := by
  refine Entails.sepExists_right ws (Entails.pure_right hlen (sepConj_mono_right ?_))
  exact Entails.sepExists_right H (Entails.pure_right hreasm (Entails.refl _))

theorem RelocQuads.elim {k : Nat} {F : BitVec 64 → SepProp} (hF : RelocQuads k F)
    (a : BitVec 64) {Q R : SepProp}
    (h : ∀ (ws : List (BitVec 64)), ws.length = k → ∀ (H : SepProp),
      (∀ a' : BitVec 64, quadListAt a' ws ∗ H ⊢ F a') →
      (quadListAt a ws ∗ H) ∗ Q ⊢ R) :
    F a ∗ Q ⊢ R := by
  refine Entails.trans (sepConj_mono_left (hF a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ws
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlen
  rw [← sepConj_assoc (quadListAt a ws), sepConj_comm (quadListAt a ws), sepConj_assoc]
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hreasm
  have hcomm : H ∗ (quadListAt a ws ∗ Q) = (quadListAt a ws ∗ H) ∗ Q := by ac_rfl
  rw [hcomm]
  exact h ws hlen H hreasm

theorem RelocQuads.congr {k : Nat} {F G : BitVec 64 → SepProp}
    (hF : RelocQuads k F) (heq : ∀ a, F a = G a) : RelocQuads k G := by
  intro a
  rw [← heq a, ← sepConj_emp (F a)]
  refine RelocQuads.elim hF a (fun ws hlen H hreasm => ?_)
  rw [sepConj_emp]
  exact RelocQuads.of_witness ws hlen H (fun a' => by rw [← heq a']; exact hreasm a')

theorem RelocQuads.cell64 (w : BitVec 64) :
    RelocQuads 1 (fun a => a ↦₆₄ w) := by
  intro a
  dsimp only
  have heq : (a ↦₆₄ w) = quadListAt a [w] ∗ emp := by
    rw [quadListAt_cons, quadListAt_nil, sepConj_emp, sepConj_emp]
  rw [heq]
  refine RelocQuads.of_witness [w] rfl emp (fun a' => ?_)
  rw [quadListAt_cons, quadListAt_nil, sepConj_emp, sepConj_emp]
  exact Entails.refl _

theorem RelocQuads.exists_left {α : Type} {k : Nat} {F : α → BitVec 64 → SepProp}
    (h : ∀ x : α, RelocQuads k (F x)) :
    RelocQuads k (fun a => ∃∗ x : α, F x a) := by
  intro a
  apply Entails.sepExists_elim; intro x
  rw [← sepConj_emp (F x a)]
  refine RelocQuads.elim (h x) a (fun ws hlen H hreasm => ?_)
  rw [sepConj_emp]
  exact RelocQuads.of_witness ws hlen H (fun a' =>
    Entails.trans (hreasm a') (Entails.sepExists_intro (P := fun y => F y a') x))

theorem RelocQuads.const_right {k : Nat} {F : BitVec 64 → SepProp} (P : SepProp)
    (hF : RelocQuads k F) :
    RelocQuads k (fun a => F a ∗ P) := by
  intro a
  refine RelocQuads.elim hF a (fun ws hlen H hreasm => ?_)
  rw [sepConj_assoc]
  refine RelocQuads.of_witness ws hlen (H ∗ P) (fun a' => ?_)
  rw [← sepConj_assoc]
  exact sepConj_mono_left (hreasm a')

theorem RelocQuads.const_left {k : Nat} {F : BitVec 64 → SepProp} (P : SepProp)
    (hF : RelocQuads k F) :
    RelocQuads k (fun a => P ∗ F a) :=
  RelocQuads.congr (RelocQuads.const_right P hF) (fun a => sepConj_comm (F a) P)

theorem RelocQuads.sep {k1 k2 k : Nat} {off : BitVec 64} {F G : BitVec 64 → SepProp}
    (hF : RelocQuads k1 F) (hG : RelocQuads k2 G)
    (hoff : off = BitVec.ofNat 64 (8 * k1)) (hk : k1 + k2 = k) :
    RelocQuads k (fun a => F a ∗ G (a + off)) := by
  subst hoff hk
  intro a
  refine RelocQuads.elim hF a (fun ws1 hlen1 H1 hreasm1 => ?_)
  rw [sepConj_comm]
  refine RelocQuads.elim hG (a + BitVec.ofNat 64 (8 * k1)) (fun ws2 hlen2 H2 hreasm2 => ?_)
  have hgroup :
      (quadListAt (a + BitVec.ofNat 64 (8 * k1)) ws2 ∗ H2) ∗ (quadListAt a ws1 ∗ H1) =
      quadListAt a (ws1 ++ ws2) ∗ (H1 ∗ H2) := by
    rw [quadListAt_append, hlen1]; ac_rfl
  rw [hgroup]
  refine RelocQuads.of_witness (ws1 ++ ws2) (by rw [List.length_append, hlen1, hlen2]) (H1 ∗ H2) (fun a' => ?_)
  have hgroup' :
      quadListAt a' (ws1 ++ ws2) ∗ (H1 ∗ H2) =
      (quadListAt a' ws1 ∗ H1) ∗ (quadListAt (a' + BitVec.ofNat 64 (8 * k1)) ws2 ∗ H2) := by
    rw [quadListAt_append, hlen1]; ac_rfl
  rw [hgroup']
  exact sepConj_mono (hreasm1 a') (hreasm2 (a' + BitVec.ofNat 64 (8 * k1)))

theorem RelocQuads.sep3 {k1 k2 k3 k : Nat} {off1 off2 : BitVec 64}
    {F1 F2 F3 : BitVec 64 → SepProp}
    (h1 : RelocQuads k1 F1) (h2 : RelocQuads k2 F2) (h3 : RelocQuads k3 F3)
    (hoff1 : off1 = BitVec.ofNat 64 (8 * k1))
    (hoff2 : off2 = BitVec.ofNat 64 (8 * (k1 + k2)))
    (hk : k1 + k2 + k3 = k) :
    RelocQuads k (fun a => F1 a ∗ F2 (a + off1) ∗ F3 (a + off2)) :=
  RelocQuads.congr (RelocQuads.sep (RelocQuads.sep h1 h2 hoff1 rfl) h3 hoff2 hk)
    (fun _ => sepConj_assoc _ _ _)

theorem RelocQuads.sep4 {k1 k2 k3 k4 k : Nat} {off1 off2 off3 : BitVec 64}
    {F1 F2 F3 F4 : BitVec 64 → SepProp}
    (h1 : RelocQuads k1 F1) (h2 : RelocQuads k2 F2) (h3 : RelocQuads k3 F3) (h4 : RelocQuads k4 F4)
    (hoff1 : off1 = BitVec.ofNat 64 (8 * k1))
    (hoff2 : off2 = BitVec.ofNat 64 (8 * (k1 + k2)))
    (hoff3 : off3 = BitVec.ofNat 64 (8 * (k1 + k2 + k3)))
    (hk : k1 + k2 + k3 + k4 = k) :
    RelocQuads k (fun a => F1 a ∗ F2 (a + off1) ∗ F3 (a + off2) ∗ F4 (a + off3)) :=
  RelocQuads.congr (RelocQuads.sep (RelocQuads.sep3 h1 h2 h3 hoff1 hoff2 rfl) h4 hoff3 hk)
    (fun _ => by ac_rfl)

theorem RelocQuads.sep5 {k1 k2 k3 k4 k5 k : Nat} {off1 off2 off3 off4 : BitVec 64}
    {F1 F2 F3 F4 F5 : BitVec 64 → SepProp}
    (h1 : RelocQuads k1 F1) (h2 : RelocQuads k2 F2) (h3 : RelocQuads k3 F3)
    (h4 : RelocQuads k4 F4) (h5 : RelocQuads k5 F5)
    (hoff1 : off1 = BitVec.ofNat 64 (8 * k1))
    (hoff2 : off2 = BitVec.ofNat 64 (8 * (k1 + k2)))
    (hoff3 : off3 = BitVec.ofNat 64 (8 * (k1 + k2 + k3)))
    (hoff4 : off4 = BitVec.ofNat 64 (8 * (k1 + k2 + k3 + k4)))
    (hk : k1 + k2 + k3 + k4 + k5 = k) :
    RelocQuads k (fun a => F1 a ∗ F2 (a + off1) ∗ F3 (a + off2) ∗ F4 (a + off3) ∗ F5 (a + off4)) :=
  RelocQuads.congr (RelocQuads.sep (RelocQuads.sep4 h1 h2 h3 h4 hoff1 hoff2 hoff3 rfl) h5 hoff4 hk)
    (fun _ => by ac_rfl)

theorem RelocQuads.of_memRegion8 :
    RelocQuads 1 (fun a => memRegion a 8) := by
  refine RelocQuads.congr (RelocQuads.exists_left RelocQuads.cell64) ?_
  intro a; exact (ProofLib.memRegion_eight a).symm

theorem RelocQuads.of_memRegion (k : Nat) (hbound : 8 * k ≤ 2 ^ 64) :
    RelocQuads k (fun a => memRegion a (8 * k)) := by
  induction k with
  | zero =>
    refine RelocQuads.congr (F := fun _ => emp) ?_ (fun a => (memRegion_zero a).symm)
    intro a
    have heq : (emp : SepProp) = quadListAt a [] ∗ emp := by
      rw [quadListAt_nil, emp_sepConj]
    refine Entails.trans (Entails.of_eq heq) ?_
    refine RelocQuads.of_witness [] rfl emp (fun a' => ?_)
    rw [quadListAt_nil, emp_sepConj]
    exact Entails.refl _
  | succ k ih =>
    have hstep : ∀ a : BitVec 64,
        memRegion a (8 * (k + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * k) := by
      intro a
      exact ProofLib.memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8 * k)
        (N := 8 * (k + 1)) (by omega) rfl hbound
    exact RelocQuads.congr
      (RelocQuads.sep RelocQuads.of_memRegion8 (ih (by omega)) rfl (by omega))
      (fun a => (hstep a).symm)

/-! ## 3. Relocation of `vecHeader`, `vecU8`, `vecU8Cap`, `vecVecU8`, and `Authenticator` -/

theorem RelocQuads.vecCells (cap ptr : BitVec 64) (len : Nat) :
    RelocQuads 3 (fun a =>
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 len)) :=
  RelocQuads.sep3 (off1 := 8#64) (off2 := 16#64)
    (RelocQuads.cell64 cap) (RelocQuads.cell64 ptr)
    (RelocQuads.cell64 (BitVec.ofNat 64 len)) rfl rfl rfl

theorem RelocQuads.vecHeader (cap ptr : BitVec 64) (len : Nat) :
    RelocQuads 3 (fun a => vecHeader a cap ptr len) :=
  RelocQuads.vecCells cap ptr len

theorem RelocQuads.vecU8At (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RelocQuads 3 (fun a => RustHeap.vecU8At A a cap ptr bs) :=
  RelocQuads.congr
    (RelocQuads.const_right (vecU8Buf A cap ptr bs) (RelocQuads.vecHeader cap ptr bs.length))
    (fun a => (vecU8At_eq_header_sep_buf A a cap ptr bs).symm)

theorem RelocQuads.vecU8 (A : RustAlloc) (bs : List (BitVec 8)) :
    RelocQuads 3 (fun a => RustHeap.vecU8 A a bs) :=
  RelocQuads.exists_left (fun cap => RelocQuads.exists_left (fun ptr => RelocQuads.vecU8At A cap ptr bs))

theorem RelocQuads.vecU8Cap (A : RustAlloc) (bsLen : Nat) (bs : List (BitVec 8)) :
    RelocQuads 3 (fun a => ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A a cap ptr bs) :=
  RelocQuads.exists_left (fun cap =>
    RelocQuads.exists_left (fun ptr =>
      RelocQuads.const_left ⌜BytesMergeCapOk cap bsLen⌝ (RelocQuads.vecU8At A cap ptr bs)))

theorem RelocQuads.vecVecU8PinnedAt (A : RustAlloc) (pin : VecPin) (bss : List (List (BitVec 8))) :
    RelocQuads 3 (fun a => ProtoRepr.vecVecU8PinnedAt A pin a bss) :=
  RelocQuads.congr
    (RelocQuads.const_right (ProtoRepr.vecVecU8Buf A pin.cap pin.ptr bss)
      (RelocQuads.vecCells pin.cap pin.ptr bss.length))
    (fun a => by rw [ProtoRepr.vecVecU8PinnedAt_eq_header_buf]; ac_rfl)

theorem RelocQuads.vecVecU8At (A : RustAlloc) (bss : List (List (BitVec 8))) :
    RelocQuads 3 (fun a => ProtoRepr.vecVecU8At A a bss) :=
  RelocQuads.congr
    (RelocQuads.exists_left (fun pin => RelocQuads.vecVecU8PinnedAt A pin bss))
    (fun a => (ProtoRepr.vecVecU8At_eq_exists_pin A a bss).symm)

theorem RelocQuads.authenticatorPBCapAt (A : RustAlloc) (bsLen : Nat) (auth : ProtoAuthenticator) :
    RelocQuads 6 (fun a => Auth.authenticatorPBCapAt A a bsLen auth) :=
  RelocQuads.sep (RelocQuads.vecU8Cap A bsLen auth.rootKey)
    (RelocQuads.vecU8Cap A bsLen auth.macKey) rfl rfl

theorem RelocQuads.optAuthenticatorPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option ProtoAuthenticator) :
    RelocQuads 6 (fun a => Prost.MessageMerge.optAuthenticatorPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 5 (by decide)) rfl rfl
  | some auth =>
    exact RelocQuads.authenticatorPBCapAt A bsLen auth

theorem RelocQuads.unchunked2CapAt (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) :
    RelocQuads 7 (fun a => Prost.MessageMerge.unchunked2CapAt A a bsLen epoch auth) :=
  RelocQuads.sep (RelocQuads.optAuthenticatorPBCapAt A bsLen auth)
    (RelocQuads.cell64 epoch) rfl rfl

theorem RelocQuads.optKeysUnsampledPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    RelocQuads 7 (fun a => Prost.MessageMerge.optKeysUnsampledPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap2)
      (RelocQuads.of_memRegion 6 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked2CapAt A bsLen u.epoch u.auth

theorem RelocQuads.optNoHeaderReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    RelocQuads 7 (fun a => Prost.MessageMerge.optNoHeaderReceivedPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap2)
      (RelocQuads.of_memRegion 6 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked2CapAt A bsLen u.epoch u.auth

theorem RelocQuads.optCt2SentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    RelocQuads 7 (fun a => Prost.MessageMerge.optCt2SentPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap2)
      (RelocQuads.of_memRegion 6 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked2CapAt A bsLen u.epoch u.auth

theorem RelocQuads.unchunked3CapAt (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    RelocQuads 10 (fun a => Prost.MessageMerge.unchunked3CapAt A a bsLen epoch auth v3) :=
  RelocQuads.sep3 (RelocQuads.vecU8Cap A bsLen v3)
    (RelocQuads.optAuthenticatorPBCapAt A bsLen auth)
    (RelocQuads.cell64 epoch) rfl rfl rfl

theorem RelocQuads.optHeaderReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    RelocQuads 10 (fun a => Prost.MessageMerge.optHeaderReceivedPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 9 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked3CapAt A bsLen u.epoch u.auth u.hdr

theorem RelocQuads.optEkSentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.EkSent) :
    RelocQuads 10 (fun a => Prost.MessageMerge.optEkSentPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 9 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked3CapAt A bsLen u.epoch u.auth u.dk

theorem RelocQuads.unchunked4CapAt (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    RelocQuads 13 (fun a => Prost.MessageMerge.unchunked4CapAt A a bsLen epoch auth v3 v4) :=
  RelocQuads.sep4 (RelocQuads.vecU8Cap A bsLen v3)
    (RelocQuads.vecU8Cap A bsLen v4)
    (RelocQuads.optAuthenticatorPBCapAt A bsLen auth)
    (RelocQuads.cell64 epoch) rfl rfl rfl rfl

theorem RelocQuads.optHeaderSentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.HeaderSent) :
    RelocQuads 13 (fun a => Prost.MessageMerge.optHeaderSentPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 12 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked4CapAt A bsLen u.epoch u.auth u.ek u.dk

theorem RelocQuads.unchunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (u : V1State.Unchunked.EkSentCt1Received) :
    RelocQuads 13 (fun a => Prost.MessageMerge.unchunkedEkSentCt1ReceivedPBCapAt A a bsLen u) :=
  RelocQuads.sep4 (RelocQuads.vecU8Cap A bsLen u.dk)
    (RelocQuads.vecU8Cap A bsLen u.ct1)
    (RelocQuads.optAuthenticatorPBCapAt A bsLen u.auth)
    (RelocQuads.cell64 u.epoch) rfl rfl rfl rfl

theorem RelocQuads.optUnchunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    RelocQuads 13 (fun a => Prost.MessageMerge.optUnchunkedEkSentCt1ReceivedPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 12 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunkedEkSentCt1ReceivedPBCapAt A bsLen u

theorem RelocQuads.unchunkedCt1SentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (u : V1State.Unchunked.Ct1Sent) :
    RelocQuads 16 (fun a => Prost.MessageMerge.unchunkedCt1SentPBCapAt A a bsLen u) :=
  RelocQuads.sep5 (RelocQuads.vecU8Cap A bsLen u.hdr)
    (RelocQuads.vecU8Cap A bsLen u.es)
    (RelocQuads.vecU8Cap A bsLen u.ct1)
    (RelocQuads.optAuthenticatorPBCapAt A bsLen u.auth)
    (RelocQuads.cell64 u.epoch) rfl rfl rfl rfl rfl

theorem RelocQuads.optUnchunkedCt1SentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct1Sent) :
    RelocQuads 16 (fun a => Prost.MessageMerge.optUnchunkedCt1SentPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 15 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunkedCt1SentPBCapAt A bsLen u

theorem RelocQuads.unchunked5CapAt (A : RustAlloc) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    RelocQuads 16 (fun a => Prost.MessageMerge.unchunked5CapAt A a bsLen epoch auth v3 v4 v5) :=
  RelocQuads.sep5 (RelocQuads.vecU8Cap A bsLen v3)
    (RelocQuads.vecU8Cap A bsLen v4)
    (RelocQuads.vecU8Cap A bsLen v5)
    (RelocQuads.optAuthenticatorPBCapAt A bsLen auth)
    (RelocQuads.cell64 epoch) rfl rfl rfl rfl rfl

theorem RelocQuads.optCt1SentEkReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    RelocQuads 16 (fun a => Prost.MessageMerge.optCt1SentEkReceivedPBCapAt A a bsLen opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 15 (by decide)) rfl rfl
  | some u =>
    exact RelocQuads.unchunked5CapAt A bsLen u.epoch u.auth u.es u.ek u.ct1

/-! ## 4. Relocation of `PolynomialEncoder` and `PolynomialDecoder` -/

def pack32Pair (v0 v1 : BitVec 32) : BitVec 64 :=
  pack64 (v0.extractLsb' 0 8) (v0.extractLsb' 8 8) (v0.extractLsb' 16 8) (v0.extractLsb' 24 8)
    (v1.extractLsb' 0 8) (v1.extractLsb' 8 8) (v1.extractLsb' 16 8) (v1.extractLsb' 24 8)

theorem pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (v0 v1 : BitVec 32) :
    (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1) = a ↦₆₄ pack32Pair v0 v1 := by
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  dsimp only [pack32Pair, pack64]
  rw [unpack64_pack64]
  exact (pointsToBytes_append a (unpack32 v0) (unpack32 v1)).symm

theorem RelocQuads.cell32_pair (v0 v1 : BitVec 32) :
    RelocQuads 1 (fun a => (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1)) :=
  RelocQuads.congr (RelocQuads.cell64 (pack32Pair v0 v1))
    (fun a => (pointsTo32_pair_eq_pointsTo64 a v0 v1).symm)

theorem RelocQuads.cell32_memRegion4 (v0 : BitVec 32) :
    RelocQuads 1 (fun a => (a ↦₃₂ v0) ∗ memRegion (a + 4#64) 4) := by
  refine RelocQuads.congr (RelocQuads.exists_left (fun v1 => RelocQuads.cell32_pair v0 v1)) ?_
  intro a
  rw [ProofLib.memRegion_four (a + 4#64), sepExists_sepConj_right]

def pack8_8_16_32 (b0 b1 : BitVec 8) (v2 : BitVec 16) (v4 : BitVec 32) : BitVec 64 :=
  pack64 b0 b1 (v2.extractLsb' 0 8) (v2.extractLsb' 8 8)
    (v4.extractLsb' 0 8) (v4.extractLsb' 8 8) (v4.extractLsb' 16 8) (v4.extractLsb' 24 8)

theorem pointsTo8_memRegion7_eq_exists64 (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 =
      ∃∗ v4 : BitVec 32, ∃∗ v2 : BitVec 16, ∃∗ b1 : BitVec 8,
        a ↦₆₄ pack8_8_16_32 b0 b1 v2 v4 := by
  have s1 := ProofLib.memRegion_split' (b := a + 1#64) (b' := a + 2#64) (n := 1) (k := 6) (N := 7) rfl (by bv_lin) (by decide)
  have s2 := ProofLib.memRegion_split' (b := a + 2#64) (b' := a + 4#64) (n := 2) (k := 4) (N := 6) rfl (by bv_lin) (by decide)
  rw [s1, s2, ProofLib.memRegion_one (a + 1#64), ProofLib.memRegion_two (a + 2#64),
    ProofLib.memRegion_four (a + 4#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext v4; congr 1; funext v2; congr 1; funext b1
  rw [← pointsToBytes_singleton a b0, ← pointsToBytes_singleton (a + 1#64) b1,
    pointsTo16_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  dsimp only [pack8_8_16_32, pack64]
  rw [unpack64_pack64]
  have h1 := pointsToBytes_append a [b0] ([b1] ++ (unpack16 v2 ++ unpack32 v4))
  have h2 := pointsToBytes_append (a + 1#64) [b1] (unpack16 v2 ++ unpack32 v4)
  have h3 := pointsToBytes_append (a + 2#64) (unpack16 v2) (unpack32 v4)
  dsimp only [List.length] at h1 h2 h3
  have ha2 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have ha4 : a + 2#64 + BitVec.ofNat 64 (unpack16 v2).length = a + 4#64 := by
    simp only [unpack16, List.length]; bv_lin
  rw [ha2] at h2
  rw [ha4] at h3
  have hlist : [b0] ++ ([b1] ++ (unpack16 v2 ++ unpack32 v4)) =
      [b0, b1, v2.extractLsb' 0 8, v2.extractLsb' 8 8,
       v4.extractLsb' 0 8, v4.extractLsb' 8 8, v4.extractLsb' 16 8, v4.extractLsb' 24 8] := rfl
  rw [← hlist, h1, h2, h3]

theorem RelocQuads.cell8_memRegion7 (b0 : BitVec 8) :
    RelocQuads 1 (fun a => (a ↦₈ b0) ∗ memRegion (a + 1#64) 7) := by
  refine RelocQuads.congr
    (RelocQuads.exists_left (fun v4 =>
      RelocQuads.exists_left (fun v2 =>
        RelocQuads.exists_left (fun b1 =>
          RelocQuads.cell64 (pack8_8_16_32 b0 b1 v2 v4))))) ?_
  intro a
  exact (pointsTo8_memRegion7_eq_exists64 a b0).symm

theorem RelocQuads.polynomialEncoderPBAt (A : RustAlloc) (pb : PolynomialEncoder) :
    RelocQuads 7 (fun a => ProtoRepr.polynomialEncoderPBAt A a pb) := by
  refine RelocQuads.congr
    (RelocQuads.sep3 (off1 := 24#64) (off2 := 48#64)
      (RelocQuads.vecVecU8At A pb.pts)
      (RelocQuads.vecVecU8At A pb.polys)
      (RelocQuads.cell32_memRegion4 pb.idx) rfl rfl rfl) ?_
  intro a
  dsimp only [ProtoRepr.polynomialEncoderPBAt]
  have h52 : a + 48#64 + 4#64 = a + 52#64 := by bv_lin
  rw [h52]

theorem RelocQuads.optPolynomialEncoderPBAt (A : RustAlloc) (opt : Option PolynomialEncoder) :
    RelocQuads 7 (fun a => ProtoRepr.optPolynomialEncoderPBAt A a opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 6 (by decide)) rfl rfl
  | some pb =>
    exact RelocQuads.polynomialEncoderPBAt A pb

theorem RelocQuads.polynomialDecoderPBAt (A : RustAlloc) (pb : PolynomialDecoder) :
    RelocQuads 5 (fun a => ProtoRepr.polynomialDecoderPBAt A a pb) := by
  refine RelocQuads.congr
    (RelocQuads.sep3 (off1 := 24#64) (off2 := 32#64)
      (RelocQuads.vecVecU8At A pb.pts)
      (RelocQuads.cell32_pair pb.ptsNeeded pb.polys)
      (RelocQuads.cell8_memRegion7 (ProtoRepr.boolByte pb.isComplete)) rfl rfl rfl) ?_
  intro a
  dsimp only [ProtoRepr.polynomialDecoderPBAt]
  have h28 : a + 24#64 + 4#64 = a + 28#64 := by bv_lin
  have h33 : a + 32#64 + 1#64 = a + 33#64 := by bv_lin
  rw [h28, h33]
  ac_rfl

theorem RelocQuads.optPolynomialDecoderPBAt (A : RustAlloc) (opt : Option PolynomialDecoder) :
    RelocQuads 5 (fun a => ProtoRepr.optPolynomialDecoderPBAt A a opt) := by
  cases opt with
  | none =>
    exact RelocQuads.sep (RelocQuads.cell64 noneCap)
      (RelocQuads.of_memRegion 4 (by decide)) rfl rfl
  | some pb =>
    exact RelocQuads.polynomialDecoderPBAt A pb

/-! ## 5. Relocation of `V1State.Chunked.*` and `V1State.InnerState` -/

theorem RelocQuads.chunkedKeysUnsampledPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.KeysUnsampled) :
    RelocQuads 7 (fun a => Prost.MessageMerge.chunkedKeysUnsampledPBCapAt A a bsLen s) :=
  RelocQuads.optKeysUnsampledPBCapAt A bsLen s.uc

theorem RelocQuads.chunkedKeysSampledPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.KeysSampled) :
    RelocQuads 20 (fun a => Prost.MessageMerge.chunkedKeysSampledPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 104#64)
    (RelocQuads.optHeaderSentPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialEncoderPBAt A s.sendingHdr) rfl rfl

theorem RelocQuads.chunkedHeaderSentPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.HeaderSent) :
    RelocQuads 22 (fun a => Prost.MessageMerge.chunkedHeaderSentPBCapAt A a bsLen s) :=
  RelocQuads.sep3 (off1 := 80#64) (off2 := 136#64)
    (RelocQuads.optEkSentPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialEncoderPBAt A s.sendingEk)
    (RelocQuads.optPolynomialDecoderPBAt A s.receivingCt1) rfl rfl rfl

theorem RelocQuads.chunkedCt1ReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Received) :
    RelocQuads 20 (fun a => Prost.MessageMerge.chunkedCt1ReceivedPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 104#64)
    (RelocQuads.optUnchunkedEkSentCt1ReceivedPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialEncoderPBAt A s.sendingEk) rfl rfl

theorem RelocQuads.chunkedEkSentCt1ReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.EkSentCt1Received) :
    RelocQuads 18 (fun a => Prost.MessageMerge.chunkedEkSentCt1ReceivedPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 104#64)
    (RelocQuads.optUnchunkedEkSentCt1ReceivedPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialDecoderPBAt A s.receivingCt2) rfl rfl

theorem RelocQuads.chunkedNoHeaderReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.NoHeaderReceived) :
    RelocQuads 12 (fun a => Prost.MessageMerge.chunkedNoHeaderReceivedPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 40#64)
    (RelocQuads.optPolynomialDecoderPBAt A s.receivingHdr)
    (RelocQuads.optNoHeaderReceivedPBCapAt A bsLen s.uc) rfl rfl

theorem RelocQuads.chunkedHeaderReceivedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.HeaderReceived) :
    RelocQuads 15 (fun a => Prost.MessageMerge.chunkedHeaderReceivedPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 80#64)
    (RelocQuads.optHeaderReceivedPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialDecoderPBAt A s.receivingEk) rfl rfl

theorem RelocQuads.chunkedEkReceivedCt1SampledPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.EkReceivedCt1Sampled) :
    RelocQuads 23 (fun a => Prost.MessageMerge.chunkedEkReceivedCt1SampledPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 128#64)
    (RelocQuads.optCt1SentEkReceivedPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialEncoderPBAt A s.sendingCt1) rfl rfl

theorem RelocQuads.chunkedCt1AcknowledgedPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Acknowledged) :
    RelocQuads 21 (fun a => Prost.MessageMerge.chunkedCt1AcknowledgedPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 128#64)
    (RelocQuads.optUnchunkedCt1SentPBCapAt A bsLen s.uc)
    (RelocQuads.optPolynomialDecoderPBAt A s.receivingEk) rfl rfl

theorem RelocQuads.chunkedCt2SampledPBCapAt (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct2Sampled) :
    RelocQuads 14 (fun a => Prost.MessageMerge.chunkedCt2SampledPBCapAt A a bsLen s) :=
  RelocQuads.sep (off := 56#64)
    (RelocQuads.optPolynomialEncoderPBAt A s.sendingCt2)
    (RelocQuads.optCt2SentPBCapAt A bsLen s.uc) rfl rfl

/-- Canonical instantiation of `V1InnerHeapPred`: the location-independent heap
    ownership `H` of a 224-byte `V1State.InnerState` whose 28 inline quadwords are `q`,
    characterized by its ability to reassemble `Drop.protoInnerStateAt A a' is` at any
    target address `a'`. -/
def canonicalV1InnerHeap : V1InnerHeapPred :=
  fun A q is =>
    ∃∗ H : SepProp,
      ⌜∀ a' : BitVec 64,
        quads28At a' q ∗ H ⊢ CryptoVerification.SpqrV1.Drop.protoInnerStateAt A a' is⌝ ∗ H

theorem reloc28_of_tagged {A : RustAlloc} {is : V1State.InnerState} {remLen : Nat}
    {tag : BitVec 64} {F : BitVec 64 → SepProp}
    (htag : tag ≠ none3Cap)
    (hF : RelocQuads 27 F)
    (heq : ∀ a : BitVec 64,
      (a ↦₆₄ tag) ∗ F (a + 8#64) ⊢
        Prost.MessageMerge.optProtoInnerStateCapAt A a remLen (some is)) :
    ∀ a : BitVec 64,
      (a ↦₆₄ tag) ∗ F (a + 8#64) ⊢
        ∃∗ q : Quads28, ⌜q.head ≠ none3Cap⌝ ∗ quads28At a q ∗
          ∃∗ H : SepProp,
            ⌜(∀ a' : BitVec 64, quads28At a' q ∗ H ⊢
                Prost.MessageMerge.optProtoInnerStateCapAt A a' remLen (some is)) ∧
             (H ⊢ canonicalV1InnerHeap A q is)⌝ ∗
            H := by
  intro a
  rw [sepConj_comm (a ↦₆₄ tag)]
  refine RelocQuads.elim hF (a + 8#64) (fun ws hlen H hreasm => ?_)
  obtain ⟨q, hq_head, hq_at⟩ := exists_quads28_of_head_tail27 tag ws hlen
  refine Entails.sepExists_right q ?_
  refine Entails.pure_right (by rw [hq_head]; exact htag) ?_
  have hgroup :
      (quadListAt (a + 8#64) ws ∗ H) ∗ (a ↦₆₄ tag) =
      quads28At a q ∗ H := by
    rw [hq_at a]; ac_rfl
  rw [hgroup]
  refine sepConj_mono_right ?_
  have hcap_reasm : ∀ a' : BitVec 64,
      quads28At a' q ∗ H ⊢ Prost.MessageMerge.optProtoInnerStateCapAt A a' remLen (some is) := by
    intro a'
    rw [hq_at a', sepConj_assoc]
    exact Entails.trans (sepConj_mono_right (hreasm (a' + 8#64))) (heq a')
  have hH_canon : H ⊢ canonicalV1InnerHeap A q is := by
    unfold canonicalV1InnerHeap
    refine Entails.sepExists_right H ?_
    refine Entails.pure_right (fun a' => ?_) (Entails.refl _)
    exact Entails.trans (hcap_reasm a') (protoInnerStateCapAt_entails_pb A a' remLen is)
  refine Entails.sepExists_right H ?_
  exact Entails.pure_right ⟨hcap_reasm, hH_canon⟩ (Entails.refl _)

theorem vecU8At_cap_ne_none3Cap {A : RustAlloc} {a cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {P Q : SepProp}
    (h : cap ≠ none3Cap → RustHeap.vecU8At A a cap ptr bs ∗ P ⊢ Q) :
    RustHeap.vecU8At A a cap ptr bs ∗ P ⊢ Q := by
  have h1 : RustHeap.vecU8At A a cap ptr bs ∗ P =
      ⌜ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
        (vecHeader a cap ptr (BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
             (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1) ∗ P) := by
    rw [vecU8At_eq_header_sep_buf]; dsimp only [vecU8Buf]; ac_rfl
  rw [h1]
  apply Entails.pure_left
  rintro ⟨hpne, hle, hlt⟩
  have hne : cap ≠ none3Cap := by
    intro heq; subst heq; revert hlt; decide
  refine Entails.trans ?_ (h hne)
  rw [h1]
  exact Entails.pure_right ⟨hpne, hle, hlt⟩ (Entails.refl _)

def ct1SampledSomeBody (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (cap ptr : BitVec 64) (b : BitVec 64) : SepProp :=
  (((b ↦₆₄ ptr) ∗ ((b + 8#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
    (⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8Buf A cap ptr u.hdr)) ∗
  (((∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (b + 16#64) cap ptr u.es) ∗
    (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (b + 40#64) cap ptr u.ct1) ∗
    Prost.MessageMerge.optAuthenticatorPBCapAt A (b + 64#64) bsLen u.auth ∗
    ((b + 112#64) ↦₆₄ u.epoch)) ∗
   ProtoRepr.optPolynomialEncoderPBAt A (b + 120#64) s.sendingCt1 ∗
   ProtoRepr.optPolynomialDecoderPBAt A (b + 176#64) s.receivingEk)

theorem RelocQuads.ct1SampledSomeBody (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (cap ptr : BitVec 64) :
    RelocQuads 27 (ct1SampledSomeBody A bsLen s u cap ptr) := by
  have h2 : RelocQuads 2 (fun b =>
      ((b ↦₆₄ ptr) ∗ ((b + 8#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length)) ∗
        (⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8Buf A cap ptr u.hdr)) :=
    RelocQuads.const_right _
      (RelocQuads.sep (off := 8#64) (RelocQuads.cell64 ptr)
        (RelocQuads.cell64 (BitVec.ofNat 64 u.hdr.length)) rfl rfl)
  have h13 : RelocQuads 13 (fun b =>
      (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A b cap ptr u.es) ∗
      (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (b + 24#64) cap ptr u.ct1) ∗
      Prost.MessageMerge.optAuthenticatorPBCapAt A (b + 48#64) bsLen u.auth ∗
      ((b + 96#64) ↦₆₄ u.epoch)) :=
    RelocQuads.sep4 (off1 := 24#64) (off2 := 48#64) (off3 := 96#64)
      (RelocQuads.vecU8Cap A bsLen u.es)
      (RelocQuads.vecU8Cap A bsLen u.ct1)
      (RelocQuads.optAuthenticatorPBCapAt A bsLen u.auth)
      (RelocQuads.cell64 u.epoch) rfl rfl rfl rfl
  have h25 : RelocQuads 25 (fun b =>
      ((∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A b cap ptr u.es) ∗
       (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (b + 24#64) cap ptr u.ct1) ∗
       Prost.MessageMerge.optAuthenticatorPBCapAt A (b + 48#64) bsLen u.auth ∗
       ((b + 96#64) ↦₆₄ u.epoch)) ∗
      ProtoRepr.optPolynomialEncoderPBAt A (b + 104#64) s.sendingCt1 ∗
      ProtoRepr.optPolynomialDecoderPBAt A (b + 160#64) s.receivingEk) :=
    RelocQuads.sep3 (off1 := 104#64) (off2 := 160#64)
      h13
      (RelocQuads.optPolynomialEncoderPBAt A s.sendingCt1)
      (RelocQuads.optPolynomialDecoderPBAt A s.receivingEk) rfl rfl rfl
  refine RelocQuads.congr (RelocQuads.sep (off := 16#64) h2 h25 rfl rfl) ?_
  intro b
  dsimp only [DecodeState.ct1SampledSomeBody]
  have h40 : b + 16#64 + 24#64 = b + 40#64 := by bv_lin
  have h64 : b + 16#64 + 48#64 = b + 64#64 := by bv_lin
  have h112 : b + 16#64 + 96#64 = b + 112#64 := by bv_lin
  have h120 : b + 16#64 + 104#64 = b + 120#64 := by bv_lin
  have h176 : b + 16#64 + 160#64 = b + 176#64 := by bv_lin
  rw [h40, h64, h112, h120, h176]

theorem ct1SampledSome_eq (A : RustAlloc) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (cap ptr a' : BitVec 64) :
    (⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A a' cap ptr u.hdr) ∗
      ((∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a' + 0x18#64) cap ptr u.es) ∗
       (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a' + 0x30#64) cap ptr u.ct1) ∗
       Prost.MessageMerge.optAuthenticatorPBCapAt A (a' + 0x48#64) bsLen u.auth ∗
       ((a' + 0x78#64) ↦₆₄ u.epoch)) ∗
      ProtoRepr.optPolynomialEncoderPBAt A (a' + 128#64) s.sendingCt1 ∗
      ProtoRepr.optPolynomialDecoderPBAt A (a' + 184#64) s.receivingEk =
    (a' ↦₆₄ cap) ∗ ct1SampledSomeBody A bsLen s u cap ptr (a' + 8#64) := by
  rw [vecU8At_eq_header_sep_buf A a' cap ptr u.hdr]
  dsimp only [vecHeader, ct1SampledSomeBody]
  have h16 : a' + 8#64 + 8#64 = a' + 16#64 := by bv_lin
  have h24 : a' + 8#64 + 16#64 = a' + 0x18#64 := by bv_lin
  have h48 : a' + 8#64 + 40#64 = a' + 0x30#64 := by bv_lin
  have h72 : a' + 8#64 + 64#64 = a' + 0x48#64 := by bv_lin
  have h120 : a' + 8#64 + 112#64 = a' + 0x78#64 := by bv_lin
  have h128 : a' + 8#64 + 120#64 = a' + 128#64 := by bv_lin
  have h184 : a' + 8#64 + 176#64 = a' + 184#64 := by bv_lin
  rw [h16, h24, h48, h72, h120, h128, h184]
  ac_rfl

theorem of_cap_inner_ct1Sampled (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (s : V1State.Chunked.Ct1Sampled) :
    Prost.MessageMerge.chunkedCt1SampledPBCapAt A a bsLen s ⊢
      ∃∗ q : Quads28, ⌜q.head ≠ none3Cap⌝ ∗ quads28At a q ∗
        ∃∗ H : SepProp,
          ⌜(∀ a' : BitVec 64, quads28At a' q ∗ H ⊢
              Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ct1Sampled s))) ∧
           (H ⊢ canonicalV1InnerHeap A q (.ct1Sampled s))⌝ ∗
          H := by
  rcases huc : s.uc with _ | u
  · have hbody : RelocQuads 27 (fun b =>
        memRegion b 120 ∗
          ProtoRepr.optPolynomialEncoderPBAt A (b + 120#64) s.sendingCt1 ∗
          ProtoRepr.optPolynomialDecoderPBAt A (b + 176#64) s.receivingEk) :=
      RelocQuads.sep3 (off1 := 120#64) (off2 := 176#64)
        (RelocQuads.of_memRegion 15 (by decide))
        (RelocQuads.optPolynomialEncoderPBAt A s.sendingCt1)
        (RelocQuads.optPolynomialDecoderPBAt A s.receivingEk) rfl rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.chunkedCt1SampledPBCapAt A a' bsLen s =
          (a' ↦₆₄ noneCap) ∗
            (memRegion (a' + 8#64) 120 ∗
              ProtoRepr.optPolynomialEncoderPBAt A ((a' + 8#64) + 120#64) s.sendingCt1 ∗
              ProtoRepr.optPolynomialDecoderPBAt A ((a' + 8#64) + 176#64) s.receivingEk) := by
      intro a'
      dsimp only [Prost.MessageMerge.chunkedCt1SampledPBCapAt]
      rw [huc]
      dsimp only [Prost.MessageMerge.optUnchunkedCt1SentPBCapAt]
      have h128 : a' + 8#64 + 120#64 = a' + 128#64 := by bv_lin
      have h184 : a' + 8#64 + 176#64 = a' + 184#64 := by bv_lin
      rw [h128, h184]
      ac_rfl
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']
    exact Entails.refl _
  · dsimp only [Prost.MessageMerge.chunkedCt1SampledPBCapAt]
    rw [huc]
    dsimp only [Prost.MessageMerge.optUnchunkedCt1SentPBCapAt,
      Prost.MessageMerge.unchunkedCt1SentPBCapAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ptr
    have hfront :
        ((⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A a cap ptr u.hdr) ∗
          ((∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a + 0x18#64) cap ptr u.es) ∗
           (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
           Prost.MessageMerge.optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
           ((a + 0x78#64) ↦₆₄ u.epoch))) ∗
          ProtoRepr.optPolynomialEncoderPBAt A (a + 128#64) s.sendingCt1 ∗
          ProtoRepr.optPolynomialDecoderPBAt A (a + 184#64) s.receivingEk =
        RustHeap.vecU8At A a cap ptr u.hdr ∗
          (⌜BytesMergeCapOk cap bsLen⌝ ∗
            ((∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a + 0x18#64) cap ptr u.es) ∗
             (∃∗ cap, ∃∗ ptr, ⌜BytesMergeCapOk cap bsLen⌝ ∗ RustHeap.vecU8At A (a + 0x30#64) cap ptr u.ct1) ∗
             Prost.MessageMerge.optAuthenticatorPBCapAt A (a + 0x48#64) bsLen u.auth ∗
             ((a + 0x78#64) ↦₆₄ u.epoch)) ∗
            ProtoRepr.optPolynomialEncoderPBAt A (a + 128#64) s.sendingCt1 ∗
            ProtoRepr.optPolynomialDecoderPBAt A (a + 184#64) s.receivingEk) := by ac_rfl
    rw [hfront]
    refine vecU8At_cap_ne_none3Cap (fun hne => ?_)
    rw [← sepConj_assoc (RustHeap.vecU8At A a cap ptr u.hdr),
        sepConj_comm (RustHeap.vecU8At A a cap ptr u.hdr) ⌜BytesMergeCapOk cap bsLen⌝,
        ct1SampledSome_eq A bsLen s u cap ptr a]
    refine reloc28_of_tagged hne (RelocQuads.ct1SampledSomeBody A bsLen s u cap ptr) (fun a' => ?_) a
    rw [← ct1SampledSome_eq A bsLen s u cap ptr a']
    change _ ⊢ Prost.MessageMerge.chunkedCt1SampledPBCapAt A a' bsLen s
    dsimp only [Prost.MessageMerge.chunkedCt1SampledPBCapAt]
    rw [huc]
    dsimp only [Prost.MessageMerge.optUnchunkedCt1SentPBCapAt,
      Prost.MessageMerge.unchunkedCt1SentPBCapAt]
    rw [← sepConj_assoc]
    refine sepConj_mono_left (sepConj_mono_left ?_)
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem of_cap_inner_canonical (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (is : V1State.InnerState) :
    Prost.MessageMerge.optProtoInnerStateCapAt A a bsLen (some is) ⊢
      ∃∗ q : Quads28, ⌜q.head ≠ none3Cap⌝ ∗ quads28At a q ∗
        ∃∗ H : SepProp,
          ⌜(∀ a' : BitVec 64, quads28At a' q ∗ H ⊢
              Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some is)) ∧
           (H ⊢ canonicalV1InnerHeap A q is)⌝ ∗
          H := by
  cases is with
  | keysUnsampled s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedKeysUnsampledPBCapAt A b bsLen s ∗
          memRegion (b + 56#64) 160) :=
      RelocQuads.sep (off := 56#64)
        (RelocQuads.chunkedKeysUnsampledPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 20 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.keysUnsampled s)) =
          (a' ↦₆₄ 0x8000000000000000#64) ∗
            (Prost.MessageMerge.chunkedKeysUnsampledPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 56#64) 160) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h64 : a' + 8#64 + 56#64 = a' + 64#64 := by bv_lin
      rw [h64]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | keysSampled s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedKeysSampledPBCapAt A b bsLen s ∗
          memRegion (b + 160#64) 56) :=
      RelocQuads.sep (off := 160#64)
        (RelocQuads.chunkedKeysSampledPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 7 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.keysSampled s)) =
          (a' ↦₆₄ 0x8000000000000001#64) ∗
            (Prost.MessageMerge.chunkedKeysSampledPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 160#64) 56) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h168 : a' + 8#64 + 160#64 = a' + 168#64 := by bv_lin
      rw [h168]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | headerSent s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedHeaderSentPBCapAt A b bsLen s ∗
          memRegion (b + 176#64) 40) :=
      RelocQuads.sep (off := 176#64)
        (RelocQuads.chunkedHeaderSentPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 5 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.headerSent s)) =
          (a' ↦₆₄ 0x8000000000000002#64) ∗
            (Prost.MessageMerge.chunkedHeaderSentPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 176#64) 40) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h184 : a' + 8#64 + 176#64 = a' + 184#64 := by bv_lin
      rw [h184]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | ct1Received s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedCt1ReceivedPBCapAt A b bsLen s ∗
          memRegion (b + 160#64) 56) :=
      RelocQuads.sep (off := 160#64)
        (RelocQuads.chunkedCt1ReceivedPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 7 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ct1Received s)) =
          (a' ↦₆₄ 0x8000000000000003#64) ∗
            (Prost.MessageMerge.chunkedCt1ReceivedPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 160#64) 56) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h168 : a' + 8#64 + 160#64 = a' + 168#64 := by bv_lin
      rw [h168]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | ekSentCt1Received s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedEkSentCt1ReceivedPBCapAt A b bsLen s ∗
          memRegion (b + 144#64) 72) :=
      RelocQuads.sep (off := 144#64)
        (RelocQuads.chunkedEkSentCt1ReceivedPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 9 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ekSentCt1Received s)) =
          (a' ↦₆₄ 0x8000000000000004#64) ∗
            (Prost.MessageMerge.chunkedEkSentCt1ReceivedPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 144#64) 72) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h152 : a' + 8#64 + 144#64 = a' + 152#64 := by bv_lin
      rw [h152]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | noHeaderReceived s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedNoHeaderReceivedPBCapAt A b bsLen s ∗
          memRegion (b + 96#64) 120) :=
      RelocQuads.sep (off := 96#64)
        (RelocQuads.chunkedNoHeaderReceivedPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 15 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.noHeaderReceived s)) =
          (a' ↦₆₄ 0x8000000000000005#64) ∗
            (Prost.MessageMerge.chunkedNoHeaderReceivedPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 96#64) 120) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h104 : a' + 8#64 + 96#64 = a' + 104#64 := by bv_lin
      rw [h104]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | headerReceived s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedHeaderReceivedPBCapAt A b bsLen s ∗
          memRegion (b + 120#64) 96) :=
      RelocQuads.sep (off := 120#64)
        (RelocQuads.chunkedHeaderReceivedPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 12 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.headerReceived s)) =
          (a' ↦₆₄ 0x8000000000000006#64) ∗
            (Prost.MessageMerge.chunkedHeaderReceivedPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 120#64) 96) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h128 : a' + 8#64 + 120#64 = a' + 128#64 := by bv_lin
      rw [h128]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | ct1Sampled s =>
    exact of_cap_inner_ct1Sampled A a bsLen s
  | ekReceivedCt1Sampled s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedEkReceivedCt1SampledPBCapAt A b bsLen s ∗
          memRegion (b + 184#64) 32) :=
      RelocQuads.sep (off := 184#64)
        (RelocQuads.chunkedEkReceivedCt1SampledPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 4 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ekReceivedCt1Sampled s)) =
          (a' ↦₆₄ 0x8000000000000008#64) ∗
            (Prost.MessageMerge.chunkedEkReceivedCt1SampledPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 184#64) 32) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h192 : a' + 8#64 + 184#64 = a' + 192#64 := by bv_lin
      rw [h192]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | ct1Acknowledged s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedCt1AcknowledgedPBCapAt A b bsLen s ∗
          memRegion (b + 168#64) 48) :=
      RelocQuads.sep (off := 168#64)
        (RelocQuads.chunkedCt1AcknowledgedPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 6 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ct1Acknowledged s)) =
          (a' ↦₆₄ 0x8000000000000009#64) ∗
            (Prost.MessageMerge.chunkedCt1AcknowledgedPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 168#64) 48) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h176 : a' + 8#64 + 168#64 = a' + 176#64 := by bv_lin
      rw [h176]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _
  | ct2Sampled s =>
    have hbody : RelocQuads 27 (fun b =>
        Prost.MessageMerge.chunkedCt2SampledPBCapAt A b bsLen s ∗
          memRegion (b + 112#64) 104) :=
      RelocQuads.sep (off := 112#64)
        (RelocQuads.chunkedCt2SampledPBCapAt A bsLen s)
        (RelocQuads.of_memRegion 13 (by decide)) rfl rfl
    have hshape : ∀ a' : BitVec 64,
        Prost.MessageMerge.optProtoInnerStateCapAt A a' bsLen (some (.ct2Sampled s)) =
          (a' ↦₆₄ 0x800000000000000a#64) ∗
            (Prost.MessageMerge.chunkedCt2SampledPBCapAt A (a' + 8#64) bsLen s ∗
              memRegion ((a' + 8#64) + 112#64) 104) := by
      intro a'; dsimp only [Prost.MessageMerge.optProtoInnerStateCapAt, Prost.MessageMerge.protoInnerStateCapAt]
      have h120 : a' + 8#64 + 112#64 = a' + 120#64 := by bv_lin
      rw [h120]
    rw [hshape a]
    refine reloc28_of_tagged (by decide) hbody (fun a' => ?_) a
    rw [← hshape a']; exact Entails.refl _

end CryptoVerification.SpqrV1.Top.DecodeState

