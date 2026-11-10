/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4: Relocation Combinators & Partial `memcpy`

**Checked by Lean.**

Address-independent relocation combinators (`relocatedHeap`, `Relocatable`), the partial-relocation
`call_memcpy_keep_relocate` helper keeping `F src` (`k` bytes) in place while relocating `G (src + off)`
(`m` bytes) to `dst + off` across `memcpy(dst, src, k + m)`, and word-tuple / `PolyEncoder` /
`PolyDecoder` `Relocatable` instances for Arms 2, 4, 5, 6, and 9.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

@[local arm64_norm, local wp_norm]
theorem bv_sub_sub_lit' (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem bv_add_add_lit' (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Address-Independent Relocation Combinators (`relocatedHeap`, `Relocatable`) -/

/-- Address-independent heap resource for relocating a `SepProp` family `F : BitVec 64 → SepProp`
    along with its inline byte slice `bs`. -/
def relocatedHeap (F : BitVec 64 → SepProp) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ P : SepProp, ⌜∀ dst : BitVec 64, (dst ↦ₛ bs) ∗ P ⊢ F dst⌝ ∗ P

theorem relocatedHeap_intro {F : BitVec 64 → SepProp} {bs : List (BitVec 8)} (P : SepProp)
    (h : ∀ dst : BitVec 64, (dst ↦ₛ bs) ∗ P ⊢ F dst) :
    P ⊢ relocatedHeap F bs :=
  Entails.sepExists_right P (Entails.pure_right h (Entails.refl P))

theorem relocatedHeap_recompose (F : BitVec 64 → SepProp) (bs : List (BitVec 8)) (dst : BitVec 64) :
    (dst ↦ₛ bs) ∗ relocatedHeap F bs ⊢ F dst := by
  unfold relocatedHeap
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro h
  exact h dst

/-- `Relocatable n F` means that for any `src`, `F src` decomposes into an `n`-byte slice
    `(src ↦ₛ bs)` (`bs.length = n`) and `relocatedHeap F bs`. -/
def Relocatable (n : Nat) (F : BitVec 64 → SepProp) : Prop :=
  ∀ src : BitVec 64,
    F src ⊢ ∃∗ bs : List (BitVec 8),
      ⌜bs.length = n⌝ ∗ (src ↦ₛ bs) ∗ relocatedHeap F bs

theorem Relocatable.congr {n m : Nat} {F G : BitVec 64 → SepProp}
    (hnm : n = m) (hFG : ∀ a, F a = G a) (hF : Relocatable n F) : Relocatable m G := by
  subst hnm
  have heq : F = G := funext hFG
  exact heq ▸ hF

theorem Relocatable.pointsTo64 (w : BitVec 64) : Relocatable 8 (fun a => a ↦₆₄ w) := by
  intro src; dsimp only
  refine Entails.sepExists_right (unpack64 w) ?_
  refine Entails.pure_right (unpack64_length w) ?_
  rw [pointsTo64_eq_pointsToBytes src w]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ unpack64 w)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsTo64_eq_pointsToBytes dst w]
  exact Entails.refl _

theorem Relocatable.pointsTo32 (w : BitVec 32) : Relocatable 4 (fun a => a ↦₃₂ w) := by
  intro src; dsimp only
  refine Entails.sepExists_right (unpack32 w) ?_
  refine Entails.pure_right (unpack32_length w) ?_
  rw [pointsTo32_eq_pointsToBytes src w]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ unpack32 w)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsTo32_eq_pointsToBytes dst w]
  exact Entails.refl _

theorem Relocatable.pointsTo8 (b : BitVec 8) : Relocatable 1 (fun a => a ↦₈ b) := by
  intro src; dsimp only
  refine Entails.sepExists_right [b] ?_
  refine Entails.pure_right rfl ?_
  rw [← pointsToBytes_singleton src b]
  conv_lhs => rw [← sepConj_emp (src ↦ₛ [b])]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, pointsToBytes_singleton dst b]
  exact Entails.refl _

theorem Relocatable.of_memRegion (n : Nat) (hn : n ≤ 2 ^ 64 := by decide) :
    Relocatable n (fun a => memRegion a n) := by
  intro src; dsimp only
  rw [memRegion_eq_exists_bytes src n hn]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs ?_
  refine Entails.pure_right hlen ?_
  conv_lhs => rw [← sepConj_emp (src ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro emp fun dst => ?_)
  rw [sepConj_emp, ← hlen]
  exact pointsToBytes_entails_memRegion dst bs

theorem Relocatable.pure_left {n : Nat} (P : Prop) {F : BitVec 64 → SepProp}
    (hF : P → Relocatable n F) : Relocatable n (fun a => ⌜P⌝ ∗ F a) := by
  intro src; dsimp only
  apply Entails.pure_left; intro hP
  refine Entails.trans (hF hP src) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap F bs) fun dst => ?_)
  exact Entails.pure_right hP (relocatedHeap_recompose F bs dst)

theorem Relocatable.sepConj {n k m : Nat} {off : BitVec 64} {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 n) (hm : n + k = m)
    (hF : Relocatable n F) (hG : Relocatable k G) :
    Relocatable m (fun a => F a ∗ G (a + off)) := by
  intro src; dsimp only
  refine Entails.trans (sepConj_mono (hF src) (hG (src + off))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepConj_assoc (⌜bs1.length = n⌝)]
  apply Entails.pure_left; intro hlen1
  rw [sepConj_left_comm ((src ↦ₛ bs1) ∗ relocatedHeap F bs1)]
  apply Entails.pure_left; intro hlen2
  refine Entails.sepExists_right (bs1 ++ bs2) ?_
  have hlen12 : (bs1 ++ bs2).length = m := by rw [List.length_append, hlen1, hlen2, hm]
  refine Entails.pure_right hlen12 ?_
  have hsplit_src : (src ↦ₛ (bs1 ++ bs2)) = (src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append src bs1 bs2, hlen1, ← hoff]
  have hreord :
      ((src ↦ₛ bs1) ∗ relocatedHeap F bs1) ∗ ((src + off) ↦ₛ bs2) ∗ relocatedHeap G bs2 =
        ((src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2)) ∗ (relocatedHeap F bs1 ∗ relocatedHeap G bs2) := by ac_rfl
  rw [hreord, ← hsplit_src]
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap F bs1 ∗ relocatedHeap G bs2) fun dst => ?_)
  have hsplit_dst : (dst ↦ₛ (bs1 ++ bs2)) = (dst ↦ₛ bs1) ∗ ((dst + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append dst bs1 bs2, hlen1, ← hoff]
  have hreord_dst :
      ((dst ↦ₛ bs1) ∗ ((dst + off) ↦ₛ bs2)) ∗ (relocatedHeap F bs1 ∗ relocatedHeap G bs2) =
        ((dst ↦ₛ bs1) ∗ relocatedHeap F bs1) ∗ (((dst + off) ↦ₛ bs2) ∗ relocatedHeap G bs2) := by ac_rfl
  rw [hsplit_dst, hreord_dst]
  exact sepConj_mono (relocatedHeap_recompose F bs1 dst) (relocatedHeap_recompose G bs2 (dst + off))

theorem Relocatable.vecOf {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (xs : List α) :
    Relocatable 24 (fun a => vecOf A stride align elem a xs) := by
  intro src
  dsimp only [RustHeap.vecOf, RustHeap.vecAt, RustHeap.vecHeader]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  have hhdr : Relocatable 24 (fun a =>
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length)) := by
    have h23 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
      (Relocatable.pointsTo64 ptr) (Relocatable.pointsTo64 (BitVec.ofNat 64 xs.length))
    have h123 := Relocatable.sepConj (off := 8#64) (m := 24) rfl rfl
      (Relocatable.pointsTo64 cap) h23
    refine Relocatable.congr rfl (fun a => ?_) h123
    rw [BitVec.add_assoc a 8#64 8#64]
    rfl
  let Rest := vecBuf A stride align elem cap ptr xs
  refine Entails.trans (sepConj_mono_left (hhdr src)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_assoc (⌜bs.length = 24⌝)]
  apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  rw [sepConj_assoc (src ↦ₛ bs)]
  refine sepConj_mono_right (relocatedHeap_intro (relocatedHeap _ bs ∗ Rest) fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [← sepConj_assoc (dst ↦ₛ bs)]
  exact sepConj_mono_left (relocatedHeap_recompose _ bs dst)

theorem Relocatable.arrayAt {α : Type} {stride : Nat} {elem : α → BitVec 64 → SepProp}
    (h : ∀ x : α, Relocatable stride (fun a => elem x a))
    (xs : List α) (m : Nat) (hm : stride * xs.length = m) :
    Relocatable m (fun a => RustHeap.arrayAt elem stride a xs) := by
  induction xs generalizing m with
  | nil =>
    subst hm
    intro src
    simp only [RustHeap.arrayAt, Nat.mul_zero]
    refine Entails.sepExists_right [] (Entails.pure_right rfl ?_)
    rw [pointsToBytes_nil, emp_sepConj]
    exact relocatedHeap_intro emp fun dst => by rw [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  | cons x xs ih =>
    have htl := ih (stride * xs.length) rfl
    have hcons := Relocatable.sepConj (off := BitVec.ofNat 64 stride) (m := m) rfl
      (by simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hm; omega)
      (h x) htl
    exact Relocatable.congr rfl (fun _ => rfl) hcons

theorem Relocatable.of_polyEncoderAt (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 400 (fun a => polyEncoderAt A a enc) := by
  have hstate : Relocatable 392 (fun a => encoderStateAt A a enc.s) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only [encoderStateAt]
      refine Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ => ?_
      have harr : Relocatable 384 (fun a => pointListOf A a pts) :=
        Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
          (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value)
          pts 384 (by rw [hlen]; rfl)
      exact Relocatable.sepConj (off := polyEncoderVecsOff) (m := 392) rfl rfl
        (Relocatable.pointsTo64 polyEncoderPointsTag) harr
    | polys ps =>
      dsimp only [encoderStateAt]
      refine Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen => ?_
      have harr : Relocatable 384 (fun a => polyListOf A a ps) :=
        Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
          (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients)
          ps 384 (by rw [hlen]; rfl)
      exact Relocatable.sepConj (off := polyEncoderVecsOff) (m := 392) rfl rfl
        (Relocatable.pointsTo64 polyEncoderPolysTag) harr
  have hfull := Relocatable.sepConj (off := 392#64) (m := 400) rfl rfl hstate
    (Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
      (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion 4))
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyEncoderAt polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  have h1 : a + 392#64 = a + 0x188#64 := rfl
  have h2 : (a + 392#64) + 4#64 = a + 0x18c#64 := by bv_omega
  rw [h1, h2]

theorem Relocatable.of_polyDecoderAt (A : RustAlloc) (dec : PolyDecoder) :
    Relocatable 400 (fun a => polyDecoderAt A a dec) := by
  unfold Poly.polyDecoderAt
  refine Relocatable.pure_left (dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64) fun ⟨hlen, _⟩ => ?_
  have harr : Relocatable 384 (fun a => sortedSetPtListOf A a dec.pts) :=
    Relocatable.arrayAt (elem := fun s addr => sortedSetPtOf A addr s)
      (fun s => Relocatable.vecOf A ptStride ptAlign ptAt s.vec)
      dec.pts 384 (by rw [hlen]; rfl)
  have htail2 : Relocatable 8 (fun a =>
      ((a + 0#64) ↦₈ boolByte dec.isComplete) ∗ memRegion (a + 1#64) 7) := by
    have h := Relocatable.sepConj (off := 1#64) (m := 8) rfl rfl
      (Relocatable.pointsTo8 (boolByte dec.isComplete)) (Relocatable.of_memRegion 7)
    refine Relocatable.congr rfl (fun a => ?_) h
    rw [BitVec.add_zero]
  have htail16 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
    (Relocatable.pointsTo64 (BitVec.ofNat 64 dec.ptsNeeded)) htail2
  have hfull := Relocatable.sepConj (off := 384#64) (m := 400) rfl rfl harr htail16
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyDecoderPtsNeededOff polyDecoderIsCompleteOff polyDecoderPadOff polyDecoderPadSize
  have h1 : a + 384#64 = a + 0x180#64 := rfl
  have h2 : ((a + 384#64) + 8#64) + 0#64 = a + 0x188#64 := by bv_omega
  have h3 : ((a + 384#64) + 8#64) + 1#64 = a + 0x189#64 := by bv_omega
  rw [h2, h3, h1]

/-! ## 2. Unified Partial-Relocation `memcpy` Helper (`call_memcpy_keep_relocate`) -/

/-- Pre-split entailment for `memcpy(dst, src, k + m)` where `F` (`k` bytes) is kept at `src`
    and `G` (`m` bytes at offset `off`) is relocated to `dst + off`. -/
theorem memcpy_keep_relocate_split {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64) :
    F src ∗ G (src + off) ⊢
      ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (src ↦ₛ (bs1 ++ bs2)) ∗
        relocatedHeap F bs1 ∗
        relocatedHeap G bs2 := by
  refine Entails.trans (sepConj_mono (hF src) (hG (src + off))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepConj_assoc (⌜bs1.length = k⌝)]
  apply Entails.pure_left; intro hlen1
  rw [sepConj_left_comm ((src ↦ₛ bs1) ∗ relocatedHeap F bs1)]
  apply Entails.pure_left; intro hlen2
  have hlen12 : (bs1 ++ bs2).length = n := by
    rw [List.length_append, hlen1, hlen2, hkm]
  refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
  refine Entails.pure_right ⟨hlen1, hlen2, hlen12⟩ ?_
  have hsplit_src : (src ↦ₛ (bs1 ++ bs2)) = (src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append src bs1 bs2, hlen1, ← hoff]
  rw [hsplit_src]
  exact Entails.of_eq (by ac_rfl)

/-- Post-recombine entailment for `memcpy(dst, src, k + m)`:
    recombines `(dst ↦ₛ (bs1 ++ bs2))` with `relocatedHeap G bs2` into `memRegion dst k ∗ G (dst + off)`,
    and `(src ↦ₛ (bs1 ++ bs2))` with `relocatedHeap F bs1` into `F src ∗ memRegion (src + off) m`. -/
theorem memcpy_keep_relocate_recombine {k m : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    {bs1 bs2 : List (BitVec 8)}
    (hoff : off = BitVec.ofNat 64 k)
    (hlen1 : bs1.length = k)
    (hlen2 : bs2.length = m)
    (dst src : BitVec 64) :
    (dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
      relocatedHeap F bs1 ∗ relocatedHeap G bs2 ⊢
    (memRegion dst k ∗ G (dst + off)) ∗
      (F src ∗ memRegion (src + off) m) := by
  have hsplit_dst : (dst ↦ₛ (bs1 ++ bs2)) = (dst ↦ₛ bs1) ∗ ((dst + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append dst bs1 bs2, hlen1, ← hoff]
  have hsplit_src : (src ↦ₛ (bs1 ++ bs2)) = (src ↦ₛ bs1) ∗ ((src + off) ↦ₛ bs2) := by
    rw [pointsToBytes_append src bs1 bs2, hlen1, ← hoff]
  have hdst1 : (dst ↦ₛ bs1) ⊢ memRegion dst k := by
    rw [← hlen1]; exact pointsToBytes_entails_memRegion dst bs1
  have hsrc2 : ((src + off) ↦ₛ bs2) ⊢ memRegion (src + off) m := by
    rw [← hlen2]; exact pointsToBytes_entails_memRegion (src + off) bs2
  have hreord :
      (dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
        relocatedHeap F bs1 ∗ relocatedHeap G bs2 =
      ((dst ↦ₛ bs1) ∗ (((dst + off) ↦ₛ bs2) ∗ relocatedHeap G bs2)) ∗
        (((src ↦ₛ bs1) ∗ relocatedHeap F bs1) ∗ ((src + off) ↦ₛ bs2)) := by
    rw [hsplit_dst, hsplit_src]; ac_rfl
  rw [hreord]
  exact sepConj_mono
    (sepConj_mono hdst1 (relocatedHeap_recompose G bs2 (dst + off)))
    (sepConj_mono (relocatedHeap_recompose F bs1 src) hsrc2)

/-- Call `memcpy` inside `SepWPp`, keeping `F src` (`k` bytes) at `src` and
    relocating `G (src + off)` (`m` bytes) to `dst + off`. -/
theorem call_memcpy_keep_relocate {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc
      sessionMemcpyRegionSpec)
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off))) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) := by
    rw [hsplit]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right
      (memcpy_keep_relocate_split hoff hkm hF hG dst src))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    rw [sepConj_left_comm (memRegion dst n), sepConj_assoc (⌜_⌝)]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine SepWPp.exists_elim fun bs1 => SepWPp.exists_elim fun bs2 => ?_
  refine SepWPp.pure_left fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWPp.call hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun _ _ h => by
      dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, hm⟩
  · dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
          (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m)) ∗ Frame) := by
      have hreord :
          (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2))) ∗
            (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) =
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗ Frame := by ac_rfl
      rw [hreord]
      exact sepConj_mono_left hrec
    refine SepWPp.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-! ## 3. Word-Tuple and Encoder/Decoder `Relocatable` Instances -/

/-- `Relocatable 48` for 6 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words6 (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    Relocatable 48 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) := by
  have h45 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
    (Relocatable.pointsTo64 w4) (Relocatable.pointsTo64 w5)
  have h35 := Relocatable.sepConj (off := 8#64) (m := 24) rfl rfl
    (Relocatable.pointsTo64 w3) h45
  have h25 := Relocatable.sepConj (off := 8#64) (m := 32) rfl rfl
    (Relocatable.pointsTo64 w2) h35
  have h15 := Relocatable.sepConj (off := 8#64) (m := 40) rfl rfl
    (Relocatable.pointsTo64 w1) h25
  have h05 := Relocatable.sepConj (off := 8#64) (m := 48) rfl rfl
    (Relocatable.pointsTo64 w0) h15
  refine Relocatable.congr rfl (fun a => ?_) h05
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : ((a + 8#64) + 8#64) + 8#64 = a + 24#64 := by bv_omega
  have ha32 : (((a + 8#64) + 8#64) + 8#64) + 8#64 = a + 32#64 := by bv_omega
  have ha40 : ((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64 = a + 40#64 := by bv_omega
  rw [ha40, ha32, ha24, ha16]

/-- `Relocatable 24` for 3 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words3 (w0 w1 w2 : BitVec 64) :
    Relocatable 24 (fun a =>
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  have h12 := Relocatable.sepConj (off := 8#64) (m := 16) rfl rfl
    (Relocatable.pointsTo64 w1) (Relocatable.pointsTo64 w2)
  have h02 := Relocatable.sepConj (off := 8#64) (m := 24) rfl rfl
    (Relocatable.pointsTo64 w0) h12
  refine Relocatable.congr rfl (fun a => ?_) h02
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [ha16]

/-- `Relocatable 72` for 9 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words9 (a0 a1 a2 a3 a4 a5 h0 h1 h2 : BitVec 64) :
    Relocatable 72 (fun a =>
      (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
      ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
      ((a + 48#64) ↦₆₄ h0) ∗ ((a + 56#64) ↦₆₄ h1) ∗ ((a + 64#64) ↦₆₄ h2)) := by
  have h := Relocatable.sepConj (off := 48#64) (m := 72) rfl rfl
    (Relocatable.words6 a0 a1 a2 a3 a4 a5) (Relocatable.words3 h0 h1 h2)
  refine Relocatable.congr rfl (fun a => ?_) h
  have ha56 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have ha64 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha56, ha64]; ac_rfl

/-- `Relocatable 96` for 12 consecutive 64-bit words starting at `a`. -/
theorem Relocatable.words12 (a0 a1 a2 a3 a4 a5 h0 h1 h2 c0 c1 c2 : BitVec 64) :
    Relocatable 96 (fun a =>
      (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
      ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
      ((a + 48#64) ↦₆₄ h0) ∗ ((a + 56#64) ↦₆₄ h1) ∗ ((a + 64#64) ↦₆₄ h2) ∗
      ((a + 72#64) ↦₆₄ c0) ∗ ((a + 80#64) ↦₆₄ c1) ∗ ((a + 88#64) ↦₆₄ c2)) := by
  have h := Relocatable.sepConj (off := 72#64) (m := 96) rfl rfl
    (Relocatable.words9 a0 a1 a2 a3 a4 a5 h0 h1 h2) (Relocatable.words3 c0 c1 c2)
  refine Relocatable.congr rfl (fun a => ?_) h
  have ha80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have ha88 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha80, ha88]; ac_rfl

/-- `Relocatable 472` for `polyEncoderAt A a enc` followed by 9 words at `a + 400..a + 472`. -/
theorem Relocatable.polyEncoder_words9 (A : RustAlloc) (enc : PolyEncoder)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 : BitVec 64) :
    Relocatable 472 (fun a =>
      polyEncoderAt A a enc ∗
      (((a + 400#64) ↦₆₄ a0) ∗ ((a + 408#64) ↦₆₄ a1) ∗ ((a + 416#64) ↦₆₄ a2) ∗
       ((a + 424#64) ↦₆₄ a3) ∗ ((a + 432#64) ↦₆₄ a4) ∗ ((a + 440#64) ↦₆₄ a5) ∗
       ((a + 448#64) ↦₆₄ k0) ∗ ((a + 456#64) ↦₆₄ k1) ∗ ((a + 464#64) ↦₆₄ k2))) := by
  have h := Relocatable.sepConj (off := 400#64) (m := 472) rfl rfl
    (Relocatable.of_polyEncoderAt A enc)
    (Relocatable.words9 a0 a1 a2 a3 a4 a5 k0 k1 k2)
  refine Relocatable.congr rfl (fun a => ?_) h
  have ha408 : (a + 400#64) + 8#64 = a + 408#64 := by bv_omega
  have ha416 : (a + 400#64) + 16#64 = a + 416#64 := by bv_omega
  have ha424 : (a + 400#64) + 24#64 = a + 424#64 := by bv_omega
  have ha432 : (a + 400#64) + 32#64 = a + 432#64 := by bv_omega
  have ha440 : (a + 400#64) + 40#64 = a + 440#64 := by bv_omega
  have ha448 : (a + 400#64) + 48#64 = a + 448#64 := by bv_omega
  have ha456 : (a + 400#64) + 56#64 = a + 456#64 := by bv_omega
  have ha464 : (a + 400#64) + 64#64 = a + 464#64 := by bv_omega
  rw [ha408, ha416, ha424, ha432, ha440, ha448, ha456, ha464]

/-- `Relocatable 408` for `(a ↦₆₄ epoch) ∗ polyDecoderAt A (a + 8#64) dec`. -/
theorem Relocatable.epoch_polyDecoderAt (A : RustAlloc) (epoch : BitVec 64) (dec : PolyDecoder) :
    Relocatable 408 (fun a => (a ↦₆₄ epoch) ∗ polyDecoderAt A (a + 8#64) dec) :=
  Relocatable.sepConj (off := 8#64) (m := 408) rfl rfl
    (Relocatable.pointsTo64 epoch) (Relocatable.of_polyDecoderAt A dec)

end CryptoVerification.SpqrV1.States.IntoPb
