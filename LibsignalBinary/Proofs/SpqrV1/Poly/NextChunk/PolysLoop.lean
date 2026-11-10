/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `EncoderState::Polys` Path

Verifies the 16-iteration polynomial evaluation loop (`0x6a3e0..0x6a45c -> 0x6b508`) when
`x.enc.s = .polys polys`, invoking `<Poly>::compute_at` (`0x61914`) on each `polys[i]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize

/-! ## 1. Separation-Logic Helpers for `out_ptr` Buffer and `polysArrayAt` -/

theorem memRegion_split_two_bytes (base : BitVec 64) (i : Nat) (hi : i < 16) :
    memRegion (base + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8,
        ((base + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
        ((base + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1) ∗
        memRegion (base + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) := by
  have h1 : 32 - 2 * i = 1 + (31 - 2 * i) := by omega
  have h2 : 31 - 2 * i = 1 + (32 - 2 * (i + 1)) := by omega
  have ha1 : base + BitVec.ofNat 64 (2 * i + 1) = (base + BitVec.ofNat 64 (2 * i)) + 1#64 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have ha2 : base + BitVec.ofNat 64 (2 * (i + 1)) = (base + BitVec.ofNat 64 (2 * i + 1)) + 1#64 := by
    have heq : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, heq]
  rw [ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 (2 * i)) (n := 1) (k := 31 - 2 * i)
        (b' := base + BitVec.ofNat 64 (2 * i + 1)) h1 ha1 (by omega),
      ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 (2 * i + 1)) (n := 1) (k := 32 - 2 * (i + 1))
        (b' := base + BitVec.ofNat 64 (2 * (i + 1))) h2 ha2 (by omega),
      ProofLib.memRegion_one (base + BitVec.ofNat 64 (2 * i)),
      ProofLib.memRegion_one (base + BitVec.ofNat 64 (2 * i + 1))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b1
  apply Entails.sepExists_elim; intro b0
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.of_eq (by ac_rfl)))

theorem pointsToBytes_append_two_bytes (base : BitVec 64) (bs : List (BitVec 8)) (i : Nat)
    (hlen : bs.length = 2 * i) (b0 b1 : BitVec 8) :
    (base ↦ₛ bs) ∗
      ((base + BitVec.ofNat 64 (2 * i)) ↦₈ b0) ∗
      ((base + BitVec.ofNat 64 (2 * i + 1)) ↦₈ b1) ⊢
      (base ↦ₛ (bs ++ [b0, b1])) := by
  rw [ProofLib.pointsToBytes_append base bs [b0, b1], hlen]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have ha1 : (base + BitVec.ofNat 64 (2 * i)) + 1#64 = base + BitVec.ofNat 64 (2 * i + 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [ha1]
  exact Entails.of_eq (by ac_rfl)

theorem arrayAt_append {α : Type} (elem : α → BitVec 64 → SepProp) (stride : Nat) :
    ∀ (xs ys : List α) (base : BitVec 64),
      arrayAt elem stride base (xs ++ ys) =
        (arrayAt elem stride base xs ∗
         arrayAt elem stride (base + BitVec.ofNat 64 (stride * xs.length)) ys)
  | [], ys, base => by simp [arrayAt]
  | x :: xs, ys, base => by
    simp only [List.cons_append, arrayAt, arrayAt_append elem stride xs ys, List.length_cons]
    have haddr : (base + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (stride * xs.length) =
        base + BitVec.ofNat 64 (stride * (xs.length + 1)) := by
      have hm : stride + stride * xs.length = stride * (xs.length + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
    rw [haddr]
    ac_rfl

theorem polyListOf_split_idx (A : RustAlloc) (base : BitVec 64)
    (polys : List LibsignalSpqrV1.Poly) (i : Nat) (hi : i < polys.length) :
    polyListOf A base polys =
      (polyListOf A base (polys.take i) ∗
        polyOf A (base + BitVec.ofNat 64 (24 * i)) (polys[i]'hi) ∗
        polyListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1))) := by
  unfold polyListOf
  conv => lhs; rw [← List.take_append_drop i polys]
  rw [arrayAt_append, List.length_take_of_le (by omega), List.drop_eq_getElem_cons hi]
  simp only [arrayAt, vecHeaderBytes]
  have haddr : (base + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 24 =
      base + BitVec.ofNat 64 (24 * (i + 1)) := by
    have hm : 24 * i + 24 = 24 * (i + 1) := by omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]
  rw [haddr]

theorem polyCoefficients_len_bound_of_cap {len cap : Nat}
    (hlen : len ≤ cap) (hcap : cap * gf16Stride < 2 ^ 63) :
    2 * len + 2 ≤ 2 ^ 63 := by
  dsimp [gf16Stride] at hcap
  omega

theorem chunkPolysBytes_add (idx : BitVec 16) (polys : List LibsignalSpqrV1.Poly) :
    ∀ (m k n : Nat),
      chunkPolysBytes idx polys k (m + n) =
        chunkPolysBytes idx polys k m ++ chunkPolysBytes idx polys (k + m) n
  | 0, k, n => by simp [chunkPolysBytes]
  | m + 1, k, n => by
    have hadd : m + 1 + n = (m + n) + 1 := by omega
    have hk : k + (m + 1) = (k + 1) + m := by omega
    rw [hadd]
    conv => lhs; unfold chunkPolysBytes
    conv => rhs; arg 1; unfold chunkPolysBytes
    rw [chunkPolysBytes_add idx polys m (k + 1) n, hk]
    simp only [List.cons_append]

theorem chunkPolysBytes_zero_succ (idx : BitVec 16) (polys : List LibsignalSpqrV1.Poly)
    (i : Nat) (hi : i < polys.length) :
    chunkPolysBytes idx polys 0 (i + 1) =
      chunkPolysBytes idx polys 0 i ++
        [BitVec.setWidth 8 ((computeAtPure (polys[i]'hi) (GF16.new idx)).value >>> 8),
         BitVec.setWidth 8 (computeAtPure (polys[i]'hi) (GF16.new idx)).value] := by
  rw [chunkPolysBytes_add idx polys i 0 1, Nat.zero_add]
  have hp : polys[i]? = some (polys[i]'hi) := List.getElem?_eq_getElem hi
  simp [chunkPolysBytes, hp]

theorem call_panic_sepWPp {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s0 s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.call_frame hcall hpc hrun hsp hlr hspec hφ hP hexit
    (fun sf _ hm => ?_)
    (fun sf hpcf hrunf hspf hcsf => hnext sf hpcf hrunf hspf hcsf)
    (by intro sf R' _ hm; rw [hoom_eq sf] at hm; exact Satisfies.drop_mid hm)
  have hpan_tr : allocFailedIn s sf = allocFailedIn s0 sf := by
    unfold allocFailedIn; rw [htr]
  rw [hpan_eq sf, hpan_tr, htr, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hpan, hm2⟩
  rw [← sepConj_assoc] at hm2
  unfold nextChunkOnPanic
  exact allowPanic_panicked (φ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) hpan hm2

/-- Spare-capacity and allocator-liveness portion of `polyBuf`. -/
def polyBufRest (A : RustAlloc) (cap ptr : BitVec 64) (p : LibsignalSpqrV1.Poly) : SepProp :=
  if cap = 0 then emp
  else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
    memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
      ((cap.toNat - p.coefficients.length) * gf16Stride)

theorem polyBufBody_eq_slice_rest (A : RustAlloc) (cap ptr : BitVec 64)
    (p : LibsignalSpqrV1.Poly) (hlen : p.coefficients.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
       arrayAt gf16At gf16Stride ptr p.coefficients ∗
       memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
         ((cap.toNat - p.coefficients.length) * gf16Stride)) =
      (gf16SliceAt ptr p.coefficients ∗ polyBufRest A cap ptr p) := by
  unfold polyBufRest gf16SliceAt
  by_cases h0 : cap = 0
  · have hcap0 : cap.toNat = 0 := by subst h0; rfl
    have hlen0 : p.coefficients.length = 0 := by omega
    have hnil : p.coefficients = [] := List.eq_nil_of_length_eq_zero hlen0
    simp [h0, hnil, arrayAt]
  · simp only [h0, ↓reduceIte]
    ac_rfl

theorem polyOf_unfold (A : RustAlloc) (v : BitVec 64) (p : LibsignalSpqrV1.Poly) :
    polyOf A v p ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
        ⌜p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * gf16Stride) gf16Align ∗
           arrayAt gf16At gf16Stride ptr p.coefficients ∗
           memRegion (ptr + BitVec.ofNat 64 (p.coefficients.length * gf16Stride))
             ((cap.toNat - p.coefficients.length) * gf16Stride)) := by
  unfold polyOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))

theorem polyOf_fold (A : RustAlloc) (v cap ptr : BitVec 64) (p : LibsignalSpqrV1.Poly)
    (hbounds : p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 p.coefficients.length) ∗
      gf16SliceAt ptr p.coefficients ∗
      polyBufRest A cap ptr p ⊢
      polyOf A v p := by
  have htrue : (p.coefficients.length ≤ cap.toNat ∧ cap.toNat * gf16Stride < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    propext ⟨fun _ => trivial, fun _ => hbounds⟩
  unfold polyOf vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_right cap
  apply Entails.sepExists_right ptr
  rw [htrue, pure_true, emp_sepConj, polyBufBody_eq_slice_rest A cap ptr p hbounds.1]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Arithmetic and Bitvector Normalization for the `Polys` Loop -/

@[local simp, local arm64_norm, local wp_norm]
theorem x21_sub_8_eq (encA : BitVec 64) (i : Nat) :
    (encA + BitVec.ofNat 64 (24 * i + 24)) + 18446744073709551608#64 =
      ((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64 := by
  rw [BitVec.ofNat_add]
  generalize BitVec.ofNat 64 (24 * i) = u
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem x21_sub_8_add_8_eq (encA : BitVec 64) (i : Nat) :
    (((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) + 8#64 =
      ((encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64 := by
  rw [BitVec.add_assoc (((encA + 8#64) + BitVec.ofNat 64 (24 * i))) 8#64 8#64]
  rfl

@[local simp, local arm64_norm, local wp_norm]
theorem x21_add_24_eq (encA : BitVec 64) (i : Nat) :
    (encA + BitVec.ofNat 64 (24 * i + 24)) + 24#64 =
      encA + BitVec.ofNat 64 (24 * (i + 1) + 24) := by
  have hm : (24 * i + 24) + 24 = 24 * (i + 1) + 24 := by omega
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hm]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_two_mul_add_one (i : Nat) :
    BitVec.ofNat 64 (2 * i) + 1#64 = BitVec.ofNat 64 (2 * i + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_two_mul_add_two (i : Nat) :
    BitVec.ofNat 64 (2 * i) + 2#64 = BitVec.ofNat 64 (2 * (i + 1)) := by
  have hm : 2 * i + 2 = 2 * (i + 1) := by omega
  rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, hm]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg1 (r : Nat) :
    BitVec.ofNat 64 (r + 1) + 18446744073709551615#64 = BitVec.ofNat 64 r := by
  have hneg : (1#64 : BitVec 64) + 18446744073709551615#64 = 0#64 := rfl
  rw [BitVec.ofNat_add]
  change (BitVec.ofNat 64 r + 1#64) + 18446744073709551615#64 = BitVec.ofNat 64 r
  rw [BitVec.add_assoc, hneg, BitVec.add_zero]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one' (r : Nat) :
    BitVec.ofNat 64 (r + 1) - 1#64 = BitVec.ofNat 64 r :=
  ofNat_sub_one_succ r

theorem ofNat_sub_one_beq_zero {rem : Nat} (hrem : rem < 16) :
    (BitVec.ofNat 64 (rem + 1) == 1#64) = (rem == 0) ∧
    (BitVec.ofNat 64 rem == 0#64) = (rem == 0) := by
  cases rem with
  | zero => decide
  | succ r =>
    have h1 : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
    have h0 : (0#64 : BitVec 64) = BitVec.ofNat 64 0 := rfl
    rw [h1, h0]
    rcases ofNat_beq_false_of_lt (a := 1) (b := r + 1 + 1) (by omega) (by omega) with ⟨_, _, ha, _⟩
    rcases ofNat_beq_false_of_lt (a := 0) (b := r + 1) (by omega) (by omega) with ⟨_, _, hb, _⟩
    exact ⟨ha, hb⟩

theorem lsr8_trunc8_of_trunc16 {v : BitVec 64} {val16 : BitVec 16}
    (h : v.truncate 16 = val16) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 8) =
      BitVec.setWidth 8 (val16 >>> 8) := by
  subst h; bv_slice

theorem trunc8_of_trunc16 {v : BitVec 64} {val16 : BitVec 16}
    (h : v.truncate 16 = val16) :
    BitVec.zeroExtend 8 v = BitVec.setWidth 8 val16 := by
  subst h; bv_slice

@[local simp, local arm64_norm, local wp_norm]
theorem setWidth16_mov_w_zext16 (idx16 : BitVec 16) :
    ((((idx16.setWidth 64).setWidth 32).setWidth 64).setWidth 16) = idx16 := by
  bv_slice

theorem nextChunk_add_computeAt_off (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr polyNextChunkName + 18446744073709516176#64 =
      (libsignalSessionCode.rebase b H).fnAddr computeAtName := by
  simp only [Program.fnAddr_rebase, polyNextChunk_fnOff, computeAt_fnOff]
  bv_omega

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog ret s (P x) Q Qp) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp := by
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R hmx

theorem computeAt_pre_split (p_coeffs : BitVec 64) (poly : LibsignalSpqrV1.Poly)
    (b fsp : BitVec 64) (A : RustAlloc)
    (P_cap P_ptr P_len P_restBuf P_out P_rem P_live P_outA P_tag P_take P_drop
     P_idx P_pad P_56 P_232 P_240 P_248 P_lfr P_saved : SepProp) :
    (P_cap ∗ P_ptr ∗ P_len ∗ (gf16SliceAt p_coeffs poly.coefficients ∗ P_restBuf)) ∗
      (P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
        P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗
        (memRegion (fsp - 17232#64) 12880 ∗ stackAt fsp computeAtStack)) =
    (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt fsp computeAtStack) ∗
    (P_cap ∗ P_ptr ∗ P_len ∗ P_restBuf ∗
      P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
      P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
      memRegion (fsp - 17232#64) 12880) := by
  ac_rfl

theorem call_computeAt_sepWPp {b : BitVec 64} {ext : String → Option (State → State)}
    {A : RustAlloc} {ret_pc ret fsp : BitVec 64}
    {s0 s : State} {p_coeffs : BitVec 64} {poly : LibsignalSpqrV1.Poly} {x_gf : GF16}
    {F P R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName)
      (computeAtSpec A b))
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : fsp &&& 0xf#64 = 0#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = p_coeffs)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length)
    (hx2 : (s.readReg64 Reg.x2).truncate 16 = x_gf.value)
    (hlen : 2 * poly.coefficients.length + 2 ≤ 2 ^ 63)
    (hP : P = (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt fsp computeAtStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      (sf.readReg64 Reg.x0).truncate 16 = (computeAtPure poly x_gf).value →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        ((gf16SliceAt p_coeffs poly.coefficients ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt fsp computeAtStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, hfsp_al]
  refine call_panic_sepWPp hcall (x := { p_coeffs := p_coeffs, poly := poly, x := x_gf })
    (φ := s.readReg64 Reg.x0 = p_coeffs ∧
      s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length ∧
      (s.readReg64 Reg.x2).truncate 16 = x_gf.value ∧
      2 * poly.coefficients.length + 2 ≤ 2 ^ 63)
    (T := gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt fsp computeAtStack)
    hpc hrun hsp_al hlr htr
    (by simp only [computeAtSpec, hsp_eq])
    ⟨hx0, hx1, hx2, hlen⟩
    hP
    (fun _ => rfl)
    (fun _ _ _ _ hm => by simp [computeAtSpec, satisfies_pure_sepConj] at hm)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  have hspf' : sf.sp = fsp := hspf.trans hsp_eq
  conv => arg 4; simp only [computeAtSpec, hsp_eq, sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨htrf, hx0f⟩
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (hnext sf hpcf hrunf hspf' hcsf (htrf.trans htr) hx0f)
  ac_rfl

/-! ## 3. Single Iteration of the `Polys` Loop (`0x6a40c..0x6a45c -> 0x6a3f0..0x6a408`) -/

set_option maxHeartbeats 1600000 in
theorem polysLoop_step_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (i rem : Nat) (hrem_eq : i + (rem + 1) = 16)
    (s0 s : State)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1))
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hnext : ∀ sf : State,
      sf.pc = (if rem == 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 136#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * (i + 1) + 24) →
      sf.readReg64 .x22 = BitVec.ofNat 64 rem →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitAt b ∗
         reduceTableAt b ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitAt b ∗
       reduceTableAt b ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hi16 : i < 16 := by omega
  have hi_len : i < polys.length := by omega
  have hcomp := computeAt_ok b hb A ext hA
  dsimp only [tripleRatchetProgAtExt] at hcomp
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x6c 112
  clear hA
  rw [polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
  apply SepWPp.fold (polyOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len)) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull :
      ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
        (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest =
          ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [polyBufBody_eq_slice_rest A cap ptr (polys[i]'hi_len) hlen_cap]
  have hlen_bound : 2 * (polys[i]'hi_len).coefficients.length + 2 ≤ 2 ^ 63 :=
    polyCoefficients_len_bound_of_cap hlen_cap hcap_bound
  have hfn_off := nextChunk_add_computeAt_off b (Rust.withPanics ext)
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName)
  wp_steps 3
  apply SepWP.done (by rw [← hfn_off]; wp_norm_goal) (by wp_norm_lhs)
  rw [stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
  have hsp_al : s0.sp - 1200#64 &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  refine call_computeAt_sepWPp hcomp
    (ret_pc := entry + 148#64)
    (x_gf := GF16.new (x.enc.idx.setWidth 16))
    ?_ ?_ ?_ hsp_al ?_ ?_ ?_ ?_ ?_ hlen_bound
    (computeAt_pre_split ptr (polys[i]'hi_len) b (s0.sp - 1200#64) A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    ?_
  · rw [← hfn_off]; wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using htr
  · wp_norm_lhs
  · wp_norm_lhs
  · simp [GF16.new, arm64_norm, wp_norm, hx27]
  intro sf1 hpc1 hrun1 hsp1' hcs1 htr1' hx0_1
  rcases hcs1 with ⟨_, _, hx21_cs, hx22_cs, _, hx24_cs, _, _, hx27_cs, _, _, hvregs_cs⟩
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by
    rw [hvregs_cs]; simpa [arm64_norm, wp_norm] using hvregs
  have hx21_1 : sf1.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) := by
    rw [Reg.x21, hx21_cs]; simpa [arm64_norm, wp_norm] using hx21
  have hx22_1 : sf1.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) := by
    rw [Reg.x22, hx22_cs]; simpa [arm64_norm, wp_norm] using hx22
  have hx24_1 : sf1.readReg64 .x24 = x.encA := by
    rw [Reg.x24, hx24_cs]; simpa [arm64_norm, wp_norm] using hx24
  have hx27_1 : sf1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 := by
    rw [Reg.x27, hx27_cs]; simpa [arm64_norm, wp_norm] using hx27
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_sub_one_beq_zero (rem := rem) (by omega) with ⟨hsubs_z1, hsubs_z2⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  apply SepWPp.of_sepWP (mid := if rem == 0 then entry + 4484#64 else entry + 136#64)
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 20
  have hb0_eq :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5))) >>> 8) =
        BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8) :=
    lsr8_trunc8_of_trunc16 hx0_1
  have hb1_eq :
      BitVec.zeroExtend 8 (sf1.readReg64 (Reg.gpr 0#5)) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_of_trunc16 hx0_1
  wp_conv_pre => rw [hb0_eq, hb1_eq]
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value) ⊢
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) := by
    rw [chunkPolysBytes_zero_succ (x.enc.idx.setWidth 16) polys i hi_len]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) i
      (chunkPolysBytes_length (x.enc.idx.setWidth 16) polys 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_poly :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (polys[i]'hi_len).coefficients.length) ∗
        gf16SliceAt ptr (polys[i]'hi_len).coefficients ∗
        polyBufRest A cap ptr (polys[i]'hi_len) ⊢
        polyOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) :=
    polyOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (polys[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_poly (by sep_focus)
  have hfold_list :
      polyListOf A (x.encA + 8#64) (polys.take i) ∗
        polyOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) ∗
        polyListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1)) ⊢
        polyListOf A (x.encA + 8#64) polys := by
    rw [← polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  have hfold_stk :
      memRegion (s0.sp - 18432#64) 12880 ∗
        stackAt (s0.sp - 1200#64) computeAtStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    have hsub : s0.sp - 18432#64 = (s0.sp - 1200#64) - 17232#64 := by bv_omega
    rw [hsub, ← stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_stk (by sep_focus)
  apply SepWP.done
  · simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hsubs_z1, hsubs_z2]
  · wp_norm_lhs
  · refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
      (hnext _ ?_ (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1')
        (by simpa [arm64_norm, wp_norm] using htr1')
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hvregs_1])
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx21_1])
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx22_1])
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24_1])
        (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27_1]))
    simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hsubs_z1, hsubs_z2]

/-! ## 4. Full 16-Iteration `Polys` Loop and `EncoderState::Polys` Path -/

theorem polysLoop_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64) :
    ∀ (rem i : Nat) (hrem_eq : i + (rem + 1) = 16) (s : State),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 136#64 →
      s.status = .Running →
      s.sp = s0.sp - 1200#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      (∀ sf : State,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4484#64 →
        sf.status = .Running →
        sf.sp = s0.sp - 1200#64 →
        sf.trace = s0.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        sf.readReg64 .x20 = 32#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
          ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16) ∗
           A.live out_ptr 32 1 ∗
           memRegion x.outA chunkSize ∗
           (x.encA ↦₆₄ polyEncoderPolysTag) ∗
           polyListOf A (x.encA + 8#64) polys ∗
           ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
           memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
           (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
           (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
           (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
           (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
           localFrameRest (s0.sp - 1200#64) ∗
           savedCells s0 ∗
           tokenInitAt b ∗
           reduceTableAt b ∗
           A.pool ∗
           stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitAt b ∗
         reduceTableAt b ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | 0, i, hrem_eq, s, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hdone => by
    have hi15 : i = 15 := by omega
    subst hi15
    refine polysLoop_step_sepWPp A b ext hb hA x polys hlen_polys out_ptr R 15 0 hrem_eq
      s0 s hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f _hx21_f _hx22_f hx24_f hx27_f
    simp only [beq_self_eq_true, ite_true] at hpc_f
    change sf.readReg64 .x20 = 32#64 at hx20_f
    refine SepWPp.weaken_pre ?_ (hdone sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f)
    rw [show 32 - 2 * (15 + 1) = 0 from rfl, memRegion_zero,
        show BitVec.ofNat 64 (2 * (15 + 1)) = 32#64 from rfl]
    exact Entails.of_eq (by ac_rfl)
  | r + 1, i, hrem_eq, s, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hdone => by
    refine polysLoop_step_sepWPp A b ext hb hA x polys hlen_polys out_ptr R i (r + 1) hrem_eq
      s0 s hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hx20_f hx21_f hx22_f hx24_f hx27_f
    have hne0 : (r + 1 == 0) = false := rfl
    simp only [hne0, Bool.false_eq_true, ite_false] at hpc_f
    exact polysLoop_sepWPp A b ext hb hA x polys hlen_polys out_ptr R s0 hsp0
      r (i + 1) (by omega) sf hpc_f hrun_f hsp_f htr_f hvregs_f hx21_f hx22_f hx24_f hx27_f hdone

set_option maxHeartbeats 1600000 in
theorem nextChunk_polys_sepWPp
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts b A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly)
    (hs_polys : x.enc.s = .polys polys)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A x.encA x.enc ∗
       tokenInitAt b ∗
       reduceTableAt b ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitAt b ∗
             reduceTableAt b ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  unfold polyEncoderAt encoderStateAt
  rw [hs_polys]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro hlen_polys
  have hlen16 : polys.length = 16 := hlen_polys
  have henc_eq : x.enc = { idx := x.enc.idx, s := .polys polys } := by
    cases h : x.enc; simp_all
  have hnc := nextChunk_polys_eq (idx := x.enc.idx) hlen16
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys polys := by
    rw [← henc'_eq]
  refine prologue_sepWPp A b ext hA x polyEncoderPolysTag
    (polyListOf A (x.encA + polyEncoderVecsOff) polys) R s0 hpc hrun hsp0 hx0 hx8 ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx9_1 _hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 1#64 at hx9_1
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x5c 16
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 136#64)
  wp_steps 4
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hentry]
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPolysBytes, pointsToBytes_nil, emp_sepConj]
  refine SepWPp.weaken_pre (Entails.of_eq (by rw [hinit_buf, sepConj_assoc])) ?_
  refine polysLoop_sepWPp A b ext hb hA x polys hlen16 out_ptr R s0 hsp0 15 0 rfl _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hentry]; wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · simp [arm64_norm, wp_norm, hx24_1]
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPolysTag) ∗ polyListOf A (x.encA + 8#64) polys ⊢
        encoderStateAt A x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (polys.length = NUM_POLYS) = True := propext ⟨fun _ => trivial, fun _ => hlen_polys⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq]
  refine SepWP.weaken_pre (Entails.of_eq (by
    simp only [arm64_norm]
    ac_rfl))
    (epilogue_sepWP A b ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
      hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f)
  rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
  rfl

end CryptoVerification.SpqrV1.Poly.NextChunk











