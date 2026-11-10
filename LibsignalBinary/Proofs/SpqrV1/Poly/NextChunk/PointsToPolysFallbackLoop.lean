/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallback
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Basis Loop

**Checked by Lean.**

Verifies the dynamic Lagrange basis interpolation loop (`0x6b3a4..0x6b490`, `+4128 -> +4368`),
invoking `lagrange_interpolate_prepare` and `lagrange_interpolate_complete` on `toOnePts pts`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fbl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fbl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb

/-! ## 1. Pure Characterization of `Poly.lagrangeInterpolatePt` and the Basis Loop -/

/-- Total pure version of `Poly.lagrangeInterpolatePt` (`src/encoding/polynomial.rs:236–242`). -/
def lagrangeInterpolatePtPure (ones : List Pt) (i : Nat) : Poly :=
  { coefficients := (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients.drop 1 }

@[simp]
theorem lagrangeInterpolatePtPure_length (ones : List Pt) (i : Nat) :
    (lagrangeInterpolatePtPure ones i).coefficients.length = ones.length := by
  simp [lagrangeInterpolatePtPure]

theorem lagrangeComplete_prepare_head_tail (ones : List Pt) (i : Nat) :
    ∃ c0 : GF16,
      (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients =
        c0 :: (lagrangeInterpolatePtPure ones i).coefficients := by
  have hlen : (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients.length =
      ones.length + 1 := by
    rw [lagrangeCompletePure_length, lagrangePreparePure_length]
  cases hcs : (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients with
  | nil =>
    rw [hcs, List.length_nil] at hlen
    omega
  | cons c0 rest =>
    refine ⟨c0, ?_⟩
    simp [lagrangeInterpolatePtPure, hcs]

theorem lagrangeInterpolatePt_eq_ok (ones : List Pt) (i : Nat)
    (hi : i < ones.length) (hbound : ones.length + 1 ≤ USIZE_MAX) :
    Poly.lagrangeInterpolatePt ones i = .ok (lagrangeInterpolatePtPure ones i) := by
  unfold Poly.lagrangeInterpolatePt
  rw [lagrangeInterpolatePrepare_eq_ok ones hbound]
  dsimp only [Bind.bind, Except.bind]
  rw [lagrangeInterpolateComplete_eq_ok hi]
  dsimp only
  obtain ⟨c0, hc0⟩ := lagrangeComplete_prepare_head_tail ones i
  rw [hc0]
  rfl

/-- Tail list of Lagrange basis polynomials `[lagrangeInterpolatePtPure ones i, ..., lagrangeInterpolatePtPure ones (i + rem - 1)]`. -/
def lagrangeBasisTail (ones : List Pt) : Nat → Nat → List Poly
  | _, 0 => []
  | i, rem + 1 => lagrangeInterpolatePtPure ones i :: lagrangeBasisTail ones (i + 1) rem

@[simp]
theorem lagrangeBasisTail_length (ones : List Pt) (i rem : Nat) :
    (lagrangeBasisTail ones i rem).length = rem := by
  induction rem generalizing i with
  | zero => rfl
  | succ r ih => simp [lagrangeBasisTail, ih]

theorem lagrangeBasisTail_mem_length (ones : List Pt) :
    ∀ (rem i : Nat) (p : Poly),
      p ∈ lagrangeBasisTail ones i rem → p.coefficients.length = ones.length
  | 0, _, _, h => by simp [lagrangeBasisTail] at h
  | rem + 1, i, p, h => by
    simp only [lagrangeBasisTail, List.mem_cons] at h
    rcases h with rfl | hmem
    · exact lagrangeInterpolatePtPure_length ones i
    · exact lagrangeBasisTail_mem_length ones rem (i + 1) p hmem

theorem mapM_range'_lagrangeInterpolatePt_eq_ok (ones : List Pt)
    (hbound : ones.length + 1 ≤ USIZE_MAX) :
    ∀ (rem i : Nat),
      i + rem ≤ ones.length →
      (List.range' i rem).mapM (fun k => Poly.lagrangeInterpolatePt ones k) =
        .ok (lagrangeBasisTail ones i rem)
  | 0, i, _ => rfl
  | rem + 1, i, hle => by
    have hi : i < ones.length := by omega
    simp only [List.range'_succ, List.mapM_cons, lagrangeInterpolatePt_eq_ok ones i hi hbound,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [mapM_range'_lagrangeInterpolatePt_eq_ok ones hbound rem (i + 1) (by omega)]
    rfl

theorem mapM_range_lagrangeInterpolatePt_eq_ok (ones : List Pt)
    (hbound : ones.length + 1 ≤ USIZE_MAX) :
    (List.range ones.length).mapM (fun k => Poly.lagrangeInterpolatePt ones k) =
      .ok (lagrangeBasisTail ones 0 ones.length) := by
  rw [List.range_eq_range']
  exact mapM_range'_lagrangeInterpolatePt_eq_ok ones hbound ones.length 0 (by omega)

/-! ## 2. Call-Site Offset & Stack / Memory Splitting Helpers -/

theorem nextChunk_lagrangePrepare_addr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr lagrangePrepareName =
      (libsignalSessionCode.rebase b H).fnAddr polyNextChunkName +
        bv% (2 ^ 64 + ls_off% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare" -
          ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk") := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, lagrangePrepare_fnOff, polyNextChunk_fnOff]
  bv_omega

theorem nextChunk_lagrangeComplete_addr (b : BitVec 64) (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr lagrangeCompleteName =
      (libsignalSessionCode.rebase b H).fnAddr polyNextChunkName +
        bv% (2 ^ 64 + ls_off% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete" -
          ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk") := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, lagrangeComplete_fnOff, polyNextChunk_fnOff]
  bv_omega

theorem sepConj_mono_fbl {P1 P2 Q1 Q2 : SepProp} (h1 : P1 ⊢ P2) (h2 : Q1 ⊢ Q2) :
    (P1 ∗ Q1) ⊢ (P2 ∗ Q2) :=
  Entails.trans (sepConj_mono_left h1) (sepConj_mono_right h2)

theorem stackAt_lagrangePrepare_split_complete (fsp : BitVec 64) :
    stackAt fsp lagrangePrepareStack =
      stackAt fsp lagrangeCompleteStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - lagrangeCompleteStack) := by
  have heq : lagrangePrepareStack =
      lagrangeCompleteStack + (lagrangePrepareStack - lagrangeCompleteStack) := by decide
  have h1 := ProofLib.stackAt_split_bottom fsp lagrangeCompleteStack
    (lagrangePrepareStack - lagrangeCompleteStack) (by decide)
  rw [← heq] at h1
  rw [h1, sepConj_comm]

theorem stackAt_lagrangePrepare_split_alloc (fsp : BitVec 64) :
    stackAt fsp lagrangePrepareStack =
      stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - allocHookStack) := by
  have heq : lagrangePrepareStack =
      allocHookStack + (lagrangePrepareStack - allocHookStack) := by decide
  have h1 := ProofLib.stackAt_split_bottom fsp allocHookStack
    (lagrangePrepareStack - allocHookStack) (by decide)
  rw [← heq] at h1
  rw [h1, sepConj_comm]

/-- Splitting `gf16SliceAt ptr (c0 :: cs)` into `memRegion ptr 2` and `((ptr + 2#64) ↦ₛ gf16SliceBytes cs)`. -/
theorem gf16SliceAt_cons_memRegion2 (ptr : BitVec 64) (c0 : GF16) (cs : List GF16) :
    gf16SliceAt ptr (c0 :: cs) ⊢
      memRegion ptr 2 ∗ ((ptr + 2#64) ↦ₛ gf16SliceBytes cs) := by
  rw [gf16SliceAt_cons, gf16SliceAt_eq_pointsToBytes (ptr + 2#64) cs]
  refine sepConj_mono_fbl ?_ (Entails.refl _)
  rw [ProofLib.memRegion_two ptr]
  exact Entails.sepExists_right c0.value (Entails.refl _)

/-- Recombining `memRegion ptr 2`, `((ptr + 2#64) ↦ₛ bs)` (with `bs.length = 2 * n`), and spare capacity
    into `memRegion ptr (cap.toNat * 2)` for `__rust_dealloc`. -/
theorem memRegion_recombine_prepare (ptr : BitVec 64) (cap : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hbs : bs.length = 2 * n)
    (hcap : n + 1 ≤ cap.toNat) (hcap_bound : cap.toNat * 2 < 2 ^ 63) :
    memRegion ptr 2 ∗ ((ptr + 2#64) ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 (2 * (n + 1))) (2 * (cap.toNat - (n + 1))) ⊢
      memRegion ptr (cap.toNat * 2) := by
  have h1 : 2 * (n + 1) = 2 + 2 * n := by omega
  have h2 : cap.toNat * 2 = 2 * (n + 1) + 2 * (cap.toNat - (n + 1)) := by omega
  have ha1 : (ptr + 2#64) + BitVec.ofNat 64 (2 * n) = ptr + BitVec.ofNat 64 (2 * (n + 1)) := by
    rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, h1]
  have hm1 := ProofLib.memRegion_split' (b := ptr) (N := 2 * (n + 1)) (n := 2) (k := 2 * n)
    (b' := ptr + 2#64) h1 rfl (by omega)
  have hm2 := ProofLib.memRegion_split' (b := ptr) (N := cap.toNat * 2) (n := 2 * (n + 1))
    (k := 2 * (cap.toNat - (n + 1))) (b' := ptr + BitVec.ofNat 64 (2 * (n + 1))) h2 rfl (by omega)
  refine Entails.trans
    (sepConj_mono_fbl (Entails.refl _)
      (sepConj_mono_fbl (pointsToBytes_entails_memRegion (ptr + 2#64) bs) (Entails.refl _))) ?_
  rw [hbs, ← sepConj_assoc, ← hm1, ← hm2]
  exact Entails.refl _

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

theorem bit62_shl_one_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (n + 1) - 1#64).msb = false ∧
    (BitVec.ofNat 64 n).msb = false := by
  have h2 : (BitVec.ofNat 64 n).msb = false := by
    simp only [BitVec.msb_eq_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      decide_eq_false_iff_not]
    omega
  refine ⟨?_, h2⟩
  rw [ofNat_succ_sub_one_fb]
  exact h2

theorem ult_max_2n_false {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 (2 * n)) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have hlt := BitVec.ult_iff_lt.mp h
  bv_omega

theorem adds_one_ne_zero {i : Nat} (hb : i < 0x0555555555555555) :
    (BitVec.ofNat 64 i + 1#64 == 0#64) = false ∧
    (BitVec.ofNat 64 i + 1#64 != 0#64) = true ∧
    (BitVec.ofNat 64 (i + 1) == 0#64) = false ∧
    (BitVec.ofNat 64 (i + 1) != 0#64) = true := by
  have h1 : (BitVec.ofNat 64 i + 1#64 == 0#64) = false := by
    apply Bool.eq_false_iff.mpr; intro h
    have heq := beq_iff_eq.mp h
    bv_omega
  have h2 : (BitVec.ofNat 64 i + 1#64 != 0#64) = true := by
    rw [bne, h1]; rfl
  have h3 : (BitVec.ofNat 64 (i + 1) == 0#64) = false := by
    rw [← ofNat_add_one_eq_succ_fb]; exact h1
  have h4 : (BitVec.ofNat 64 (i + 1) != 0#64) = true := by
    rw [← ofNat_add_one_eq_succ_fb]; exact h2
  exact ⟨h1, h2, h3, h4⟩

@[local simp, local arm64_norm, local wp_norm]
theorem shl_one_ofNat_eq (n : Nat) :
    BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) := by
  have h : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n * 2#64 := by bv_bits
  rw [h]; bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem shl_one_ofNat_eq_nat (n : Nat) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) :=
  shl_one_ofNat_eq n

theorem shl_one_cap_toNat {cap : BitVec 64} (hbound : cap.toNat * 2 < 2 ^ 63) :
    (cap <<< 1#64).toNat = cap.toNat * 2 := by
  have h : cap <<< 1#64 = cap * 2#64 := by bv_bits
  rw [h, BitVec.toNat_mul, BitVec.toNat_ofNat]
  change (cap.toNat * 2) % 2 ^ 64 = cap.toNat * 2
  exact Nat.mod_eq_of_lt (by omega)

theorem shl_one_cap_toNat_nat {cap : BitVec 64} (hbound : cap.toNat * 2 < 2 ^ 63) :
    (cap <<< 1).toNat = cap.toNat * 2 :=
  shl_one_cap_toNat hbound

theorem memRegion_split_polyHeader_fbl (p : BitVec 64) :
    memRegion p 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) := by
  have hp8 : p + 8#64 = p + BitVec.ofNat 64 8 := rfl
  have hp16 : p + 16#64 = (p + 8#64) + BitVec.ofNat 64 8 := by bv_omega
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 16) (b' := p + 8#64) rfl hp8 (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 8) (b' := p + 16#64) rfl hp16 (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64), ProofLib.memRegion_eight (p + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem polyHeader_entails_memRegion24 (p : BitVec 64) (u0 u8 u16 : BitVec 64) :
    ((p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16)) ⊢ memRegion p 24 := by
  rw [memRegion_split_polyHeader_fbl p]
  exact Entails.sepExists_right u16 (Entails.sepExists_right u8 (Entails.sepExists_right u0 (Entails.refl _)))

theorem polyHeader_entails_memRegion24_off (base : BitVec 64) (u0 u8 u16 : BitVec 64) :
    (((base + 656#64) ↦₆₄ u0) ∗ ((base + 664#64) ↦₆₄ u8) ∗ ((base + 672#64) ↦₆₄ u16)) ⊢
      memRegion (base + 656#64) 24 := by
  have h8 : (base + 656#64) + 8#64 = base + 664#64 := by bv_omega
  have h16 : (base + 656#64) + 16#64 = base + 672#64 := by bv_omega
  rw [← h8, ← h16]
  exact polyHeader_entails_memRegion24 (base + 656#64) u0 u8 u16

theorem polyListOf_cons_fbl (A : RustAlloc) (ptr : BitVec 64) (p : Poly) (ps : List Poly) :
    polyListOf A ptr (p :: ps) =
      (polyOf A ptr p ∗ polyListOf A (ptr + 24#64) ps) := rfl

theorem call_panic_sepWPp_fbl {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
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

theorem call_lagrangePrepare_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {ret_pc ret fsp out ptsPtr : BitVec 64} {pts : List Pt} {s0 s : State} {F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName)
      (lagrangePrepareSpec A b))
    (hlen_bound : 4 * (pts.length + 1) < 2 ^ 63)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : (fsp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = out)
    (hx1 : s.readReg64 Reg.x1 = ptsPtr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 pts.length)
    (hP : P = (memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTableAt b ∗
      tokenInitAt b ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        ((polyOf A out (lagrangePreparePure pts) ∗ ptSliceAt ptsPtr pts ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt fsp lagrangePrepareStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  refine call_panic_sepWPp_fbl hcall
    (x := { out := out, ptsPtr := ptsPtr, pts := pts, hlen_bound := hlen_bound })
    (φ := s.readReg64 Reg.x0 = out ∧
      s.readReg64 Reg.x1 = ptsPtr ∧
      s.readReg64 Reg.x2 = BitVec.ofNat 64 pts.length)
    (T := memRegion out 24 ∗ ptSliceAt ptsPtr pts ∗ reduceTableAt b ∗
      tokenInitAt b ∗ A.pool ∗ stackAt fsp lagrangePrepareStack)
    hpc hrun hsp_al hlr htr
    (by simp only [lagrangePrepareSpec, hsp_eq])
    ⟨hx0, hx1, hx2⟩
    hP
    (fun _ => rfl)
    (fun _ _ _ _ hm => by simp [lagrangePrepareSpec, satisfies_pure_sepConj] at hm)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  have hspf' : sf.sp = fsp := hspf.trans hsp_eq
  conv => arg 4; simp only [lagrangePrepareSpec, hsp_eq, sepConj_assoc]
  apply SepWPp.pure_left
  intro htrf
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf hpcf hrunf hspf' hcsf (htrf.trans htr))

theorem call_lagrangeComplete_sepWPp {b : BitVec 64} {ext : String → Option (State → State)}
    {ret_pc ret fsp coeffsPtr ptsPtr : BitVec 64} {self : Poly} {pts : List Pt} {i : Nat}
    {s0 s : State} {F P R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (hb : b &&& 0xfff#64 = 0#64)
    (hi : i < pts.length)
    (hself_bound : 2 * self.coefficients.length < 2 ^ 64)
    (hpts_bound : 4 * pts.length < 2 ^ 64)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : (fsp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = coeffsPtr)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 self.coefficients.length)
    (hx2 : s.readReg64 Reg.x2 = ptsPtr)
    (hx3 : s.readReg64 Reg.x3 = BitVec.ofNat 64 pts.length)
    (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 i)
    (hP : P = (gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
      tokenInitAt b ∗ reduceTableAt b ∗ stackAt fsp lagrangeCompleteStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      sf.trace = s0.trace →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret sf
        ((gf16SliceAt coeffsPtr (lagrangeCompletePure self pts i).coefficients ∗
          ptSliceAt ptsPtr pts ∗ tokenInitAt b ∗ reduceTableAt b ∗
          stackAt fsp lagrangeCompleteStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, beq_iff_eq.mp hfsp_al]
  refine SepWPp.call_frame hcall
    (x := { coeffsPtr := coeffsPtr, ptsPtr := ptsPtr, self := self, pts := pts, i := i })
    (φ := b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 Reg.x0 = coeffsPtr ∧
      s.readReg64 Reg.x1 = BitVec.ofNat 64 self.coefficients.length ∧
      s.readReg64 Reg.x2 = ptsPtr ∧
      s.readReg64 Reg.x3 = BitVec.ofNat 64 pts.length ∧
      s.readReg64 Reg.x4 = BitVec.ofNat 64 i ∧
      i < pts.length ∧
      2 * self.coefficients.length < 2 ^ 64 ∧
      4 * pts.length < 2 ^ 64)
    (T := gf16SliceAt coeffsPtr self.coefficients ∗ ptSliceAt ptsPtr pts ∗
      tokenInitAt b ∗ reduceTableAt b ∗ stackAt fsp lagrangeCompleteStack)
    hpc hrun hsp_al hlr
    (by simp only [lagrangeCompleteSpec, hsp_eq])
    ⟨hb, hx0, hx1, hx2, hx3, hx4, hi, hself_bound, hpts_bound⟩
    hP
    (fun _ _ _ _ hm => by simp [lagrangeCompleteSpec, satisfies_pure_sepConj] at hm)
    (fun _ _ hm => by simp [lagrangeCompleteSpec, satisfies_pure_sepConj] at hm)
    (fun sf hpcf hrunf hspf hcsf => ?_)
  have hspf' : sf.sp = fsp := hspf.trans hsp_eq
  conv => arg 4; simp only [lagrangeCompleteSpec, hsp_eq, sepConj_assoc]
  apply SepWPp.pure_left
  intro htrf
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf hpcf hrunf hspf' hcsf (htrf.trans htr))

theorem pull_pure4 (P1 P2 P3 : SepProp) (φ : Prop) (Q : SepProp) :
    P1 ∗ P2 ∗ P3 ∗ ⌜φ⌝ ∗ Q = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 ∗ Q := by
  ac_rfl

theorem polyOf_prepare_unfold (A : RustAlloc) (fsp : BitVec 64) (ones : List Pt) :
    polyOf A (fsp + 656#64) (lagrangePreparePure ones) ⊢
      ∃∗ prepCap : BitVec 64, ∃∗ prepPtr : BitVec 64,
        ⌜ones.length + 1 ≤ prepCap.toNat ∧ prepCap.toNat * 2 < 2 ^ 63 ∧ prepPtr ≠ 0#64 ∧ prepCap ≠ 0#64⌝ ∗
        ((fsp + 656#64) ↦₆₄ prepCap) ∗
        ((fsp + 664#64) ↦₆₄ prepPtr) ∗
        ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
        A.live prepPtr (prepCap.toNat * 2) 2 ∗
        gf16SliceAt prepPtr (lagrangePreparePure ones).coefficients ∗
        memRegion (prepPtr + BitVec.ofNat 64 ((ones.length + 1) * 2))
          ((prepCap.toNat - (ones.length + 1)) * 2) := by
  have h664 : (fsp + 656#64) + 8#64 = fsp + 664#64 := by bv_omega
  have h672 : (fsp + 656#64) + 16#64 = fsp + 672#64 := by bv_omega
  have hlen : (lagrangePreparePure ones).coefficients.length = ones.length + 1 :=
    lagrangePreparePure_length ones
  rw [LagrangePrepare.polyOf_eq A (fsp + 656#64) (lagrangePreparePure ones), h664, h672]
  apply Entails.sepExists_elim; intro prepCap
  apply Entails.sepExists_elim; intro prepPtr
  apply Entails.sepExists_right prepCap
  apply Entails.sepExists_right prepPtr
  rw [pull_pure4]
  apply Entails.pure_left
  rintro ⟨hle, hbound, hptr⟩
  rw [hlen] at hle
  have hcap_ne : prepCap ≠ 0#64 := by
    intro h0; subst h0; change ones.length + 1 ≤ 0 at hle; omega
  have hcap_ne' : prepCap ≠ 0 := hcap_ne
  refine Entails.pure_right ⟨hle, hbound, hptr, hcap_ne⟩ ?_
  simp only [hcap_ne', ↓reduceIte, hlen, sepConj_assoc]
  exact Entails.refl _

theorem ofNat_succ_ne_zero {n : Nat} (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (n + 1) == 0#64) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have heq := beq_iff_eq.mp h
  bv_omega

theorem ofNat_pos_ne_zero {n : Nat} (hpos : 0 < n) (hb : n ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 n == 0#64) = false ∧
    (BitVec.ofNat 64 (2 * n) == 0#64) = false := by
  refine ⟨?_, ?_⟩
  · apply Bool.eq_false_iff.mpr; intro h; have heq := beq_iff_eq.mp h; bv_omega
  · apply Bool.eq_false_iff.mpr; intro h; have heq := beq_iff_eq.mp h; bv_omega

theorem stackAt_complete_to_alloc (fsp : BitVec 64) :
    stackAt fsp lagrangeCompleteStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - lagrangeCompleteStack) ⊢
      stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack) := by
  rw [← stackAt_lagrangePrepare_split_complete fsp,
      stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

theorem stackAt_alloc_to_prepare (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗
      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
        (lagrangePrepareStack - allocHookStack) ⊢
      stackAt fsp lagrangePrepareStack := by
  rw [← stackAt_lagrangePrepare_split_alloc fsp]
  exact Entails.refl _

/-! ## 3. Single Iteration of the Lagrange Basis Loop (`0x6b3a4..0x6b490`, `+4128 -> +4128 / +4368`) -/

/-- Sub-step 1 of the Lagrange basis loop (`0x6b3a4..0x6b3d4`, `+4128 -> +4176`):
calls `lagrange_interpolate_prepare`, unfolds the resulting `Poly`, and calls
`lagrange_interpolate_complete`. -/
theorem lagrangeBasisLoop_prep_comp_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hi_lt : i < ones.length)
    (s0 s : State) (fsp xsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hcont : ∀ s1 prepCap prepPtr,
      ones.length + 1 ≤ prepCap.toNat →
      prepCap.toNat * 2 < 2 ^ 63 →
      prepPtr ≠ 0#64 →
      prepCap ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4176#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 i →
      s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x23 = BitVec.ofNat 64 (ones.length + 1) →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = prepPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         ptSliceAt xsPtr ones ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         reduceTableAt b ∗
         tokenInitAt b ∗
         stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack) ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ptSliceAt xsPtr ones ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       reduceTableAt b ∗
       tokenInitAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hprep_call := lagrangePrepare_ok b hb A ext hA
  have hcomp_call := lagrangeComplete_ok b ext
  have hprep_addr := nextChunk_lagrangePrepare_addr b (Rust.withPanics ext)
  have hcomp_addr := nextChunk_lagrangeComplete_addr b (Rust.withPanics ext)
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1020 48
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hprep_call hcomp_call hprep_addr hcomp_addr hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName)
  wp_steps
  refine SepWP.done (by rw [hprep_addr]; wp_norm_goal) (by wp_norm_lhs) ?_
  refine call_lagrangePrepare_sepWPp hprep_call (by omega)
    (ret_pc := entry + 4144#64) (fsp := fsp) (out := fsp + 656#64) (ptsPtr := xsPtr) (pts := ones)
    (by rw [hprep_addr]; wp_norm_goal)
    (by wp_norm_lhs)
    (by simp only [wp_norm, hsp])
    hfsp_align
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, htrace])
    (by simp only [wp_norm, hsp])
    (by simp only [wp_norm, hx20])
    (by simp only [wp_norm, hx22])
    (by sep_focus) ?_
  intro sfPrep hpcPrep hrunPrep hspPrep hcsPrep htrPrep
  rcases hcsPrep with ⟨hcsPrep_19, hcsPrep_20, hcsPrep_21, hcsPrep_22, hcsPrep_23,
    hcsPrep_24, hcsPrep_25, hcsPrep_26, hcsPrep_27, hcsPrep_28, hcsPrep_29, hcsPrep_vregs⟩
  refine SepWPp.weaken_pre
    (sepConj_mono_fbl (sepConj_mono_fbl (polyOf_prepare_unfold A fsp ones) (Entails.refl _)) (Entails.refl _)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro prepCap
  apply SepWPp.exists_elim; intro prepPtr
  apply SepWPp.pure_left; rintro ⟨hprep_le, hprep_bound, hprep_ptr, hprep_cap⟩
  apply SepWPp.of_sepWP (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangeCompleteName)
  wp_steps
  refine SepWP.done (by rw [hcomp_addr]; wp_norm_goal) (by wp_norm_lhs) ?_
  rw [stackAt_lagrangePrepare_split_complete fsp]
  refine call_lagrangeComplete_sepWPp hcomp_call hb hi_lt
    (self := lagrangePreparePure ones) (pts := ones) (i := i)
    (ret_pc := entry + 4176#64) (fsp := fsp) (coeffsPtr := prepPtr) (ptsPtr := xsPtr)
    (by rw [lagrangePreparePure_length]; omega)
    (by omega)
    (by rw [hcomp_addr]; wp_norm_goal)
    (by wp_norm_lhs)
    (by simp only [wp_norm, hspPrep])
    hfsp_align
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, htrPrep])
    (by wp_norm_lhs)
    (by simp only [wp_norm, lagrangePreparePure_length])
    (by simp only [wp_norm, hcsPrep_20, hx20])
    (by simp only [wp_norm, hcsPrep_22, hx22])
    (by simp only [wp_norm, hcsPrep_19, hx19])
    (by sep_focus) ?_
  intro sfComp hpcComp hrunComp hspComp hcsComp htrComp
  rcases hcsComp with ⟨hcsComp_19, hcsComp_20, hcsComp_21, hcsComp_22, hcsComp_23,
    hcsComp_24, hcsComp_25, hcsComp_26, hcsComp_27, hcsComp_28, hcsComp_29, hcsComp_vregs⟩
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont sfComp prepCap prepPtr hprep_le hprep_bound hprep_ptr hprep_cap
      hpcComp hrunComp hspComp htrComp
      (by rw [hcsComp_vregs]; simp only [arm64_norm, wp_norm, hcsPrep_vregs, *])
      (by rw [hcsComp_19]; simp only [wp_norm, hcsPrep_19, hx19])
      (by rw [hcsComp_20]; simp only [wp_norm, hcsPrep_20, hx20])
      (by rw [hcsComp_21]; simp only [wp_norm, hcsPrep_21])
      (by rw [hcsComp_22]; simp only [wp_norm, hcsPrep_22, hx22])
      (by rw [hcsComp_23]; simp only [wp_norm])
      (by rw [hcsComp_24]; simp only [wp_norm, hcsPrep_24])
      (by rw [hcsComp_25]; simp only [wp_norm, hcsPrep_25])
      (by rw [hcsComp_26]; simp only [wp_norm])
      (by rw [hcsComp_27]; simp only [wp_norm, hcsPrep_27])
      (by rw [hcsComp_28]; simp only [wp_norm, hcsPrep_28])
      (by rw [hcsComp_29]; simp only [wp_norm, hcsPrep_29]))

/-- Sub-step 2 of the Lagrange basis loop (`0x6b3d4..0x6b454`, `+4176 -> +4304`):
allocates the `2 * n`-byte `Poly` coefficient buffer, `memcpy`s the tail coefficients `[1..n]`,
and `__rust_dealloc`s the temporary `prepPtr` buffer. -/
theorem lagrangeBasisLoop_copy_free_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (s0 s : State) (fsp prepCap prepPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hprep_le : ones.length + 1 ≤ prepCap.toNat)
    (hprep_bound : prepCap.toNat * 2 < 2 ^ 63)
    (hprep_ptr : prepPtr ≠ 0#64)
    (hprep_cap : prepCap ≠ 0#64)
    (u216 u224 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (ones.length + 1))
    (hx26 : s.readReg64 .x26 = prepPtr)
    (hcont : ∀ s1 newPtr,
      newPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4304#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗
         ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 224#64) ↦₆₄ newPtr) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 656#64) ↦₆₄ prepCap) ∗
       ((fsp + 664#64) ↦₆₄ prepPtr) ∗
       A.live prepPtr (prepCap.toNat * 2) 2 ∗
       gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
       memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗
       ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  have hshim := hA.shim_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  simp only [rustAllocSpec] at halloc
  have hmemcpy := hA.session_memcpy_ok_at polyNextChunkName
    (num% (ls_off% "memcpy" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
  simp only [sessionMemcpySpec] at hmemcpy
  have hdealloc := hA.dealloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  have hpanic4592 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4592 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1050 128
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hdealloc hpanic4592 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  obtain ⟨c0, hc0⟩ := lagrangeComplete_prepare_head_tail ones i
  rw [hc0]
  have hn1_ne0 := ofNat_succ_ne_zero hbound
  obtain ⟨hn_ne0, h2n_ne0⟩ := ofNat_pos_ne_zero hn_pos hbound
  obtain ⟨hmsb1, hmsb2⟩ := bit62_shl_one_false hbound
  have hult := ult_max_2n_false hbound
  have hlayout2n : LayoutOk (2 * ones.length) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * ones.length)).toNat = 2 * ones.length :=
    Nat.mod_eq_of_lt (by omega)
  apply SepWPp.of_sepWP (mid := entry + 4228#64)
  apply SepWP.fold (gf16SliceAt_cons_memRegion2 prepPtr c0 _) (by sep_focus)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr_oom
    refine hpanic4592 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm]; rw [‹sf.trace = s.trace›, htrace] at htr_oom; exact htr_oom)
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc, hx23, h2n_toNat]
    apply sepWPp_pure_mid; intro ⟨_, htr_alloc⟩
    have hcond_oom : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom
    have hsp_sf1 : sf_1.sp = fsp := by rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
    have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ones.length := by
      simp only [wp_norm, h_15, h_5, hx23]
    have hx23_sf1 : sf_1.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (2 * ones.length) := by
      simp only [wp_norm, h_16, h_6, hx23]
    have hx26_sf1 : sf_1.readReg64 (Reg.gpr 26#5) = prepPtr := by
      simp only [wp_norm, h_19, h_9, hx26]
    have hlen_interp : (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients).length = 2 * ones.length := by
      simp [lagrangeInterpolatePtPure_length]
    apply SepWPp.of_sepWP (mid := entry + 4280#64)
    wp_steps; wp_apply
    refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
    have hrecomb := memRegion_recombine_prepare prepPtr prepCap ones.length
      (gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) hlen_interp hprep_le hprep_bound
    have hprep_cap_bne : ¬(prepCap == 0#64) = true := by simpa [beq_iff_eq] using hprep_cap
    have hcap_shl := shl_one_cap_toNat_nat hprep_bound
    have hsp_sf2 : sf_2.sp = fsp := by rw [‹sf_2.sp = _›]; simp only [wp_norm, hsp_sf1]
    have hx26_sf2 : sf_2.readReg64 (Reg.gpr 26#5) = prepPtr := by
      rw [h_29]; simp only [wp_norm, hx26_sf1]
    apply SepWPp.of_sepWP (mid := entry + 4304#64)
    apply SepWP.fold hrecomb (by sep_focus)
    wp_steps; wp_apply
    refine SepWP.done hpc_sf_3 hrun_sf_3 ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [hsp_sf2]; ac_rfl))
      (hcont sf_3 (sf_1.readReg64 (Reg.gpr 0#5)) hoom
        hpc_sf_3 hrun_sf_3
        (by rw [‹sf_3.sp = _›, hsp_sf2])
        (by rw [hpost_1, hpost, htr_alloc, ‹sf.trace = s.trace›, htrace])
        (by simp only [arm64_norm, wp_norm, *])
        (by rw [h_33, h_22, h_12, h_2])
        (by rw [h_34, h_23, h_13, h_3])
        (by rw [h_35, h_24, h_14, h_4])
        (by rw [h_36, h_25]; simp only [wp_norm, hx22_sf1])
        (by rw [h_38, h_27, h_17, h_7])
        (by rw [h_39, h_28, h_18, h_8])
        (by rw [h_41, h_30, h_20, h_10])
        (by rw [h_42, h_31, h_21, h_11])
        (by rw [hcs_sf_2, hcs_sf_1, hcs_sf, hpost_sf]))

/-- Sub-step 3 of the Lagrange basis loop (`0x6b454..0x6b490`, `+4304 -> +4128 / +4368`):
stores the `Poly` header into `curBasis`, increments `i`, and branches back to `+4128` or exits to `+4368`. -/
theorem lagrangeBasisLoop_tail_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555)
    (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (fsp curBasis newPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hnew_ptr : newPtr ≠ 0#64)
    (u656 u664 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s.readReg64 .x21 = curBasis)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
      s1.pc = (if rem == 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4368#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4128#64) →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = curBasis + 24#64 →
      s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗
         ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗
         ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.live newPtr (2 * ones.length) 2 ∗
       (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
       memRegion curBasis 24 ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 224#64) ↦₆₄ newPtr) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗
       ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < ones.length := List.length_pos_iff.mpr hones_ne
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x10d0 64
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  obtain ⟨hcmn1, hcmn2, hcmn3, hcmn4⟩ := adds_one_ne_zero (i := i) (by omega)
  have hstur_addr : (fsp + 1104#64) + 18446744073709551568#64 = fsp + 1056#64 := by bv_omega
  have hpoly_intro := polyOf_of_pointsToBytes A curBasis newPtr
    (lagrangeInterpolatePtPure ones i) ones.length hn_pos (by omega) hnew_ptr
    (lagrangeInterpolatePtPure_length ones i)
  have hmem24 := polyHeader_entails_memRegion24_off fsp
    (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 (ones.length + 1))
  apply SepWPp.of_sepWP (mid := entry + 4348#64)
  apply SepWP.fold (Entails.of_eq (memRegion_split_polyHeader_fbl curBasis)) (by sep_focus)
  apply sepWP_exists_left_sep; intro uBasis16
  apply sepWP_exists_left_sep; intro uBasis8
  apply sepWP_exists_left_sep; intro uBasis0
  wp_steps
  apply SepWP.fold hpoly_intro (by sep_focus)
  apply SepWP.fold hmem24 (by sep_focus)
  refine SepWP.done
    (by simp only [wp_norm, hx19, hcmn1, hcmn2, hcmn3, hcmn4, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  cases rem with
  | zero =>
    have hi1_eq : i + 1 = ones.length := by omega
    have hcmp_eq :
        (BitVec.ofNat 64 ones.length == BitVec.ofNat 64 i + 1#64) = true ∧
        (BitVec.ofNat 64 ones.length != BitVec.ofNat 64 i + 1#64) = false ∧
        (BitVec.ofNat 64 ones.length - (BitVec.ofNat 64 i + 1#64) == 0#64) = true := by
      rw [ofNat_add_one_eq_succ_fb, hi1_eq]
      simp [BitVec.sub_self]
    rcases hcmp_eq with ⟨hcmp1, hcmp2, hcmp3⟩
    apply SepWPp.of_sepWP (mid := entry + 4368#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq, bne_self_eq_false,
            BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length)
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq, bne_self_eq_false,
              BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hi1_eq])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx22])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx29]))
  | succ r =>
    have hi1_ne : ones.length ≠ i + 1 := by omega
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := ofNat_ne_ofNat_false hi1_ne (by omega) (by omega)
    apply SepWPp.of_sepWP (mid := entry + 4128#64)
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
            Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (BitVec.ofNat 64 ones.length) newPtr
        (BitVec.ofNat 64 ones.length) newPtr (BitVec.ofNat 64 ones.length)
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb, hcmp1, hcmp2, hcmp3,
              Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        rfl
        (by simp only [wp_norm, hx19, ofNat_add_one_eq_succ_fb])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx21])
        (by simp only [wp_norm, hx22])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm])
        (by simp only [wp_norm, hx29]))

/-- Combined single iteration of the Lagrange basis loop (`0x6b3a4..0x6b490`, `+4128 -> +4128 / +4368`). -/
theorem lagrangeBasisLoop_step_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (fsp xsPtr curBasis : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i) (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = curBasis) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
      s1.pc = (if rem == 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4368#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4128#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 (i + 1) → s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = curBasis + 24#64 → s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt xsPtr ones ∗ polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis 24 ∗ memRegion (fsp + 656#64) 24 ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeBasisLoop_prep_comp_sepWPp hA hb i ones hones_ne hbound (by omega)
      s0 s fsp xsPtr hfsp_align
      (memRegion curBasis 24 ∗ ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc hrun hsp htrace hx19 hx20 hx22 ?_)
  intro s1 prepCap prepPtr hprep_le hprep_bound hprep_ptr hprep_cap
    hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  refine SepWPp.weaken_pre
    (by
      have hst := stackAt_complete_to_alloc fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp lagrangeCompleteStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - lagrangeCompleteStack)) ∗
        (A.pool ∗ ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         A.live prepPtr (prepCap.toNat * 2) 2 ∗
         gf16SliceAt prepPtr (lagrangeCompletePure (lagrangePreparePure ones) ones i).coefficients ∗
         memRegion (prepPtr + BitVec.ofNat 64 (2 * (ones.length + 1))) (2 * (prepCap.toNat - (ones.length + 1))) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         reduceTableAt b ∗ tokenInitAt b ∗ memRegion curBasis 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    (lagrangeBasisLoop_copy_free_sepWPp hA i ones hones_ne hbound
      s0 s1 fsp prepCap prepPtr hfsp_align hprep_le hprep_bound hprep_ptr hprep_cap u216 u224
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ptSliceAt xsPtr ones ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ memRegion curBasis 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx23_1 hx26_1 ?_)
  intro s2 newPtr hnew_ptr hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2
  refine SepWPp.weaken_pre
    (by
      have hst := stackAt_alloc_to_prepare fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack)) ∗
        (A.live newPtr (2 * ones.length) 2 ∗
         (newPtr ↦ₛ gf16SliceBytes (lagrangeInterpolatePtPure ones i).coefficients) ∗
         memRegion curBasis 24 ∗
         ((fsp + 656#64) ↦₆₄ prepCap) ∗ ((fsp + 664#64) ↦₆₄ prepPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (ones.length + 1)) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗ ((fsp + 224#64) ↦₆₄ newPtr) ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         A.pool ∗ ptSliceAt xsPtr ones ∗ reduceTableAt b ∗ tokenInitAt b ∗ Frame) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl)))
    (lagrangeBasisLoop_tail_sepWPp rem i ones hones_ne hbound hsum
      s0 s2 fsp curBasis newPtr hfsp_align hnew_ptr prepCap prepPtr u1040 u1048 u1056
      (A.pool ∗ ptSliceAt xsPtr ones ∗ reduceTableAt b ∗ tokenInitAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc2 hrun2 hsp2 htr2
      (by rw [hx19_2, hx19_1]) (by rw [hx21_2, hx21_1, hx21]) hx22_2 (by rw [hx29_2, hx29_1, hx29]) ?_)
  intro s3 u216' u224' u1040' u1048' u1056'
    hpc3 hrun3 hsp3 htr3 hvregs3 hx19_3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx27_3 hx28_3 hx29_3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s3 u216' u224' u1040' u1048' u1056'
      hpc3 hrun3 hsp3 htr3 (by rw [hvregs3, hvregs2, hvregs1])
      hx19_3 (by rw [hx20_3, hx20_2, hx20_1]) hx21_3 hx22_3
      (by rw [hx24_3, hx24_2, hx24_1]) (by rw [hx25_3, hx25_2, hx25_1])
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-- Pure Lagrange basis `[(List.range ones.length).map (lagrangeInterpolatePtPure ones)]`. -/
def lagrangeBasisPure (ones : List Pt) : List Poly :=
  (List.range ones.length).map (lagrangeInterpolatePtPure ones)

/-- Suffix of `lagrangeBasisPure ones` starting at index `i` of length `k`. -/
def lagrangeBasisFrom (ones : List Pt) : Nat → Nat → List Poly
  | _, 0 => []
  | i, k + 1 => lagrangeInterpolatePtPure ones i :: lagrangeBasisFrom ones (i + 1) k

theorem lagrangeBasisFrom_eq_map_range' (ones : List Pt) (i k : Nat) :
    lagrangeBasisFrom ones i k = (List.range' i k).map (lagrangeInterpolatePtPure ones) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [lagrangeBasisFrom, List.range', ih]

theorem lagrangeBasisFrom_zero_eq (ones : List Pt) :
    lagrangeBasisFrom ones 0 ones.length = lagrangeBasisPure ones := by
  rw [lagrangeBasisFrom_eq_map_range', ← List.range_eq_range']; rfl

theorem memRegion_split_24_succ (curBasis : BitVec 64) (rem : Nat)
    (hbound : 24 * (rem + 1) < 2 ^ 64) :
    memRegion curBasis (24 * (rem + 1)) =
      memRegion curBasis 24 ∗ memRegion (curBasis + 24#64) (24 * rem) := by
  have h24 : 24 * (rem + 1) = 24 + 24 * rem := by omega
  exact ProofLib.memRegion_split' (b := curBasis) (n := 24) (k := 24 * rem)
    (b' := curBasis + 24#64) h24 rfl (by omega)

/-- Full Lagrange basis loop (`0x6b3a4..0x6b490`, `+4128 -> +4368`) over `rem + 1` iterations. -/
theorem lagrangeBasisLoop_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (rem i : Nat) (ones : List Pt) (hones_ne : ones ≠ [])
    (hbound : ones.length ≤ 0x0555555555555555) (hsum : i + (rem + 1) = ones.length)
    (s0 s : State) (fsp xsPtr curBasis : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4128#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i) (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = curBasis) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ones.length)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u216' u224' u1040' u1048' u1056',
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4368#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = xsPtr → s1.readReg64 .x22 = BitVec.ofNat 64 ones.length →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt xsPtr ones ∗
         polyListOf A curBasis (lagrangeBasisFrom ones i (rem + 1)) ∗
         memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt xsPtr ones ∗ memRegion curBasis (24 * (rem + 1)) ∗
       memRegion (fsp + 656#64) 24 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 ones.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  induction rem generalizing i s curBasis u216 u224 u1040 u1048 u1056 Frame with
  | zero =>
    rw [memRegion_split_24_succ curBasis 0 (by omega), Nat.mul_zero, ProofLib.memRegion_zero, sepConj_emp]
    refine lagrangeBasisLoop_step_sepWPp hA hb 0 i ones hones_ne hbound hsum
      s0 s fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056 Frame R
      hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 ?_
    intro s1 u216' u224' u1040' u1048' u1056'
      hpc1 hrun1 hsp1 htr1 hvregs1 _ hx20_1 _ hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    have hpoly_one :
        polyListOf A curBasis (lagrangeBasisFrom ones i 1) =
          polyOf A curBasis (lagrangeInterpolatePtPure ones i) := by
      simp [lagrangeBasisFrom, polyListOf, arrayAt]
    rw [← hpoly_one]
    exact hcont s1 u216' u224' u1040' u1048' u1056'
      hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  | succ r ih =>
    rw [memRegion_split_24_succ curBasis (r + 1) (by omega)]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (lagrangeBasisLoop_step_sepWPp hA hb (r + 1) i ones hones_ne hbound hsum
        s0 s fsp xsPtr curBasis hfsp_align u216 u224 u1040 u1048 u1056
        (memRegion (curBasis + 24#64) (24 * (r + 1)) ∗ Frame) R
        hpc hrun hsp htrace hx19 hx20 hx21 hx22 hx29 ?_)
    intro s1 u216' u224' u1040' u1048' u1056'
      hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (ih (i + 1) (by omega) s1 (curBasis + 24#64) u216' u224' u1040' u1048' u1056'
        (polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗ Frame)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx29_1 ?_)
    intro s2 u216'' u224'' u1040'' u1048'' u1056''
      hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2
    have hpoly_cons :
        polyListOf A curBasis (lagrangeBasisFrom ones i (r + 2)) =
          polyOf A curBasis (lagrangeInterpolatePtPure ones i) ∗
          polyListOf A (curBasis + 24#64) (lagrangeBasisFrom ones (i + 1) (r + 1)) := rfl
    refine SepWPp.weaken_pre (by rw [hpoly_cons]; exact Entails.of_eq (by ac_rfl))
      (hcont s2 u216'' u224'' u1040'' u1048'' u1056''
        hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx20_2 hx22_2
        (by rw [hx24_2, hx24_1]) (by rw [hx25_2, hx25_1])
        (by rw [hx27_2, hx27_1]) (by rw [hx28_2, hx28_1]) hx29_2)

end CryptoVerification.SpqrV1.Poly.NextChunk
