/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
public import Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim
public import VCVio.CryptoFoundations.ReplayForkCost
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
# Forking-lemma reduction from `GapSigEufCmaRo` to standalone `GapDH`

**Checked by Lean.** Reduces XEdDSA EUF-CMA unforgeability in the SHA-512 random-oracle model with
an X25519 decisional Diffie-Hellman oracle (`GapSigEufCmaRo`) to standalone `GapDH` via conditional
challenge-digest lifting (`xeddsaModLoss`), 2-special soundness with clamped `±a` scalar recovery,
and a replay-forking reduction (`GapSigEufCmaRoBoundQuad` and `GapSigEufCmaRoBound`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 512

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction

open OracleComp OracleSpec
open scoped MeasureTheory ENNReal OracleSpec.PrimitiveQuery
open MeasureTheory (
  Measure lintegral_mono lintegral_add_right lintegral_const lintegral_const_mul measure_ne_top
)
open ProbabilityTheory (uniformOn_univ_prod map_uniformOn_univ_of_bijective)
open _root_.SignalPqxdh (
  Bytes Primitives PrimQuery primSpec PrimBaseSpec primImpl primBaseImpl isPrimQuery
  DdhQuery gapDhOracleSpec SigQuery sigOracleSpec sigAndDdhSpec
  GapDhAdv gapDhExp GapDH WellFormedPrimitivesδ onCurveKey
  clampScalar25519 fitBytesRef fitBytesRef_length scalarIsInRange
  word256ToBytes sampleBytes32 sampleScalar32 sampleRandom64
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 l25519_pos l25519_lt_two_pow_253
  natOfBytesLE bytesOfNatLE bytesOfNatLE_length natOfBytesLE_bytesOfNatLE
  encodeScalarBytes decodeScalarBytes encodeScalarBytes_length decodeScalarBytes_encodeScalarBytes
  xeddsaHashPrefix xeddsaHashPrefix_length clearSignBit32 clearSignBit32_length
  scalarIsInRange_clearSignBit32_xeddsaHashPrefix append_ne_xeddsaHashPrefix_append
  clampedScalarZMod recoverClampedScalar recoverClampedScalar_length recoverClampedScalar_spec
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  edDummy edBaseMul
  sha512RoSpec sha512RoBaseImpl Sha512RoComp sha512RoImpl
  xeddsaSignRo xeddsaVerifyRo primRoStep primRoImpl primBaseRoImpl
  XeddsaRomOracleSpec isRomPrimQuery isRomPrimVerifyQuery isRomPrimSigSignQuery
  isRomDirectRoQuery isRomSigChalQuery isRomDdhChalQuery
  GapSigEufCmaRoAdv gapSigEufCmaRoExp GapSigEufCmaRo
  XeddsaCurveWitness XeddsaCurveLaws
  wideRem deltaWide xeddsaChalBudget xeddsaSimLoss xeddsaModLoss
  GapSigEufCmaRoBoundQuad GapSigEufCmaRoBound
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim (
  xeddsaSimSign gapSigEufCmaSimExpOnPk gapSigEufCmaSimExpAt gapSigEufCmaSimExp
  gapSigEufCmaRo_le_sim
)

/-! ## Real-algebra bounds for the forking inequality -/

theorem quad_le_of_le_of_nonneg_rhs {x y Q c B : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hy : y * (y / Q - c) ≤ B) :
    x * (x / Q - c) ≤ B := by
  by_cases hneg : x / Q - c ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hx hneg).trans hB
  · push Not at hneg
    have hdiv_le : x / Q - c ≤ y / Q - c := by
      have : x / Q ≤ y / Q := div_le_div_of_nonneg_right hxy hQ.le
      linarith
    exact (mul_le_mul hxy hdiv_le hneg.le (hx.trans hxy)).trans hy

theorem quad_to_sqrt_bound {eps' Q L G : ℝ}
    (_heps : 0 ≤ eps') (hQ : 0 < Q) (hL : 0 < L) (hG : 0 ≤ G)
    (hquad : eps' * (eps' / Q - 1 / L) ≤ 2 * G) :
    eps' ≤ Real.sqrt (2 * Q * G) + Q / L := by
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hmul : eps' * (eps' - Q / L) ≤ 2 * Q * G := by
    have h1 : Q * (eps' * (eps' / Q - 1 / L)) ≤ Q * (2 * G) :=
      mul_le_mul_of_nonneg_left hquad hQ.le
    have h2 : Q * (eps' * (eps' / Q - 1 / L)) = eps' * (eps' - Q / L) := by
      calc Q * (eps' * (eps' / Q - 1 / L))
          = eps' * (Q * (eps' / Q) - Q * (1 / L)) := by ring
        _ = eps' * (eps' - Q / L) := by
            rw [mul_div_cancel₀ eps' hQne, mul_one_div]
    linarith
  have h2QG : 0 ≤ 2 * Q * G := by positivity
  have hR_nonneg : 0 ≤ Real.sqrt (2 * Q * G) := Real.sqrt_nonneg _
  have hR_sq : Real.sqrt (2 * Q * G) ^ 2 = 2 * Q * G := Real.sq_sqrt h2QG
  have hQL_nonneg : 0 ≤ Q / L := div_nonneg hQ.le hL.le
  nlinarith [mul_nonneg hR_nonneg hQL_nonneg]

/-- Derives the closed-form square-root bound `GapSigEufCmaRoBound` from `GapSigEufCmaRoBoundQuad`. -/
theorem gapSigEufCmaRoBound_of_quad (hQuad : GapSigEufCmaRoBoundQuad) :
    GapSigEufCmaRoBound := by
  intro P hWF hCurve A hA
  obtain ⟨B₂, hB₂_bound, hB₂_ddh, hB₂_prim, hB₂_quad⟩ := hQuad P hWF hCurve A hA
  refine ⟨B₂, hB₂_bound, hB₂_ddh, hB₂_prim, ?_⟩
  set q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
  set eps' := max 0
    (GapSigEufCmaRo P P.isValidDhTriple A - xeddsaSimLoss A.q_sig q_H - xeddsaModLoss q_H)
  have hQ : 0 < (q_H : ℝ) + 1 := by positivity
  have hL : 0 < (l25519 : ℝ) := Nat.cast_pos.mpr l25519_pos
  have hG : 0 ≤ GapDH P P.isValidDhTriple P.pow8 B₂ := ENNReal.toReal_nonneg
  have hsqrt := quad_to_sqrt_bound (le_max_left _ _) hQ hL hG hB₂_quad
  have hle_max :
      GapSigEufCmaRo P P.isValidDhTriple A - xeddsaSimLoss A.q_sig q_H - xeddsaModLoss q_H ≤
        eps' := le_max_right _ _
  linarith

/-! ## Conditional 64-byte preimage sampler and `deltaWide` TV bound -/

def wideQuot : ℕ :=
  2 ^ 512 / l25519

theorem wideQuot_pos : 0 < wideQuot := by
  unfold wideQuot
  have hl : l25519 < 2 ^ 512 :=
    lt_trans l25519_lt_two_pow_253 (Nat.pow_lt_pow_right (by decide) (by decide))
  exact Nat.div_pos (le_of_lt hl) l25519_pos

theorem wideRem_lt_l25519 : wideRem < l25519 :=
  Nat.mod_lt _ l25519_pos

theorem two_pow_512_eq : l25519 * wideQuot + wideRem = 2 ^ 512 :=
  Nat.div_add_mod (2 ^ 512) l25519

instance instNeZeroWideQuot : NeZero wideQuot :=
  ⟨Nat.ne_of_gt wideQuot_pos⟩

instance instNeZeroTwoPow512 : NeZero (2 ^ 512) :=
  ⟨Nat.ne_of_gt (Nat.pow_pos (by decide))⟩

theorem add_mul_lt_two_pow_512_of_lt_wideRem {r q : ℕ}
    (hr : r < wideRem) (hq : q < wideQuot + 1) :
    r + l25519 * q < 2 ^ 512 := by
  have hle : q ≤ wideQuot := Nat.lt_succ_iff.mp hq
  have hmul : l25519 * q ≤ l25519 * wideQuot := Nat.mul_le_mul_left l25519 hle
  calc r + l25519 * q
      < wideRem + l25519 * wideQuot := by omega
    _ = l25519 * wideQuot + wideRem := Nat.add_comm _ _
    _ = 2 ^ 512 := two_pow_512_eq

theorem add_mul_lt_two_pow_512_of_ge_wideRem {r q : ℕ}
    (hr : r < l25519) (hq : q < wideQuot) :
    r + l25519 * q < 2 ^ 512 := by
  have hle : q + 1 ≤ wideQuot := hq
  have hmul : l25519 * (q + 1) ≤ l25519 * wideQuot := Nat.mul_le_mul_left l25519 hle
  have hexp : l25519 * (q + 1) = l25519 * q + l25519 := by ring
  calc r + l25519 * q
      < l25519 * wideQuot + wideRem := by omega
    _ = 2 ^ 512 := two_pow_512_eq

noncomputable def liftChalFin (h : ZMod l25519) : ProbComp (Fin (2 ^ 512)) :=
  if hlt : h.val < wideRem then
    (fun q : Fin (wideQuot + 1) =>
      ⟨h.val + l25519 * q.val, add_mul_lt_two_pow_512_of_lt_wideRem hlt q.isLt⟩) <$>
      ($ᵗ (Fin (wideQuot + 1)))
  else
    (fun q : Fin wideQuot =>
      ⟨h.val + l25519 * q.val, add_mul_lt_two_pow_512_of_ge_wideRem h.val_lt q.isLt⟩) <$>
      ($ᵗ (Fin wideQuot))

/-- Conditional uniform 64-byte little-endian preimage sampler lifting `h : ZMod l25519` into `Bytes`. -/
noncomputable def liftChalTo64 (h : ZMod l25519) : ProbComp Bytes :=
  (fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> liftChalFin h

theorem liftChalFin_mod_eq {h : ZMod l25519} {k : Fin (2 ^ 512)}
    (hk : k ∈ support (liftChalFin h)) :
    (k.val : ZMod l25519) = h := by
  unfold liftChalFin at hk
  split_ifs at hk with hlt
  · rw [support_map] at hk
    obtain ⟨q, _, rfl⟩ := hk
    simp
  · rw [support_map] at hk
    obtain ⟨q, _, rfl⟩ := hk
    simp

theorem liftChalTo64_length {h : ZMod l25519} {w : Bytes}
    (hw : w ∈ support (liftChalTo64 h)) :
    w.length = 64 := by
  unfold liftChalTo64 at hw
  rw [support_map] at hw
  obtain ⟨k, _, rfl⟩ := hw
  exact bytesOfNatLE_length 64 k.val

theorem decodeScalarBytes_fit64_liftChalTo64 {h : ZMod l25519} {w : Bytes}
    (hw : w ∈ support (liftChalTo64 h)) :
    decodeScalarBytes (fitBytesRef 64 w) = h := by
  have hlen : w.length = 64 := liftChalTo64_length hw
  have hfit : fitBytesRef 64 w = w := by simp [fitBytesRef, hlen]
  rw [hfit]
  unfold liftChalTo64 at hw
  rw [support_map] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  unfold decodeScalarBytes
  rw [natOfBytesLE_bytesOfNatLE]
  have hpow : (256 : ℕ) ^ 64 = 2 ^ 512 := by
    rw [show (256 : ℕ) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [hpow, Nat.mod_eq_of_lt k.isLt]
  exact liftChalFin_mod_eq hk

private theorem word256ToBytes_eq_bytesOfNatLE (w : BitVec 256) :
    word256ToBytes w = bytesOfNatLE 32 w.toNat := by
  have hlen1 : (word256ToBytes w).length = 32 := by simp [word256ToBytes]
  have hlen2 : (bytesOfNatLE 32 w.toNat).length = 32 := bytesOfNatLE_length 32 w.toNat
  apply List.ext_getElem (hlen1.trans hlen2.symm)
  intro i hi1 hi2
  simp only [word256ToBytes, List.getElem_ofFn]
  have hgetD : (bytesOfNatLE 32 w.toNat)[i]'hi2 = (bytesOfNatLE 32 w.toNat).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]
  rw [hgetD]
  apply UInt8.toNat_inj.mp
  rw [Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.getD_toNat_eq_div_mod,
    natOfBytesLE_bytesOfNatLE]
  have hw_lt : w.toNat < 256 ^ 32 := by
    have : (256 : ℕ) ^ 32 = 2 ^ 256 := by decide
    rw [this]; exact w.isLt
  have hpow_i : (256 : ℕ) ^ i = 2 ^ (8 * i) := by
    rw [show (256 : ℕ) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [Nat.mod_eq_of_lt hw_lt, Nat.shiftRight_eq_div_pow, hpow_i]
  have hmod_lt : (w.toNat / 2 ^ (8 * i)) % 256 < UInt8.size := Nat.mod_lt _ (by decide)
  rw [UInt8.toNat_ofNat_of_lt' hmod_lt]

private theorem two_pow_256_mul_eq_512 : (2 : ℕ) ^ 256 * 2 ^ 256 = 2 ^ 512 := by
  rw [← Nat.pow_add]

private def pairBitVec256ToFin512 (b1 b2 : BitVec 256) : Fin (2 ^ 512) :=
  ⟨b1.toNat + 2 ^ 256 * b2.toNat, by
    have h1 := b1.isLt
    have h2 := b2.isLt
    calc b1.toNat + 2 ^ 256 * b2.toNat
        < 2 ^ 256 + 2 ^ 256 * b2.toNat := Nat.add_lt_add_right h1 _
      _ = 2 ^ 256 * (b2.toNat + 1) := by ring
      _ ≤ 2 ^ 256 * 2 ^ 256 := Nat.mul_le_mul_left _ h2
      _ = 2 ^ 512 := two_pow_256_mul_eq_512⟩

private theorem pairBitVec256ToFin512_bijective :
    Function.Bijective (Function.uncurry pairBitVec256ToFin512) := by
  let inv : Fin (2 ^ 512) → BitVec 256 × BitVec 256 := fun k =>
    (BitVec.ofNatLT (k.val % 2 ^ 256) (Nat.mod_lt _ (Nat.pow_pos (by decide))),
     BitVec.ofNatLT (k.val / 2 ^ 256) (by
       refine (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr ?_
       rw [two_pow_256_mul_eq_512]
       exact k.isLt))
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · rintro ⟨b1, b2⟩
    have h1 := b1.isLt
    have h2 := b2.isLt
    apply Prod.ext <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [inv, Function.uncurry, pairBitVec256ToFin512, BitVec.toNat_ofNatLT] <;>
      omega
  · intro k
    apply Fin.ext
    simp only [inv, Function.uncurry, pairBitVec256ToFin512, BitVec.toNat_ofNatLT]
    exact Nat.mod_add_div k.val (2 ^ 256)

private theorem bytesOfNatLE_64_pair (b1 b2 : BitVec 256) :
    word256ToBytes b1 ++ word256ToBytes b2 =
      bytesOfNatLE 64 (pairBitVec256ToFin512 b1 b2).val := by
  rw [word256ToBytes_eq_bytesOfNatLE, word256ToBytes_eq_bytesOfNatLE]
  set lhs := bytesOfNatLE 32 b1.toNat ++ bytesOfNatLE 32 b2.toNat
  have hlen : lhs.length = 64 := by simp [lhs]
  rw [← Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.bytesOfNatLE_natOfBytesLE lhs, hlen]
  apply congrArg (bytesOfNatLE 64)
  dsimp only [lhs, pairBitVec256ToFin512]
  rw [Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.natOfBytesLE_append,
    bytesOfNatLE_length, natOfBytesLE_bytesOfNatLE, natOfBytesLE_bytesOfNatLE]
  have hpow : (256 : ℕ) ^ 32 = 2 ^ 256 := by decide
  rw [hpow, Nat.mod_eq_of_lt b1.isLt, Nat.mod_eq_of_lt b2.isLt]

theorem sampleRandom64_evalDist_eq :
    letI : MeasurableSpace Bytes := ⊤
    𝒟[sampleRandom64] =
      𝒟[(fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> ($ᵗ (Fin (2 ^ 512)))] := by
  let _ : MeasurableSpace Bytes := ⊤
  let _ : MeasurableSpace (BitVec 256) := ⊤
  let _ : MeasurableSpace (Fin (2 ^ 512)) := ⊤
  have hpair :
      sampleRandom64 =
        (fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$>
          (Function.uncurry pairBitVec256ToFin512 <$>
            (do let b1 ← $ᵗ (BitVec 256); let b2 ← $ᵗ (BitVec 256); return (b1, b2))) := by
    unfold sampleRandom64 sampleBytes32
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
      Function.uncurry, bytesOfNatLE_64_pair]
  rw [hpair, evalDist_map_of_discrete, evalDist_map_of_discrete, evalDist_map_of_discrete]
  congr 1
  rw [evalDist_pair, SampleableType.evalDist_uniformSample,
    SampleableType.evalDist_uniformSample, ← uniformOn_univ_prod]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete pairBitVec256ToFin512_bijective

noncomputable def liftChalSampleFin : ProbComp (Fin (2 ^ 512)) := do
  let h ← $ᵗ (ZMod l25519)
  liftChalFin h

private theorem div_lt_wideQuot_add_one (k : Fin (2 ^ 512)) :
    k.val / l25519 < wideQuot + 1 := by
  have hw := wideRem_lt_l25519
  have hlt : k.val < l25519 * (wideQuot + 1) := by
    calc k.val
        < 2 ^ 512 := k.isLt
      _ = l25519 * wideQuot + wideRem := two_pow_512_eq.symm
      _ < l25519 * wideQuot + l25519 := Nat.add_lt_add_left hw _
      _ = l25519 * (wideQuot + 1) := by ring
  exact (Nat.div_lt_iff_lt_mul l25519_pos).mpr (by rw [mul_comm]; exact hlt)

private theorem div_lt_wideQuot_of_not_lt_wideRem (k : Fin (2 ^ 512))
    (hge : ¬ k.val % l25519 < wideRem) :
    k.val / l25519 < wideQuot := by
  by_contra hnot
  push Not at hnot
  have hmul : l25519 * wideQuot ≤ l25519 * (k.val / l25519) := Nat.mul_le_mul_left l25519 hnot
  have hdiv := Nat.div_add_mod k.val l25519
  have hle : 2 ^ 512 ≤ k.val := by
    calc 2 ^ 512
        = l25519 * wideQuot + wideRem := two_pow_512_eq.symm
      _ ≤ k.val := by omega
  exact Nat.not_lt.mpr hle k.isLt

private theorem prEvent_liftChalFin_eq_singleton (k : Fin (2 ^ 512)) :
    Pr{let x ← liftChalFin (k.val : ZMod l25519)}[x = k] =
      if k.val % l25519 < wideRem then ((wideQuot + 1 : ℕ) : ℝ≥0∞)⁻¹
      else (wideQuot : ℝ≥0∞)⁻¹ := by
  have hval : ((k.val : ZMod l25519)).val = k.val % l25519 :=
    ZMod.val_natCast (n := l25519) k.val
  have hdiv : k.val % l25519 + l25519 * (k.val / l25519) = k.val := by
    have := Nat.div_add_mod k.val l25519
    omega
  unfold liftChalFin
  by_cases hlt : k.val % l25519 < wideRem
  · have hlt_z : ((k.val : ZMod l25519)).val < wideRem := by rwa [hval]
    simp only [hlt_z, ↓reduceDIte, hlt, ↓reduceIte, prEvent_map]
    let q0 : Fin (wideQuot + 1) := ⟨k.val / l25519, div_lt_wideQuot_add_one k⟩
    have heq : (fun q : Fin (wideQuot + 1) =>
        (⟨((k.val : ZMod l25519)).val + l25519 * q.val,
          add_mul_lt_two_pow_512_of_lt_wideRem hlt_z q.isLt⟩ : Fin (2 ^ 512)) = k) =
        (· = q0) := by
      ext q
      simp only [Fin.ext_iff, hval, q0]
      constructor
      · intro h
        have hpos := l25519_pos
        nlinarith
      · intro h; rw [h, hdiv]
    rw [heq, SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  · have hlt_z : ¬ ((k.val : ZMod l25519)).val < wideRem := by rwa [hval]
    simp only [hlt_z, ↓reduceDIte, hlt, ↓reduceIte, prEvent_map]
    let q0 : Fin wideQuot := ⟨k.val / l25519, div_lt_wideQuot_of_not_lt_wideRem k hlt⟩
    have heq : (fun q : Fin wideQuot =>
        (⟨((k.val : ZMod l25519)).val + l25519 * q.val,
          add_mul_lt_two_pow_512_of_ge_wideRem ((k.val : ZMod l25519)).val_lt q.isLt⟩ :
            Fin (2 ^ 512)) = k) =
        (· = q0) := by
      ext q
      simp only [Fin.ext_iff, hval, q0]
      constructor
      · intro h
        have hpos := l25519_pos
        nlinarith
      · intro h; rw [h, hdiv]
    rw [heq, SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]

private theorem evalDist_liftChalSampleFin_singleton (k : Fin (2 ^ 512)) :
    letI : MeasurableSpace (Fin (2 ^ 512)) := ⊤
    𝒟[liftChalSampleFin] {k} =
      if k.val % l25519 < wideRem then
        (l25519 : ℝ≥0∞)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ≥0∞)⁻¹
      else
        (l25519 : ℝ≥0∞)⁻¹ * (wideQuot : ℝ≥0∞)⁻¹ := by
  let _ : MeasurableSpace (Fin (2 ^ 512)) := ⊤
  rw [← prEvent_eq_evalDist_singleton, liftChalSampleFin]
  rw [OracleComp.prEvent_bind_eq_mul_of_unique ($ᵗ (ZMod l25519)) liftChalFin
    (k.val : ZMod l25519) k (fun h' _ hk' => (liftChalFin_mod_eq hk').symm)]
  rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card,
    prEvent_liftChalFin_eq_singleton]
  split_ifs <;> rfl

private theorem card_filter_lt_wideRem_le (S : Finset (Fin (2 ^ 512))) :
    (S.filter (fun k => k.val % l25519 < wideRem)).card ≤ wideRem * (wideQuot + 1) := by
  classical
  set S0 := S.filter (fun k => k.val % l25519 < wideRem)
  let f : {k // k ∈ S0} → Fin wideRem × Fin (wideQuot + 1) :=
    fun x => (⟨x.1.val % l25519, (Finset.mem_filter.mp x.2).2⟩,
      ⟨x.1.val / l25519, div_lt_wideQuot_add_one x.1⟩)
  have hf : Function.Injective f := by
    intro x1 x2 heq
    simp only [f, Prod.mk.injEq, Fin.ext_iff] at heq
    obtain ⟨heq1, heq2⟩ := heq
    apply Subtype.ext; apply Fin.ext
    calc x1.1.val
        = l25519 * (x1.1.val / l25519) + x1.1.val % l25519 := (Nat.div_add_mod _ _).symm
      _ = l25519 * (x2.1.val / l25519) + x2.1.val % l25519 := by rw [heq1, heq2]
      _ = x2.1.val := Nat.div_add_mod _ _
  calc S0.card
      = S0.attach.card := S0.card_attach.symm
    _ = (S0.attach.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ Fintype.card (Fin wideRem × Fin (wideQuot + 1)) := Finset.card_le_univ _
    _ = wideRem * (wideQuot + 1) := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

private theorem card_filter_ge_wideRem_le (S : Finset (Fin (2 ^ 512))) :
    (S.filter (fun k => ¬ k.val % l25519 < wideRem)).card ≤ (l25519 - wideRem) * wideQuot := by
  classical
  set S1 := S.filter (fun k => ¬ k.val % l25519 < wideRem)
  let f : {k // k ∈ S1} → Fin (l25519 - wideRem) × Fin wideQuot :=
    fun x => (⟨x.1.val % l25519 - wideRem,
        Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp (Finset.mem_filter.mp x.2).2)
          (by rw [Nat.add_sub_of_le (le_of_lt wideRem_lt_l25519)]
              exact Nat.mod_lt x.1.val l25519_pos)⟩,
      ⟨x.1.val / l25519, div_lt_wideQuot_of_not_lt_wideRem x.1 (Finset.mem_filter.mp x.2).2⟩)
  have hf : Function.Injective f := by
    intro x1 x2 heq
    have hr1 : wideRem ≤ x1.1.val % l25519 := Nat.not_lt.mp (Finset.mem_filter.mp x1.2).2
    have hr2 : wideRem ≤ x2.1.val % l25519 := Nat.not_lt.mp (Finset.mem_filter.mp x2.2).2
    simp only [f, Prod.mk.injEq, Fin.ext_iff] at heq
    obtain ⟨heq1, heq2⟩ := heq
    have hrem : x1.1.val % l25519 = x2.1.val % l25519 := by
      calc x1.1.val % l25519
          = x1.1.val % l25519 - wideRem + wideRem := (Nat.sub_add_cancel hr1).symm
        _ = x2.1.val % l25519 - wideRem + wideRem := by rw [heq1]
        _ = x2.1.val % l25519 := Nat.sub_add_cancel hr2
    apply Subtype.ext; apply Fin.ext
    calc x1.1.val
        = l25519 * (x1.1.val / l25519) + x1.1.val % l25519 := (Nat.div_add_mod _ _).symm
      _ = l25519 * (x2.1.val / l25519) + x2.1.val % l25519 := by rw [hrem, heq2]
      _ = x2.1.val := Nat.div_add_mod _ _
  calc S1.card
      = S1.attach.card := S1.card_attach.symm
    _ = (S1.attach.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ Fintype.card (Fin (l25519 - wideRem) × Fin wideQuot) := Finset.card_le_univ _
    _ = (l25519 - wideRem) * wideQuot := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

private theorem deltaWide_abs_bound {a0 a1 : ℕ}
    (ha0 : a0 ≤ wideRem * (wideQuot + 1))
    (ha1 : a1 ≤ (l25519 - wideRem) * wideQuot) :
    let x : ℝ := (a0 : ℝ) * ((2 : ℝ) ^ 512)⁻¹ + (a1 : ℝ) * ((2 : ℝ) ^ 512)⁻¹
    let y : ℝ :=
      (a0 : ℝ) * ((l25519 : ℝ)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ)⁻¹) +
        (a1 : ℝ) * ((l25519 : ℝ)⁻¹ * (wideQuot : ℝ)⁻¹)
    x ≤ y + deltaWide ∧ y ≤ x + deltaWide := by
  intro x y
  set L : ℝ := (l25519 : ℝ)
  set Q : ℝ := (wideQuot : ℝ)
  set R : ℝ := (wideRem : ℝ)
  set D : ℝ := ((l25519 - wideRem : ℕ) : ℝ)
  set P512 : ℝ := (2 : ℝ) ^ 512
  have hL_pos : 0 < L := Nat.cast_pos.mpr l25519_pos
  have hQ_pos : 0 < Q := Nat.cast_pos.mpr wideQuot_pos
  have hQ1_eq : ((wideQuot + 1 : ℕ) : ℝ) = Q + 1 := by rw [Nat.cast_add, Nat.cast_one]
  have hQ1_pos : 0 < Q + 1 := by linarith
  have hP_pos : 0 < P512 := pow_pos zero_lt_two 512
  have hP_eq : L * Q + R = P512 := by
    have h := congrArg (Nat.cast (R := ℝ)) two_pow_512_eq
    rwa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hD_eq : D = L - R := Nat.cast_sub (le_of_lt wideRem_lt_l25519)
  have hR_nonneg : 0 ≤ R := Nat.cast_nonneg _
  have hD_nonneg : 0 ≤ D := Nat.cast_nonneg _
  have ha0_real : (a0 : ℝ) ≤ R * (Q + 1) := by
    have h := (Nat.cast_le (α := ℝ)).mpr ha0
    rwa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have ha1_real : (a1 : ℝ) ≤ D * Q := by
    have h := (Nat.cast_le (α := ℝ)).mpr ha1
    rwa [Nat.cast_mul] at h
  have ha0_nonneg : 0 ≤ (a0 : ℝ) := Nat.cast_nonneg _
  have ha1_nonneg : 0 ≤ (a1 : ℝ) := Nat.cast_nonneg _
  have hdelta : deltaWide = R * D / (L * P512) := rfl
  have hx_eq : x = (a0 : ℝ) / P512 + (a1 : ℝ) / P512 := by
    dsimp only [x, P512]; ring
  have hy_eq : y = (a0 : ℝ) / (L * (Q + 1)) + (a1 : ℝ) / (L * Q) := by
    dsimp only [y]
    rw [hQ1_eq]
    change (a0 : ℝ) * (L⁻¹ * (Q + 1)⁻¹) + (a1 : ℝ) * (L⁻¹ * Q⁻¹) =
      (a0 : ℝ) / (L * (Q + 1)) + (a1 : ℝ) / (L * Q)
    field_simp
  have hLQ1_pos : 0 < P512 * L * (Q + 1) := mul_pos (mul_pos hP_pos hL_pos) hQ1_pos
  have hLQ_pos : 0 < P512 * L * Q := mul_pos (mul_pos hP_pos hL_pos) hQ_pos
  have hLP_pos : 0 < L * P512 := mul_pos hL_pos hP_pos
  have hdiff :
      x - y =
        (a0 : ℝ) * D / (P512 * L * (Q + 1)) -
          (a1 : ℝ) * R / (P512 * L * Q) := by
    rw [hx_eq, hy_eq]
    field_simp
    rw [← hP_eq, hD_eq]
    ring
  constructor
  · have hterm1 :
        (a0 : ℝ) * D / (P512 * L * (Q + 1)) ≤ deltaWide := by
      rw [hdelta]
      have hnum : (a0 : ℝ) * D ≤ (R * (Q + 1)) * D :=
        mul_le_mul_of_nonneg_right ha0_real hD_nonneg
      calc (a0 : ℝ) * D / (P512 * L * (Q + 1))
          ≤ (R * (Q + 1)) * D / (P512 * L * (Q + 1)) :=
            div_le_div_of_nonneg_right hnum hLQ1_pos.le
        _ = R * D / (L * P512) := by field_simp
    have hterm2 : 0 ≤ (a1 : ℝ) * R / (P512 * L * Q) :=
      div_nonneg (mul_nonneg ha1_nonneg hR_nonneg) hLQ_pos.le
    linarith
  · have hterm1 : 0 ≤ (a0 : ℝ) * D / (P512 * L * (Q + 1)) :=
      div_nonneg (mul_nonneg ha0_nonneg hD_nonneg) hLQ1_pos.le
    have hterm2 :
        (a1 : ℝ) * R / (P512 * L * Q) ≤ deltaWide := by
      rw [hdelta]
      have hnum : (a1 : ℝ) * R ≤ (D * Q) * R :=
        mul_le_mul_of_nonneg_right ha1_real hR_nonneg
      calc (a1 : ℝ) * R / (P512 * L * Q)
          ≤ (D * Q) * R / (P512 * L * Q) :=
            div_le_div_of_nonneg_right hnum hLQ_pos.le
        _ = R * D / (L * P512) := by field_simp
    linarith

/-- Total-variation distance between a uniform 64-byte digest `sampleRandom64` and a uniform
    `ZMod l25519` challenge lifted via `liftChalTo64` is at most `deltaWide`. -/
theorem measureETVDist_sampleRandom64_liftChalTo64 :
    letI : MeasurableSpace Bytes := ⊤
    measureETVDist sampleRandom64
      (do let h ← $ᵗ (ZMod l25519); liftChalTo64 h) ≤ ENNReal.ofReal deltaWide := by
  classical
  let _ : MeasurableSpace Bytes := ⊤
  let _ : MeasurableSpace (Fin (2 ^ 512)) := ⊤
  have hmap_rhs :
      (do let h ← $ᵗ (ZMod l25519); liftChalTo64 h) =
        (fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> liftChalSampleFin := by
    simp only [liftChalTo64, liftChalSampleFin, map_eq_bind_pure_comp, bind_assoc]
  rw [hmap_rhs]
  have hetv_eq :
      measureETVDist sampleRandom64
          ((fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> liftChalSampleFin) =
        measureETVDist
          ((fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> ($ᵗ (Fin (2 ^ 512))))
          ((fun k : Fin (2 ^ 512) => bytesOfNatLE 64 k.val) <$> liftChalSampleFin) := by
    simp only [measureETVDist, sampleRandom64_evalDist_eq]
  rw [hetv_eq]
  refine (measureETVDist_map_le _ _ _ Measurable.of_discrete).trans ?_
  refine iSup_le fun s => ?_
  let S : Finset (Fin (2 ^ 512)) := Finset.univ.filter (· ∈ s.1)
  have hs_eq : s.1 = (↑S : Set (Fin (2 ^ 512))) := by
    ext k; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S]
  let p : Fin (2 ^ 512) → Prop := fun k => k.val % l25519 < wideRem
  set a0 := (S.filter p).card
  set a1 := (S.filter (fun k => ¬ p k)).card
  have hP_pos : (0 : ℝ) < (2 : ℝ) ^ 512 := pow_pos zero_lt_two 512
  have hL_pos : (0 : ℝ) < (l25519 : ℝ) := Nat.cast_pos.mpr l25519_pos
  have hQ_pos : (0 : ℝ) < (wideQuot : ℝ) := Nat.cast_pos.mpr wideQuot_pos
  have hQ1_pos : (0 : ℝ) < ((wideQuot + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos _)
  have hP_inv_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ 512)⁻¹ := inv_nonneg.mpr hP_pos.le
  have hL_inv_nn : (0 : ℝ) ≤ (l25519 : ℝ)⁻¹ := inv_nonneg.mpr hL_pos.le
  have hQ_inv_nn : (0 : ℝ) ≤ (wideQuot : ℝ)⁻¹ := inv_nonneg.mpr hQ_pos.le
  have hQ1_inv_nn : (0 : ℝ) ≤ ((wideQuot + 1 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr hQ1_pos.le
  have hmu_nn :
      0 ≤ (a0 : ℝ) * ((2 : ℝ) ^ 512)⁻¹ + (a1 : ℝ) * ((2 : ℝ) ^ 512)⁻¹ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hP_inv_nn)
      (mul_nonneg (Nat.cast_nonneg _) hP_inv_nn)
  have hnu_nn :
      0 ≤ (a0 : ℝ) * ((l25519 : ℝ)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ)⁻¹) +
        (a1 : ℝ) * ((l25519 : ℝ)⁻¹ * (wideQuot : ℝ)⁻¹) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL_inv_nn hQ1_inv_nn))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL_inv_nn hQ_inv_nn))
  have hmu :
      𝒟[($ᵗ (Fin (2 ^ 512)) : ProbComp (Fin (2 ^ 512)))] s.1 =
        ENNReal.ofReal
          ((a0 : ℝ) * ((2 : ℝ) ^ 512)⁻¹ + (a1 : ℝ) * ((2 : ℝ) ^ 512)⁻¹) := by
    rw [hs_eq, ← MeasureTheory.sum_measure_singleton,
      ← Finset.sum_filter_add_sum_filter_not S p]
    simp only [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hP_inv_nn)
        (mul_nonneg (Nat.cast_nonneg _) hP_inv_nn),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_inv_of_pos hP_pos, ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  have hnu :
      𝒟[liftChalSampleFin] s.1 =
        ENNReal.ofReal
          ((a0 : ℝ) * ((l25519 : ℝ)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ)⁻¹) +
            (a1 : ℝ) * ((l25519 : ℝ)⁻¹ * (wideQuot : ℝ)⁻¹)) := by
    rw [hs_eq, ← MeasureTheory.sum_measure_singleton,
      ← Finset.sum_filter_add_sum_filter_not S p]
    have hs0 :
        ∑ x ∈ S.filter p, 𝒟[liftChalSampleFin] {x} =
          (a0 : ℝ≥0∞) * ((l25519 : ℝ≥0∞)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
      have : ∀ x ∈ S.filter p,
          𝒟[liftChalSampleFin] {x} =
            (l25519 : ℝ≥0∞)⁻¹ * ((wideQuot + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        intro x hx
        rw [evalDist_liftChalSampleFin_singleton, ite_eq_left (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    have hs1 :
        ∑ x ∈ S.filter (fun k => ¬ p k), 𝒟[liftChalSampleFin] {x} =
          (a1 : ℝ≥0∞) * ((l25519 : ℝ≥0∞)⁻¹ * (wideQuot : ℝ≥0∞)⁻¹) := by
      have : ∀ x ∈ S.filter (fun k => ¬ p k),
          𝒟[liftChalSampleFin] {x} =
            (l25519 : ℝ≥0∞)⁻¹ * (wideQuot : ℝ≥0∞)⁻¹ := by
        intro x hx
        rw [evalDist_liftChalSampleFin_singleton, ite_eq_right (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    rw [hs0, hs1,
      ENNReal.ofReal_add
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL_inv_nn hQ1_inv_nn))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL_inv_nn hQ_inv_nn)),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul hL_inv_nn, ENNReal.ofReal_mul hL_inv_nn,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_inv_of_pos hL_pos,
      ENNReal.ofReal_inv_of_pos hQ1_pos,
      ENNReal.ofReal_inv_of_pos hQ_pos,
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hmu, hnu]
  have hbounds := deltaWide_abs_bound
    (card_filter_lt_wideRem_le S) (card_filter_ge_wideRem_le S)
  have hdelta_nonneg : 0 ≤ deltaWide :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_pos hL_pos hP_pos).le
  refine ENNReal.absDiff_le_iff.mpr ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_add hnu_nn hdelta_nonneg]
    exact ENNReal.ofReal_le_ofReal hbounds.1
  · rw [← ENNReal.ofReal_add hmu_nn hdelta_nonneg]
    exact ENNReal.ofReal_le_ofReal hbounds.2

/-! ## `H_1` domain separation and `xeddsaModLoss` hop -/

def isH1Input (bs : Bytes) : Bool :=
  bs.take 32 == xeddsaHashPrefix

theorem isH1Input_xeddsaHashPrefix_append (rest : Bytes) :
    isH1Input (xeddsaHashPrefix ++ rest) = true := by
  unfold isH1Input
  have hlen : xeddsaHashPrefix.length = 32 := xeddsaHashPrefix_length
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact beq_self_eq_true _

theorem isH1Input_false_of_scalarIsInRange {capR rest : Bytes}
    (hlen : capR.length = 32)
    (hinRange : scalarIsInRange (clearSignBit32 capR) = true) :
    isH1Input (capR ++ rest) = false := by
  unfold isH1Input
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  apply beq_false_of_ne
  intro heq
  rw [heq, scalarIsInRange_clearSignBit32_xeddsaHashPrefix] at hinRange
  cases hinRange

def isChalRomQuery (q : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery))) : Bool :=
  isRomDirectRoQuery q || isRomPrimVerifyQuery q || isRomPrimSigSignQuery q

private theorem isQueryBoundP_or_of_disjoint {ι α : Type} {spec : OracleSpec ι}
    {oa : OracleComp spec α} {p₁ p₂ : ι → Prop} [DecidablePred p₁] [DecidablePred p₂]
    {n₁ n₂ : ℕ} (hdisj : ∀ t, ¬ (p₁ t ∧ p₂ t))
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBoundP (fun t => p₁ t ∨ p₂ t) (n₁ + n₂) := by
  refine OracleComp.IsQueryBoundP.proj (fun b : ℕ × ℕ => b.1 + b.2) ?_ ?_
    (OracleComp.IsQueryBoundP.and_isQueryBound_pair h₁ h₂)
  · intro t b hcan hp
    rcases hp with hp1 | hp2
    · have := hcan.1.resolve_left (not_not.mpr hp1); omega
    · have := hcan.2.resolve_left (not_not.mpr hp2); omega
  · intro t b hcan
    by_cases hp1 : p₁ t <;> by_cases hp2 : p₂ t
    · exact (hdisj t ⟨hp1, hp2⟩).elim
    · have := hcan.1.resolve_left (not_not.mpr hp1)
      simp only [hp1, hp2, or_false, ↓reduceIte]; omega
    · have := hcan.2.resolve_left (not_not.mpr hp2)
      simp only [hp1, hp2, false_or, ↓reduceIte]; omega
    · simp [hp1, hp2]

theorem isQueryBoundP_isChalRomQuery {A : GapSigEufCmaRoAdv} (hA : A.Bounded) (pk : Bytes) :
    OracleComp.IsQueryBoundP (A.run pk) (fun q => isChalRomQuery q = true)
      (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  obtain ⟨_, _, _, hro, hver, hsig⟩ := hA
  have hd1 : ∀ t, ¬ (isRomDirectRoQuery t = true ∧ isRomPrimVerifyQuery t = true) := by
    rintro (((_ | p) | _) | (_ | _)) ⟨h1, h2⟩ <;>
      simp [isRomDirectRoQuery, isRomPrimVerifyQuery] at h1 h2
  have h12 := isQueryBoundP_or_of_disjoint hd1 (hro pk) (hver pk)
  have hd2 : ∀ t, ¬ ((isRomDirectRoQuery t = true ∨ isRomPrimVerifyQuery t = true) ∧
      isRomPrimSigSignQuery t = true) := by
    rintro (((_ | p) | _) | (_ | _)) ⟨h1, h2⟩
    · simp [isRomPrimSigSignQuery] at h2
    · cases p <;> simp only [isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery,
        Bool.false_eq_true, or_self] at h1 h2
    · simp [isRomPrimSigSignQuery] at h2
    · simp [isRomPrimSigSignQuery] at h2
    · simp [isRomPrimSigSignQuery] at h2
  have h123 := isQueryBoundP_or_of_disjoint hd2 h12 (hsig pk)
  unfold xeddsaChalBudget
  refine (OracleComp.isQueryBoundP_congr_pred ?_).mp h123
  intro t
  simp [isChalRomQuery, Bool.or_eq_true]

abbrev ChalDigestSpec : OracleSpec (ℕ ⊕ Unit) :=
  unifSpec + (Unit →ₒ Bytes)

abbrev ChalRoComp : Type → Type :=
  StateT sha512RoSpec.QueryCache (OracleComp ChalDigestSpec)

noncomputable def liftProbToChal {α : Type} (oa : ProbComp α) : OracleComp ChalDigestSpec α :=
  simulateQ (QueryImpl.ofLift unifSpec (OracleComp ChalDigestSpec)) oa

noncomputable def splitRoBaseImpl : QueryImpl sha512RoSpec (OracleComp ChalDigestSpec) :=
  fun bs =>
    if isH1Input bs then liftProbToChal sampleRandom64
    else liftM (ChalDigestSpec.query (Sum.inr ()))

noncomputable def splitRoImpl : QueryImpl sha512RoSpec ChalRoComp :=
  splitRoBaseImpl.withCaching

noncomputable def xeddsaSimSignChal (P : Primitives) (pk : Bytes) (bSim : UInt8) (m : Bytes) :
    ChalRoComp Bytes := do
  let edPk := (P.montToEd pk bSim).getD (edDummy P)
  let capA := P.compress edPk
  let minusCapA := P.edNeg edPk
  let sVal ← liftM (m := OracleComp ChalDigestSpec) (liftProbToChal ($ᵗ (ZMod l25519)))
  let hDigest ← liftM (m := OracleComp ChalDigestSpec) (liftProbToChal sampleRandom64)
  let h := P.scalarFromWide hDigest
  let s := encodeScalarBytes sVal
  let capR := P.compress (P.doubleScalarMulBasepoint h minusCapA s)
  let signBitByte : UInt8 := (bSim &&& 1) <<< 7
  modify fun cache =>
    match cache (capR ++ capA ++ m) with
    | some _ => cache
    | none   => cache.cacheQuery (capR ++ capA ++ m) hDigest
  return (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte])

noncomputable def primSplitRoImpl (P : Primitives) : QueryImpl primSpec ChalRoComp :=
  fun q => simulateQ splitRoImpl (primRoStep P q)

noncomputable def primBaseSplitRoImpl (P : Primitives) :
    QueryImpl (PrimBaseSpec + sha512RoSpec) ChalRoComp :=
  ((QueryImpl.ofLift unifSpec (OracleComp ChalDigestSpec)).liftTarget ChalRoComp +
    primSplitRoImpl P) + splitRoImpl

/-- Simulated-signing EUF-CMA experiment factored through `ChalDigestSpec`. -/
noncomputable def simWithChalDigest (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    OracleComp ChalDigestSpec Bool := do
  let sigImpl : QueryImpl sigOracleSpec (StateT (List Bytes) ChalRoComp) :=
    fun (.sign m) => do
      let sig ← liftM (m := ChalRoComp) (xeddsaSimSignChal P pk bSim m)
      modify (m :: ·)
      return sig
  let ddhImpl : QueryImpl gapDhOracleSpec (StateT (List Bytes) ChalRoComp) :=
    fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
  let fullImpl :=
    (primBaseSplitRoImpl P).liftTarget (StateT (List Bytes) ChalRoComp) + (sigImpl + ddhImpl)
  let checkInRo : ChalRoComp Bool := do
    let ((mStar, sigStar), signedMsgs) ← (simulateQ fullImpl (A.run pk)).run []
    let ok ← simulateQ splitRoImpl (xeddsaVerifyRo P pk mStar sigStar)
    return (ok && decide (mStar ∉ signedMsgs))
  checkInRo.run' ∅

noncomputable def implReal : QueryImpl ChalDigestSpec ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + fun () => sampleRandom64

noncomputable def implLifted : QueryImpl ChalDigestSpec ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + fun () => do
    let h ← $ᵗ (ZMod l25519)
    liftChalTo64 h

private theorem simulateQ_implReal_liftProbToChal {α : Type} (oa : ProbComp α) :
    simulateQ implReal (liftProbToChal oa) = oa := by
  unfold liftProbToChal
  rw [← QueryImpl.simulateQ_compose]
  have hid : implReal ∘ₛ QueryImpl.ofLift unifSpec (OracleComp ChalDigestSpec) =
      QueryImpl.id' unifSpec := by
    funext n
    rw [QueryImpl.apply_compose, QueryImpl.ofLift_apply]
    change simulateQ implReal (liftM (ChalDigestSpec.query (Sum.inl n))) = _
    rw [simulateQ_spec_query]
    rfl
  rw [hid, simulateQ_id']

private theorem simulateQ_implReal_splitRoBaseImpl (bs : Bytes) :
    simulateQ implReal (splitRoBaseImpl bs) = sha512RoBaseImpl bs := by
  unfold splitRoBaseImpl sha512RoBaseImpl
  split_ifs
  · exact simulateQ_implReal_liftProbToChal sampleRandom64
  · rw [simulateQ_spec_query]; rfl

private theorem mapStateTBase_implReal_splitRoImpl :
    implReal.mapStateTBase splitRoImpl = sha512RoImpl := by
  funext bs
  apply StateT.ext
  intro cache
  simp only [QueryImpl.mapStateTBase, StateT.run_mk, splitRoImpl, sha512RoImpl,
    QueryImpl.withCaching_apply]
  cases h : cache bs <;>
    simp [h, simulateQ_map, simulateQ_implReal_splitRoBaseImpl]

private theorem simulateQ_implReal_xeddsaSimSignChal_run
    (P : Primitives) (pk : Bytes) (bSim : UInt8) (m : Bytes)
    (cache : sha512RoSpec.QueryCache) :
    simulateQ implReal ((xeddsaSimSignChal P pk bSim m).run cache) =
      (xeddsaSimSign P pk bSim m).run cache := by
  unfold xeddsaSimSignChal xeddsaSimSign
  simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_modify, StateT.run_pure,
    simulateQ_bind, simulateQ_pure, simulateQ_implReal_liftProbToChal]
  rfl

private theorem mapStateTBase_implReal_primSplitRoImpl (P : Primitives) :
    implReal.mapStateTBase (primSplitRoImpl P) = primRoImpl P := by
  funext q
  apply StateT.ext
  intro cache
  simp only [QueryImpl.mapStateTBase, StateT.run_mk, primSplitRoImpl, primRoImpl,
    QueryImpl.simulateQ_mapStateTBase_run, mapStateTBase_implReal_splitRoImpl]

private theorem simulateQ_implReal_nested_run {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8)
    (oa : OracleComp XeddsaRomOracleSpec α)
    (msgs : List Bytes) (cache : sha512RoSpec.QueryCache) :
    let sigImplC : QueryImpl sigOracleSpec (StateT (List Bytes) ChalRoComp) :=
      fun (.sign m) => do
        let sig ← liftM (m := ChalRoComp) (xeddsaSimSignChal P pk bSim m)
        modify (m :: ·)
        return sig
    let ddhImplC : QueryImpl gapDhOracleSpec (StateT (List Bytes) ChalRoComp) :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    let fullImplC :=
      (primBaseSplitRoImpl P).liftTarget (StateT (List Bytes) ChalRoComp) + (sigImplC + ddhImplC)
    let sigImplR : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp) :=
      fun (.sign m) => do
        let sig ← liftM (m := Sha512RoComp) (xeddsaSimSign P pk bSim m)
        modify (m :: ·)
        return sig
    let ddhImplR : QueryImpl gapDhOracleSpec (StateT (List Bytes) Sha512RoComp) :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    let fullImplR :=
      (primBaseRoImpl P).liftTarget (StateT (List Bytes) Sha512RoComp) + (sigImplR + ddhImplR)
    simulateQ implReal (((simulateQ fullImplC oa).run msgs).run cache) =
      ((simulateQ fullImplR oa).run msgs).run cache := by
  intro sigImplC ddhImplC fullImplC sigImplR ddhImplR fullImplR
  have hstep : ∀ t (s : List Bytes) (c : sha512RoSpec.QueryCache),
      simulateQ implReal (((fullImplC t).run s).run c) = ((fullImplR t).run s).run c := by
    intro t s c
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · dsimp only [fullImplC, fullImplR, primBaseSplitRoImpl, primBaseRoImpl]
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply,
        OracleComp.liftM_run_StateT, StateT.run_bind, StateT.run_pure,
        simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
      change (simulateQ implReal (liftM (ChalDigestSpec.query (Sum.inl n))) >>= _) = _
      rw [simulateQ_spec_query]
      rfl
    · have hp := congrArg (fun (impl : QueryImpl primSpec Sha512RoComp) =>
          (impl p).run c) (mapStateTBase_implReal_primSplitRoImpl P)
      simp only [QueryImpl.mapStateTBase, StateT.run_mk] at hp
      simp [fullImplC, fullImplR, primBaseSplitRoImpl, primBaseRoImpl, hp]
    · have hbs := congrArg (fun (impl : QueryImpl sha512RoSpec Sha512RoComp) =>
          (impl bs).run c) mapStateTBase_implReal_splitRoImpl
      simp only [QueryImpl.mapStateTBase, StateT.run_mk] at hbs
      simp [fullImplC, fullImplR, primBaseSplitRoImpl, primBaseRoImpl, hbs]
    · cases qSig with
      | sign m =>
          simp [fullImplC, fullImplR, sigImplC, sigImplR, StateT.run_bind, StateT.run_modify,
            simulateQ_implReal_xeddsaSimSignChal_run]
    · simp [fullImplC, fullImplR, ddhImplC, ddhImplR]
  induction oa using OracleComp.inductionOn generalizing msgs cache with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
        StateT.run_bind, StateT.run_bind, simulateQ_bind, hstep t msgs cache]
      exact bind_congr fun z => ih z.1.1 z.1.2 z.2

theorem simulateQ_implReal_simWithChalDigest_eq
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    simulateQ implReal (simWithChalDigest P isValidDhTriple pk bSim A) =
      gapSigEufCmaSimExpOnPk P isValidDhTriple pk bSim A := by
  unfold simWithChalDigest gapSigEufCmaSimExpOnPk
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_bind, StateT.run_pure,
    simulateQ_bind, simulateQ_pure]
  congr 1
  rw [simulateQ_implReal_nested_run]
  refine bind_congr fun ⟨⟨⟨mStar, sigStar⟩, signedMsgs⟩, cache⟩ => ?_
  have hv := QueryImpl.simulateQ_mapStateTBase_run implReal splitRoImpl
    (xeddsaVerifyRo P pk mStar sigStar) cache
  rw [mapStateTBase_implReal_splitRoImpl] at hv
  simp [hv]

private theorem isQueryBoundP_liftProbToChal {α : Type} (oa : ProbComp α) :
    OracleComp.IsQueryBoundP (liftProbToChal oa) (· = Sum.inr ()) 0 := by
  unfold liftProbToChal
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind n mx ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift]
      change OracleComp.IsQueryBoundP
        (liftM (ChalDigestSpec.query (Sum.inl n)) >>= fun u =>
          simulateQ (QueryImpl.ofLift unifSpec (OracleComp ChalDigestSpec)) (mx u))
        (· = Sum.inr ()) 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

private theorem isQueryBoundP_splitRoImpl_of_isH1 {bs : Bytes} (hH1 : isH1Input bs = true)
    (cache : sha512RoSpec.QueryCache) :
    OracleComp.IsQueryBoundP ((splitRoImpl bs).run cache) (· = Sum.inr ()) 0 := by
  simp only [splitRoImpl, QueryImpl.withCaching_apply]
  cases h : cache bs with
  | some u => simp [h]
  | none =>
      simp only [h, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modifyGet,
        OracleComp.liftM_run_StateT, bind_assoc, splitRoBaseImpl, hH1, ↓reduceIte]
      have hmap :
          (do let u ← liftProbToChal sampleRandom64; pure (u, cache.cacheQuery bs u)) =
            (fun u => (u, cache.cacheQuery bs u)) <$> liftProbToChal sampleRandom64 := by
        simp [map_eq_bind_pure_comp]
      rw [hmap, OracleComp.isQueryBoundP_map_iff]
      exact isQueryBoundP_liftProbToChal sampleRandom64

private theorem isQueryBoundP_splitRoImpl (bs : Bytes) (cache : sha512RoSpec.QueryCache) :
    OracleComp.IsQueryBoundP ((splitRoImpl bs).run cache) (· = Sum.inr ()) 1 := by
  simp only [splitRoImpl, QueryImpl.withCaching_apply]
  cases h : cache bs with
  | some u => simp [h]
  | none =>
      simp only [h, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modifyGet,
        OracleComp.liftM_run_StateT, bind_assoc, splitRoBaseImpl]
      have hmap : ∀ (mx : OracleComp ChalDigestSpec Bytes),
          (do let u ← mx; pure (u, cache.cacheQuery bs u)) =
            (fun u => (u, cache.cacheQuery bs u)) <$> mx := by
        intro mx; simp [map_eq_bind_pure_comp]
      rw [hmap, OracleComp.isQueryBoundP_map_iff]
      split_ifs
      · exact (isQueryBoundP_liftProbToChal sampleRandom64).mono (by omega)
      · rw [OracleComp.isQueryBoundP_query_iff]
        intro _; omega

private theorem isQueryBoundP_xeddsaVerifyRo_split (P : Primitives) (pk m sig : Bytes)
    (cache : sha512RoSpec.QueryCache) :
    OracleComp.IsQueryBoundP ((simulateQ splitRoImpl (xeddsaVerifyRo P pk m sig)).run cache)
      (· = Sum.inr ()) 1 := by
  unfold xeddsaVerifyRo
  split_ifs with hg
  · dsimp only
    cases hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) with
    | none => simp [simulateQ_pure]
    | some edPk =>
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
          StateT.run_pure]
        refine (OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
          (isQueryBoundP_splitRoImpl (sig.take 32 ++ P.compress edPk ++ m) cache) ?_).mono
          (by omega)
        intro _ _; simp
  · simp [simulateQ_pure]

private theorem isQueryBoundP_xeddsaSignRo_split (P : Primitives) (sk m rand : Bytes)
    (cache : sha512RoSpec.QueryCache) :
    OracleComp.IsQueryBoundP ((simulateQ splitRoImpl (xeddsaSignRo P sk m rand)).run cache)
      (· = Sum.inr ()) 1 := by
  unfold xeddsaSignRo
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure]
  have hH1 : isH1Input
      (xeddsaHashPrefix ++ clampScalar25519 sk ++ m ++ fitBytesRef 64 rand) = true := by
    rw [List.append_assoc, List.append_assoc]
    exact isH1Input_xeddsaHashPrefix_append _
  have h1 := isQueryBoundP_splitRoImpl_of_isH1 hH1 cache
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 1) h1 ?_).mono (by omega)
  intro z1 _
  refine (OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
    (isQueryBoundP_splitRoImpl
      (P.compress (edBaseMul P (P.scalarFromWide z1.1)) ++
        P.compress (edBaseMul P (P.scalarFromBytesModOrder (clampScalar25519 sk))) ++ m) z1.2)
    ?_).mono (by omega)
  intro _ _; simp

private theorem isQueryBoundP_xeddsaSimSignChal (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (m : Bytes) (cache : sha512RoSpec.QueryCache) :
    OracleComp.IsQueryBoundP ((xeddsaSimSignChal P pk bSim m).run cache)
      (· = Sum.inr ()) 0 := by
  unfold xeddsaSimSignChal
  simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_modify, StateT.run_pure,
    bind_assoc, pure_bind]
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (isQueryBoundP_liftProbToChal _) ?_).mono (by omega)
  intro _ _
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (isQueryBoundP_liftProbToChal _) ?_).mono (by omega)
  intro _ _
  simp

private theorem isQueryBoundP_nested_run_of_step
    {ι α σ τ : Type} {spec : OracleSpec ι}
    {p : ι → Prop} [DecidablePred p]
    {impl : QueryImpl spec (StateT σ (StateT τ (OracleComp ChalDigestSpec)))}
    {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n)
    (hstep : ∀ t s c,
      OracleComp.IsQueryBoundP (((impl t).run s).run c) (· = Sum.inr ()) (if p t then 1 else 0))
    (s : σ) (c : τ) :
    OracleComp.IsQueryBoundP (((simulateQ impl oa).run s).run c) (· = Sum.inr ()) n := by
  induction oa using OracleComp.inductionOn generalizing n s c with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [OracleComp.run_simulateQ_query_bind, StateT.run_bind]
      have h1 := h.1
      have hb : OracleComp.IsQueryBoundP
          (((impl t).run s).run c >>= fun z =>
            (((simulateQ impl (mx z.1.1)).run z.1.2).run z.2))
          (· = Sum.inr ()) ((if p t then 1 else 0) + (if p t then n - 1 else n)) :=
        OracleComp.isQueryBoundP_bind (hstep t s c) fun z _ => ih z.1.1 (h.2 z.1.1) z.1.2 z.2
      refine hb.mono ?_
      by_cases hpt : p t
      · have hpos : 0 < n := h1.resolve_left (not_not.mpr hpt)
        simp only [hpt, ↓reduceIte]; omega
      · simp [hpt]

theorem simWithChalDigest_isQueryBoundP
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    OracleComp.IsQueryBoundP (simWithChalDigest P isValidDhTriple pk bSim A)
      (· = Sum.inr ())
      (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign + 1) := by
  unfold simWithChalDigest
  simp only [StateT.run'_eq, OracleComp.isQueryBoundP_map_iff, StateT.run_bind, StateT.run_pure]
  refine OracleComp.isQueryBoundP_bind ?_ ?_
  · refine isQueryBoundP_nested_run_of_step (isQueryBoundP_isChalRomQuery hA pk) ?_ [] ∅
    intro t msgs cache
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · simp only [isChalRomQuery, isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery,
        Bool.or_self, Bool.false_eq_true, ↓reduceIte, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, primBaseSplitRoImpl, OracleComp.liftM_run_StateT,
        StateT.run_bind, StateT.run_pure, QueryImpl.ofLift_apply, bind_assoc, pure_bind]
      change OracleComp.IsQueryBoundP
        (liftM (ChalDigestSpec.query (Sum.inl n)) >>= fun a => pure ((a, msgs), cache))
        (· = Sum.inr ()) 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => trivial⟩
    · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, primBaseSplitRoImpl,
        QueryImpl.add_apply_inr, OracleComp.liftM_run_StateT, StateT.run_bind, StateT.run_pure]
      refine (OracleComp.isQueryBoundP_bind
        (n := if isChalRomQuery (Sum.inl (Sum.inl (Sum.inr p))) = true then 1 else 0) (m := 0)
        ?_ ?_).mono (by omega)
      · cases p <;>
          simp only [isChalRomQuery, isRomDirectRoQuery, isRomPrimVerifyQuery,
            isRomPrimSigSignQuery, Bool.false_or, Bool.or_false, ↓reduceIte,
            Bool.false_eq_true, primSplitRoImpl, primRoStep, simulateQ_pure, StateT.run_pure,
            OracleComp.isQueryBoundP_pure]
        · exact isQueryBoundP_xeddsaSignRo_split P _ _ _ cache
        · exact isQueryBoundP_xeddsaVerifyRo_split P _ _ _ cache
      · intro _ _; simp
    · simp only [isChalRomQuery, isRomDirectRoQuery, Bool.true_or, ↓reduceIte,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, primBaseSplitRoImpl,
        QueryImpl.add_apply_inr, OracleComp.liftM_run_StateT, StateT.run_bind, StateT.run_pure]
      refine (OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (isQueryBoundP_splitRoImpl bs cache) ?_).mono (by omega)
      intro _ _; simp
    · cases qSig with
      | sign m =>
          simp only [isChalRomQuery, isRomDirectRoQuery, isRomPrimVerifyQuery,
            isRomPrimSigSignQuery, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_bind,
            OracleComp.liftM_run_StateT, StateT.run_modify, StateT.run_pure,
            bind_assoc, pure_bind]
          refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
            (isQueryBoundP_xeddsaSimSignChal P pk bSim m cache) ?_).mono (by omega)
          intro _ _; simp
    · simp [isChalRomQuery, isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery]
  · rintro ⟨⟨⟨mStar, sigStar⟩, signedMsgs⟩, cache⟩ _
    refine (OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
      (isQueryBoundP_xeddsaVerifyRo_split P pk mStar sigStar cache) ?_).mono (by omega)
    intro _ _; simp

private theorem prEvent_gapSigEufCmaSimExpOnPk_le_lifted_add
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
    Pr{let ok ← gapSigEufCmaSimExpOnPk P isValidDhTriple pk bSim A}[ok = true] ≤
      Pr{let ok ← simulateQ implLifted (simWithChalDigest P isValidDhTriple pk bSim A)}[ok = true] +
        ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide := by
  intro q_H
  let _ : MeasurableSpace Bool := ⊤
  let _ : MeasurableSpace (Bool × PUnit) := ⊤
  rw [← simulateQ_implReal_simWithChalDigest_eq]
  set oa := simWithChalDigest P isValidDhTriple pk bSim A
  let impl₁ : QueryImpl ChalDigestSpec (StateT PUnit ProbComp) :=
    implReal.liftTarget (StateT PUnit ProbComp)
  let impl₂ : QueryImpl ChalDigestSpec (StateT PUnit ProbComp) :=
    implLifted.liftTarget (StateT PUnit ProbComp)
  have hrun_eq (impl : QueryImpl ChalDigestSpec ProbComp) :
      simulateQ impl oa = Prod.fst <$> (simulateQ (impl.liftTarget (StateT PUnit ProbComp)) oa).run () := by
    have h1 := simulateQ_liftTarget (m := ProbComp) (n := StateT PUnit ProbComp) impl oa
    have h2 : (liftM (simulateQ impl oa) : StateT PUnit ProbComp Bool).run () =
        (·, ()) <$> simulateQ impl oa := by
      simp [map_eq_bind_pure_comp]
    rw [← StateT.run'_eq, StateT.run'_eq, h1, h2, Functor.map_map]
    simp
  have hetv :
      measureETVDist (simulateQ implReal oa) (simulateQ implLifted oa) ≤
        ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide := by
    rw [hrun_eq implReal, hrun_eq implLifted]
    refine (measureETVDist_map_le _ _ Prod.fst Measurable.of_discrete).trans ?_
    refine OracleComp.ProgramLogic.Relational.measureETVDist_simulateQ_run_le_queryBoundP_mul
      impl₁ impl₂ (· = Sum.inr ()) ?_ ?_ oa (simWithChalDigest_isQueryBoundP P isValidDhTriple pk bSim hA) ()
    · rintro (_ | ⟨⟩) hS ⟨⟩
      · cases hS
      · let _ : MeasurableSpace Bytes := ⊤
        let _ : MeasurableSpace (Bytes × PUnit) := ⊤
        have hm1 : ((impl₁ (Sum.inr ())).run ()) = (·, ()) <$> sampleRandom64 := by
          simp only [impl₁, QueryImpl.liftTarget_apply, OracleComp.liftM_run_StateT,
            map_eq_bind_pure_comp]
          rfl
        have hm2 : ((impl₂ (Sum.inr ())).run ()) =
            (·, ()) <$> (do let h ← $ᵗ (ZMod l25519); liftChalTo64 h) := by
          simp only [impl₂, QueryImpl.liftTarget_apply, OracleComp.liftM_run_StateT,
            map_eq_bind_pure_comp]
          rfl
        rw [hm1, hm2]
        exact (measureETVDist_map_le _ _ (·, ()) Measurable.of_discrete).trans
          measureETVDist_sampleRandom64_liftChalTo64
    · rintro (n | ⟨⟩) hS ⟨⟩
      · rfl
      · exact (hS rfl).elim
  exact (prEvent_le_prEvent_add_measureETVDist _ _ (· = true) Measurable.of_discrete).trans
    (add_le_add le_rfl hetv)

/-- Replacing uniform 64-byte SHA-512 challenge digests with uniform `ZMod l25519` challenges lifted
    via `liftChalTo64` changes the simulated-signing EUF-CMA win probability by at most
    `xeddsaModLoss q_H`. -/
theorem gapSigEufCmaSimExpOnPk_le_lifted_add_modLoss
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
    (𝒟[gapSigEufCmaSimExpOnPk P isValidDhTriple pk bSim A] {true}).toReal ≤
      (𝒟[simulateQ implLifted (simWithChalDigest P isValidDhTriple pk bSim A)] {true}).toReal +
        xeddsaModLoss q_H := by
  intro q_H
  let _ : MeasurableSpace Bool := ⊤
  have hpr := prEvent_gapSigEufCmaSimExpOnPk_le_lifted_add P isValidDhTriple pk bSim hA
  dsimp only at hpr
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at hpr
  have hdelta_nn : 0 ≤ deltaWide := by
    unfold deltaWide
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_pos (Nat.cast_pos.mpr l25519_pos) (pow_pos zero_lt_two 512)).le
  have hfin1 : 𝒟[simulateQ implLifted (simWithChalDigest P isValidDhTriple pk bSim A)] {true} ≠ ⊤ :=
    measure_ne_top _ _
  have hfin2 : ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have htoReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) hpr
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hdelta_nn] at htoReal
  simpa [xeddsaModLoss, Nat.cast_add, Nat.cast_one] using htoReal

abbrev ChalZModSpec : OracleSpec (ℕ ⊕ Unit) :=
  unifSpec + (Unit →ₒ ZMod l25519)

noncomputable local instance : OracleSpec.UniformAnswerMeasure (Unit →ₒ ZMod l25519) :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty (Unit →ₒ ZMod l25519)

noncomputable def liftChalImpl : QueryImpl ChalDigestSpec (OracleComp ChalZModSpec)
  | .inl n  => liftM (ChalZModSpec.query (Sum.inl n))
  | .inr () => do
      let h ← liftM (ChalZModSpec.query (Sum.inr ()))
      simulateQ (QueryImpl.ofLift unifSpec (OracleComp ChalZModSpec)) (liftChalTo64 h)

noncomputable def evalChalZMod : QueryImpl ChalZModSpec ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := (Unit →ₒ ZMod l25519))

theorem evalChalZMod_evalDistEq {α : Type} (oa : OracleComp ChalZModSpec α) :
    simulateQ evalChalZMod oa =ᵈ oa := by
  let _ : MeasurableSpace α := ⊤
  refine EvalDistEq.of_evalDist_eq (evalDist_simulateQ_eq_of_forall _ (fun t => ?_) oa)
  rw [OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn]
  rcases t with n | u
  · simp only [evalChalZMod, QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    exact evalDist_liftM_query_uniform (spec := unifSpec) n
  · let _ : MeasurableSpace (ZMod l25519) := ⊤
    simp only [evalChalZMod, QueryImpl.add_apply_inr, uniformSampleImpl_apply]
    exact SampleableType.evalDist_uniformSample

theorem evalChalZMod_comp_liftChalImpl :
    evalChalZMod ∘ₛ liftChalImpl = implLifted := by
  funext t
  rcases t with (n | ⟨⟩)
  · rw [QueryImpl.apply_compose, liftChalImpl, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, liftChalImpl, implLifted,
      simulateQ_bind, simulateQ_spec_query]
    change ((uniformSampleImpl (spec := (Unit →ₒ ZMod l25519))) () >>= _) =
      ($ᵗ (ZMod l25519) >>= _)
    rw [uniformSampleImpl_apply]
    refine bind_congr fun h => ?_
    rw [← QueryImpl.simulateQ_compose]
    have hid : evalChalZMod ∘ₛ QueryImpl.ofLift unifSpec (OracleComp ChalZModSpec) =
        QueryImpl.id' unifSpec := by
      funext n
      rw [QueryImpl.apply_compose, QueryImpl.ofLift_apply]
      change simulateQ evalChalZMod (liftM (ChalZModSpec.query (Sum.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [hid, simulateQ_id']

/-! ## 2-special soundness and clamped `±a` scalar recovery -/

def sigRespBytes (sig : Bytes) : Bytes :=
  let sRaw := sig.drop 32
  sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]

def sigRespScalar (sig : Bytes) : ZMod l25519 :=
  decodeScalarBytes (fitBytesRef 32 (sigRespBytes sig))

def xeddsaVerifyChalInput? (P : Primitives) (pk m sig : Bytes) : Option Bytes :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => none
    | some edPk => some (sig.take 32 ++ P.compress edPk ++ m)
  else
    none

def xeddsaVerifyWithDigest (P : Primitives) (pk _m sig hDigest : Bytes) : Bool :=
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => false
    | some edPk =>
      let minusCapA := P.edNeg edPk
      let capR := sig.take 32
      let sClamped := sigRespBytes sig
      let h := P.scalarFromWide hDigest
      let sScalar := P.scalarFromBytesModOrder sClamped
      P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar) == capR
  else
    false

theorem xeddsaVerifyRo_eq (P : Primitives) (pk m sig : Bytes) :
    xeddsaVerifyRo P pk m sig =
      match xeddsaVerifyChalInput? P pk m sig with
      | none => pure false
      | some chalIn => do
          let hDigest ← liftM (OracleSpec.query (spec := sha512RoSpec) chalIn)
          return xeddsaVerifyWithDigest P pk m sig hDigest := by
  unfold xeddsaVerifyRo xeddsaVerifyChalInput? xeddsaVerifyWithDigest sigRespBytes
  split_ifs with hg
  · dsimp only
    cases hmont : P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) <;> simp
  · simp

private theorem uint8_signBit_bool (b : UInt8) :
    ((b &&& 0x80) >>> 7) = 0 ∨ ((b &&& 0x80) >>> 7) = 1 := by
  have hcheck : ∀ i : Fin 256,
      ((UInt8.ofNat i.val &&& 0x80) >>> 7) = 0 ∨
        ((UInt8.ofNat i.val &&& 0x80) >>> 7) = 1 := by decide
  have hofNat : UInt8.ofNat b.toNat = b :=
    UInt8.toNat_inj.mp (UInt8.toNat_ofNat_of_lt' b.toBitVec.isLt)
  simpa [hofNat] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

theorem xeddsaVerifyWithDigest_spec {P : Primitives} (C : XeddsaCurveWitness P)
    {sk m sig hDigest : Bytes}
    (hacc : xeddsaVerifyWithDigest P (P.x25519Base sk) m sig hDigest = true) :
    sig.length = 64 ∧
      ∃ y : ZMod l25519,
        (y = clampedScalarZMod sk ∨ y = -clampedScalarZMod sk) ∧
        xeddsaVerifyChalInput? P (P.x25519Base sk) m sig =
          some (sig.take 32 ++ C.compressEd y ++ m) ∧
        sig.take 32 =
          C.compressEd (decodeScalarBytes (fitBytesRef 64 hDigest) * (-y) + sigRespScalar sig) ∧
        isH1Input (sig.take 32 ++ C.compressEd y ++ m) = false ∧
        (sig.take 32 ++ C.compressEd y ++ m).drop 64 = m := by
  unfold xeddsaVerifyWithDigest at hacc
  split_ifs at hacc with hg
  have hsig_len : sig.length = 64 := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact hg.1.2
  set signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
  obtain ⟨edPk, hmont, hrep⟩ :=
    C.montToEd_base sk signBit (uint8_signBit_bool (sig.getD 63 0))
  set y : ZMod l25519 :=
    if signBit == C.edSign (clampedScalarZMod sk) then clampedScalarZMod sk
    else -clampedScalarZMod sk
  have hy_pm : y = clampedScalarZMod sk ∨ y = -clampedScalarZMod sk := by
    dsimp only [y]; split_ifs <;> simp
  have hchal :
      xeddsaVerifyChalInput? P (P.x25519Base sk) m sig =
        some (sig.take 32 ++ C.compressEd y ++ m) := by
    unfold xeddsaVerifyChalInput?
    rw [ite_eq_left hg]
    dsimp only
    change (match P.montToEd (P.x25519Base sk) signBit with
      | none => none
      | some edPk => some (sig.take 32 ++ P.compress edPk ++ m)) = _
    rw [hmont]
    dsimp only
    rw [C.compress_of_represents hrep]
  change (match P.montToEd (P.x25519Base sk) signBit with
    | none => false
    | some edPk => _) = true at hacc
  rw [hmont] at hacc
  dsimp only at hacc
  rw [beq_iff_eq] at hacc
  set hScalar : ZMod l25519 := decodeScalarBytes (fitBytesRef 64 hDigest)
  have hdsmb_rep :
      C.RepresentsEd (hScalar * (-y) + sigRespScalar sig)
        (P.doubleScalarMulBasepoint (P.scalarFromWide hDigest) (P.edNeg edPk)
          (P.scalarFromBytesModOrder (sigRespBytes sig))) := by
    rw [C.scalarWide_eq hDigest, C.scalarMod_eq (sigRespBytes sig)]
    exact C.dsmb_represents hScalar (sigRespScalar sig) (C.edNeg_represents hrep)
  have hcapR_eq :
      sig.take 32 = C.compressEd (hScalar * (-y) + sigRespScalar sig) := by
    rw [← hacc, C.compress_of_represents hdsmb_rep]
  have hcapR_len : (sig.take 32).length = 32 := by
    rw [hcapR_eq]; exact C.compressEd_len _
  have hcapA_len : (C.compressEd y).length = 32 := C.compressEd_len y
  have hinRange : scalarIsInRange (clearSignBit32 (sig.take 32)) = true := by
    rw [hcapR_eq]; exact C.compressEd_inRange _
  have hnoH1 : isH1Input (sig.take 32 ++ C.compressEd y ++ m) = false := by
    rw [List.append_assoc]
    exact isH1Input_false_of_scalarIsInRange hcapR_len hinRange
  have hdrop64 : (sig.take 32 ++ C.compressEd y ++ m).drop 64 = m := by
    have h64 : (sig.take 32 ++ C.compressEd y).length = 64 := by
      simp [hcapR_len, hcapA_len]
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append]
  exact ⟨hsig_len, y, hy_pm, hchal, hcapR_eq, hnoH1, hdrop64⟩

/-- Recovers a 32-byte clamped X25519 scalar from two signatures `(sig₁, sig₂)` and distinct
    challenges `(h₁, h₂)` in `ZMod l25519`. -/
noncomputable def extractClampedKey (sig₁ sig₂ : Bytes) (h₁ h₂ : ZMod l25519) : Bytes :=
  recoverClampedScalar ((sigRespScalar sig₁ - sigRespScalar sig₂) * (h₁ - h₂)⁻¹)

/-- Two accepting verifications on `P.x25519Base sk` sharing the same challenge input under distinct
    challenges `h₁ ≠ h₂` recover `±clampedScalarZMod sk`. -/
theorem extractScalar_pm_of_two_accepts {P : Primitives} (C : XeddsaCurveWitness P)
    {sk m₁ sig₁ w₁ m₂ sig₂ w₂ : Bytes} {h₁ h₂ : ZMod l25519}
    (hacc₁ : xeddsaVerifyWithDigest P (P.x25519Base sk) m₁ sig₁ w₁ = true)
    (hacc₂ : xeddsaVerifyWithDigest P (P.x25519Base sk) m₂ sig₂ w₂ = true)
    (hchal : xeddsaVerifyChalInput? P (P.x25519Base sk) m₁ sig₁ =
      xeddsaVerifyChalInput? P (P.x25519Base sk) m₂ sig₂)
    (hh₁ : decodeScalarBytes (fitBytesRef 64 w₁) = h₁)
    (hh₂ : decodeScalarBytes (fitBytesRef 64 w₂) = h₂)
    (hne : h₁ ≠ h₂) :
    let aExt := (sigRespScalar sig₁ - sigRespScalar sig₂) * (h₁ - h₂)⁻¹
    aExt = clampedScalarZMod sk ∨ aExt = -clampedScalarZMod sk := by
  obtain ⟨hsig₁, y₁, hy₁_pm, hchal₁, hcapR₁, _, _⟩ := xeddsaVerifyWithDigest_spec C hacc₁
  obtain ⟨hsig₂, y₂, _, hchal₂, hcapR₂, _, _⟩ := xeddsaVerifyWithDigest_spec C hacc₂
  rw [hh₁] at hcapR₁
  rw [hh₂] at hcapR₂
  have hconcat : sig₁.take 32 ++ (C.compressEd y₁ ++ m₁) =
      sig₂.take 32 ++ (C.compressEd y₂ ++ m₂) := by
    rw [hchal₁, hchal₂] at hchal
    simpa [List.append_assoc] using Option.some.inj hchal
  have hlenR₁ : (sig₁.take 32).length = 32 := by simp [hsig₁]
  have hlenR₂ : (sig₂.take 32).length = 32 := by simp [hsig₂]
  have hlenA₁ : (C.compressEd y₁).length = 32 := C.compressEd_len y₁
  have hlenA₂ : (C.compressEd y₂).length = 32 := C.compressEd_len y₂
  have hR_eq : sig₁.take 32 = sig₂.take 32 := by
    have ht := congrArg (List.take 32) hconcat
    simpa only [List.take_append_of_le_length (by omega : 32 ≤ (sig₁.take 32).length),
      List.take_append_of_le_length (by omega : 32 ≤ (sig₂.take 32).length),
      List.take_of_length_le (by omega : (sig₁.take 32).length ≤ 32),
      List.take_of_length_le (by omega : (sig₂.take 32).length ≤ 32)] using ht
  have hA_eq : C.compressEd y₁ = C.compressEd y₂ := by
    have hd := congrArg (fun l => (l.drop 32).take 32) hconcat
    simpa only [List.drop_append_of_le_length (by omega : 32 ≤ (sig₁.take 32).length),
      List.drop_append_of_le_length (by omega : 32 ≤ (sig₂.take 32).length),
      List.drop_eq_nil_of_le (by omega : (sig₁.take 32).length ≤ 32),
      List.drop_eq_nil_of_le (by omega : (sig₂.take 32).length ≤ 32),
      List.nil_append, hlenR₁, hlenR₂, Nat.sub_self, List.drop_zero,
      List.take_append_of_le_length (by omega : 32 ≤ (C.compressEd y₁).length),
      List.take_append_of_le_length (by omega : 32 ≤ (C.compressEd y₂).length),
      List.take_of_length_le (by omega : (C.compressEd y₁).length ≤ 32),
      List.take_of_length_le (by omega : (C.compressEd y₂).length ≤ 32)] using hd
  have hy_eq : y₁ = y₂ := C.compressEd_inj hA_eq
  subst hy_eq
  have hlin : h₁ * (-y₁) + sigRespScalar sig₁ = h₂ * (-y₁) + sigRespScalar sig₂ := by
    apply C.compressEd_inj
    rw [← hcapR₁, ← hcapR₂, hR_eq]
  have hsub : sigRespScalar sig₁ - sigRespScalar sig₂ = (h₁ - h₂) * y₁ := by
    calc sigRespScalar sig₁ - sigRespScalar sig₂
        = (h₁ * (-y₁) + sigRespScalar sig₁) - (h₂ * (-y₁) + sigRespScalar sig₂) +
            (h₁ - h₂) * y₁ := by ring
      _ = (h₁ - h₂) * y₁ := by rw [hlin, sub_self, zero_add]
  have hdiff_ne : h₁ - h₂ ≠ 0 := sub_ne_zero.mpr hne
  have haExt : (sigRespScalar sig₁ - sigRespScalar sig₂) * (h₁ - h₂)⁻¹ = y₁ := by
    rw [hsub, mul_right_comm, mul_inv_cancel₀ hdiff_ne, one_mul]
  dsimp only
  rwa [haExt]

/-- On a successful fork of `P.x25519Base sk` against `P.x25519Base v`, `extractClampedKey` computes
    the shared secret `P.x25519 sk (P.x25519Base v)`. -/
theorem x25519_extractClampedKey_eq {P : Primitives}
    (hWF : WellFormedPrimitivesδ P) (C : XeddsaCurveWitness P)
    {sk v m₁ sig₁ w₁ m₂ sig₂ w₂ : Bytes} {h₁ h₂ : ZMod l25519}
    (hsk_len : sk.length = 32)
    (hacc₁ : xeddsaVerifyWithDigest P (P.x25519Base sk) m₁ sig₁ w₁ = true)
    (hacc₂ : xeddsaVerifyWithDigest P (P.x25519Base sk) m₂ sig₂ w₂ = true)
    (hchal : xeddsaVerifyChalInput? P (P.x25519Base sk) m₁ sig₁ =
      xeddsaVerifyChalInput? P (P.x25519Base sk) m₂ sig₂)
    (hh₁ : decodeScalarBytes (fitBytesRef 64 w₁) = h₁)
    (hh₂ : decodeScalarBytes (fitBytesRef 64 w₂) = h₂)
    (hne : h₁ ≠ h₂) :
    P.x25519 (extractClampedKey sig₁ sig₂ h₁ h₂) (P.x25519Base v) =
      P.x25519 sk (P.x25519Base v) := by
  have haExt := extractScalar_pm_of_two_accepts C hacc₁ hacc₂ hchal hh₁ hh₂ hne
  obtain ⟨_, hpm⟩ := recoverClampedScalar_spec haExt
  have hbase_eq : P.x25519Base (extractClampedKey sig₁ sig₂ h₁ h₂) = P.x25519Base sk :=
    C.x25519Base_eq_of_clamped_pm _ _ hpm
  exact hWF.x25519_congr_of_base_eq (extractClampedKey sig₁ sig₂ h₁ h₂) sk (P.x25519Base v)
    (recoverClampedScalar_length _) hsk_len (Or.inl (hWF.canon_base v)) hbase_eq

/-! ## Deterministic side-oracle commutation with `OracleComp.contextFork` -/

abbrev ForkSpec : OracleSpec (((ℕ ⊕ PrimQuery) ⊕ DdhQuery) ⊕ Unit) :=
  (PrimBaseSpec + gapDhOracleSpec) + (Unit →ₒ ZMod l25519)

def primEval (P : Primitives) : (q : PrimQuery) → primSpec.Range q
  | .x25519 sk pk          => P.x25519 sk pk
  | .x25519Base sk         => P.x25519Base sk
  | .isCanonical pk        => P.isCanonical pk
  | .pow8 pk               => P.pow8 pk
  | .sigPkGen sk           => P.sigPkGen sk
  | .sigSign sk m r        => P.sigSign sk m r
  | .sigVerify pk m sg     => P.sigVerify pk m sg
  | .kemKeyGen seed        => P.kemKeyGen seed
  | .kemEncaps pk r        => P.kemEncaps pk r
  | .kemDecaps sk ct       => P.kemDecaps sk ct
  | .hkdfDerive96 ikm      => P.hkdfDerive96 ikm
  | .rootCreateChain rk dh => P.rootCreateChain rk dh
  | .chainKdfSeed ck       => P.chainKdfSeed ck
  | .chainKdfNext ck       => P.chainKdfNext ck
  | .spqrInitSend q r      => P.spqrInitSend q r
  | .spqrInitRecv q m      => P.spqrInitRecv q m
  | .deriveMsgKeys m s     => P.deriveMsgKeys m s
  | .aeadEnc mk ad pt      => P.aeadEnc mk ad pt
  | .aeadDec mk ad ct      => P.aeadDec mk ad ct

private theorem primImpl_eq_pure_primEval (P : Primitives) (q : PrimQuery) :
    primImpl P q = pure (primEval P q) := by
  cases q <;> rfl

def sideImpl (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl ForkSpec (OracleComp ChalZModSpec)
  | .inl (.inl (.inl n))  => PFunctor.FreeM.lift (P := ChalZModSpec.toPFunctor) (Sum.inl n)
  | .inl (.inl (.inr p))  => pure (primEval P p)
  | .inl (.inr (X, Y, Z)) => pure (isValidDhTriple X Y Z)
  | .inr ()               => PFunctor.FreeM.lift (P := ChalZModSpec.toPFunctor) (Sum.inr ())

/-- Eliminates deterministic side queries from an `OracleComp ForkSpec` tree by structural
    recursion, preserving `implicit_reducible` path indices. -/
@[implicit_reducible]
def elimSide (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) {α : Type} :
    OracleComp ForkSpec α → OracleComp ChalZModSpec α
  | .pure x => .pure x
  | .liftBind (.inl (.inl (.inl n))) next =>
      .liftBind (.inl n) (fun ans => elimSide P isValidDhTriple (next ans))
  | .liftBind (.inl (.inl (.inr p))) next =>
      elimSide P isValidDhTriple (next (primEval P p))
  | .liftBind (.inl (.inr (X, Y, Z))) next =>
      elimSide P isValidDhTriple (next (isValidDhTriple X Y Z))
  | .liftBind (.inr ()) next =>
      .liftBind (.inr ()) (fun ans => elimSide P isValidDhTriple (next ans))

theorem simulateQ_sideImpl_eq_elimSide
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    {α : Type} (m : OracleComp ForkSpec α) :
    simulateQ (sideImpl P isValidDhTriple) m = elimSide P isValidDhTriple m := by
  change PFunctor.FreeM.liftM (sideImpl P isValidDhTriple) m = elimSide P isValidDhTriple m
  induction m using PFunctor.FreeM.rec with
  | pure _ => rfl
  | liftBind a next ih =>
      rcases a with (((n | p) | ⟨X, Y, Z⟩) | u)
      · dsimp only [PFunctor.FreeM.liftM, sideImpl, elimSide]
        change PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n)
            (fun ans => PFunctor.FreeM.liftM (sideImpl P isValidDhTriple) (next ans)) =
          PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n)
            (fun ans => elimSide P isValidDhTriple (next ans))
        exact congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n))
          (funext ih)
      · exact ih (primEval P p)
      · exact ih (isValidDhTriple X Y Z)
      · cases u
        dsimp only [PFunctor.FreeM.liftM, sideImpl, elimSide]
        change PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ())
            (fun ans => PFunctor.FreeM.liftM (sideImpl P isValidDhTriple) (next ans)) =
          PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ())
            (fun ans => elimSide P isValidDhTriple (next ans))
        exact congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ()))
          (funext ih)

noncomputable def answerChalOnBase :
    QueryImpl ForkSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec))
  | .inl q  => liftM ((PrimBaseSpec + gapDhOracleSpec).query q)
  | .inr () =>
      simulateQ (QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec)))
        ($ᵗ (ZMod l25519))

theorem evalSide_comp_answerChalOnBase
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    (primBaseImpl P + ddhImpl) ∘ₛ answerChalOnBase =
      evalChalZMod ∘ₛ sideImpl P isValidDhTriple := by
  intro ddhImpl
  funext t
  rcases t with (((n | p) | ⟨X, Y, Z⟩) | ⟨⟩)
  · rw [QueryImpl.apply_compose, QueryImpl.apply_compose, answerChalOnBase, simulateQ_spec_query]
    rfl
  · rw [QueryImpl.apply_compose, QueryImpl.apply_compose, answerChalOnBase, sideImpl,
      simulateQ_spec_query, simulateQ_pure]
    change primImpl P p = pure (primEval P p)
    exact primImpl_eq_pure_primEval P p
  · rw [QueryImpl.apply_compose, QueryImpl.apply_compose, answerChalOnBase, sideImpl,
      simulateQ_spec_query, simulateQ_pure]
    rfl
  · rw [QueryImpl.apply_compose, QueryImpl.apply_compose, answerChalOnBase, sideImpl]
    have hlhs :
        simulateQ (primBaseImpl P + ddhImpl)
          (simulateQ (QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec)))
            ($ᵗ (ZMod l25519))) = $ᵗ (ZMod l25519) := by
      rw [← QueryImpl.simulateQ_compose]
      have hid : (primBaseImpl P + ddhImpl) ∘ₛ
          QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec)) =
          QueryImpl.id' unifSpec := by
        funext n
        rw [QueryImpl.apply_compose, QueryImpl.ofLift_apply]
        change simulateQ (primBaseImpl P + ddhImpl)
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query (Sum.inl (Sum.inl n)))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hid, simulateQ_id']
    rw [hlhs]
    change ($ᵗ (ZMod l25519)) =
      simulateQ evalChalZMod (liftM (ChalZModSpec.query (Sum.inr ())))
    rw [simulateQ_spec_query]
    change ($ᵗ (ZMod l25519)) = (uniformSampleImpl (spec := (Unit →ₒ ZMod l25519))) ()
    rw [uniformSampleImpl_apply]

section SideElim

attribute [local implicit_reducible] PFunctor.FreeM.bind PFunctor.FreeM.lift PFunctor.FreeM.map

private theorem contextFork_eq_bind_withPath {ι α : Type} {spec : OracleSpec ι}
    [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp.contextFork main qb i cf =
      PFunctor.FreeM.bind (PFunctor.FreeM.withPath main) fun path =>
        match cf (PFunctor.FreeM.output main path) with
        | none => pure none
        | some s =>
            match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s.val with
            | none => pure none
            | some located =>
                PFunctor.FreeM.map (OracleComp.classifyForkView main qb i cf s) located.fork := by
  unfold OracleComp.contextFork OracleComp.contextForkWitness
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy]
  unfold PFunctor.FreeM.Cursor.filterMapLocateAndForkBy
  rw [← PFunctor.FreeM.comp_map, PFunctor.FreeM.Cursor.map_locateAndForkBy]
  apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath main))
  funext path
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · rfl
  · rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path s.val with
      _ | located
    · simp [hloc]
    · simp only [hloc]
      apply congrArg (fun f => PFunctor.FreeM.map f located.fork)
      funext view
      simp only [Function.comp_apply, Option.join, Option.map]
      unfold OracleComp.acceptContextForkWitness OracleComp.classifyForkView
      split <;> split <;> simp_all
      grind

@[implicit_reducible]
private def embedPath (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) {α : Type} :
    (m : OracleComp ForkSpec α) →
      PFunctor.FreeM.Path (elimSide P ddh m) → PFunctor.FreeM.Path m
  | .pure _, _ => ⟨⟩
  | .liftBind (.inl (.inl (.inl _))) next, ⟨ans, suffix⟩ =>
      ⟨ans, embedPath P ddh (next ans) suffix⟩
  | .liftBind (.inl (.inl (.inr p))) next, path =>
      ⟨primEval P p, embedPath P ddh (next (primEval P p)) path⟩
  | .liftBind (.inl (.inr (X, Y, Z))) next, path =>
      ⟨ddh X Y Z, embedPath P ddh (next (ddh X Y Z)) path⟩
  | .liftBind (.inr ()) next, ⟨ans, suffix⟩ =>
      ⟨ans, embedPath P ddh (next ans) suffix⟩

private theorem elimSide_map (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α β : Type} (f : α → β) (m : OracleComp ForkSpec α) :
    elimSide P ddh (PFunctor.FreeM.map f m) = PFunctor.FreeM.map f (elimSide P ddh m) := by
  rw [← simulateQ_sideImpl_eq_elimSide, ← simulateQ_sideImpl_eq_elimSide]
  exact simulateQ_map (sideImpl P ddh) m f

private theorem elimSide_bind (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α β : Type} (m : OracleComp ForkSpec α) (f : α → OracleComp ForkSpec β) :
    elimSide P ddh (PFunctor.FreeM.bind m f) =
      PFunctor.FreeM.bind (elimSide P ddh m) (fun a => elimSide P ddh (f a)) := by
  induction m using PFunctor.FreeM.rec with
  | pure _ => rfl
  | liftBind a next ih =>
      rcases a with (((n | p) | ⟨X, Y, Z⟩) | u)
      · dsimp only [PFunctor.FreeM.bind, elimSide]
        exact congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n))
          (funext ih)
      · exact ih (primEval P p)
      · exact ih (ddh X Y Z)
      · cases u
        dsimp only [PFunctor.FreeM.bind, elimSide]
        exact congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ()))
          (funext ih)

private theorem elimSide_withPath (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) {α : Type}
    (m : OracleComp ForkSpec α) :
    elimSide P ddh (PFunctor.FreeM.withPath m) =
      PFunctor.FreeM.map (embedPath P ddh m) (PFunctor.FreeM.withPath (elimSide P ddh m)) := by
  induction m using PFunctor.FreeM.rec with
  | pure _ => rfl
  | liftBind a next ih =>
      rcases a with (((n | p) | ⟨X, Y, Z⟩) | u)
      · dsimp only [PFunctor.FreeM.withPath, elimSide]
        simp only [elimSide_map, PFunctor.FreeM.map]
        apply congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n))
        funext ans
        rw [ih ans, ← PFunctor.FreeM.comp_map, ← PFunctor.FreeM.comp_map]
        rfl
      · dsimp only [PFunctor.FreeM.withPath, elimSide]
        rw [elimSide_map, ih (primEval P p), ← PFunctor.FreeM.comp_map]
        rfl
      · dsimp only [PFunctor.FreeM.withPath, elimSide]
        rw [elimSide_map, ih (ddh X Y Z), ← PFunctor.FreeM.comp_map]
        rfl
      · cases u
        dsimp only [PFunctor.FreeM.withPath, elimSide]
        simp only [elimSide_map, PFunctor.FreeM.map]
        apply congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ()))
        funext ans
        rw [ih ans, ← PFunctor.FreeM.comp_map, ← PFunctor.FreeM.comp_map]
        rfl

private theorem output_embedPath (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) {α : Type} :
    (m : OracleComp ForkSpec α) → (path : PFunctor.FreeM.Path (elimSide P ddh m)) →
      PFunctor.FreeM.output m (embedPath P ddh m path) =
        PFunctor.FreeM.output (elimSide P ddh m) path
  | .pure _, _ => rfl
  | .liftBind (.inl (.inl (.inl _))) next, ⟨ans, suffix⟩ =>
      output_embedPath P ddh (next ans) suffix
  | .liftBind (.inl (.inl (.inr p))) next, path =>
      output_embedPath P ddh (next (primEval P p)) path
  | .liftBind (.inl (.inr (X, Y, Z))) next, path =>
      output_embedPath P ddh (next (ddh X Y Z)) path
  | .liftBind (.inr ()) next, ⟨ans, suffix⟩ =>
      output_embedPath P ddh (next ans) suffix

abbrev forkQbFork (q_H : ℕ) : ForkSpec.Domain → ℕ
  | .inr () => q_H
  | _       => 0

abbrev forkQbChal (q_H : ℕ) : ChalZModSpec.Domain → ℕ
  | .inr () => q_H
  | _       => 0

private def classifyForkViewAt {ι α : Type} {spec : OracleSpec ι}
    [∀ t, DecidableEq (spec.Range t)] (main : OracleComp spec α)
    (q_H : ℕ) (i : ι) (cf : α → Option (Fin (q_H + 1))) (s : Fin (q_H + 1)) (k : Nat)
    (view : PFunctor.FreeM.Cursor.ForkView (P := spec.toPFunctor) i main k) :
    Option (α × α) :=
  let x₁ := PFunctor.FreeM.output main view.firstPath
  let x₂ := PFunctor.FreeM.output main view.secondPath
  if view.firstAnswer = view.secondAnswer then none
  else if cf x₁ = some s ∧ cf x₂ = some s then some (x₁, x₂)
  else none

private theorem classifyForkViewAt_comp_prependOther {ι α : Type} {spec : OracleSpec ι}
    [∀ t, DecidableEq (spec.Range t)] {i a : ι} {next : spec.Range a → OracleComp spec α}
    (hne : a ≠ i) (ans : spec.Range a) (q_H : ℕ)
    (cf : α → Option (Fin (q_H + 1))) (s : Fin (q_H + 1)) (k : Nat) :
    classifyForkViewAt (PFunctor.FreeM.liftBind (P := spec.toPFunctor) a next) q_H i cf s k ∘
      PFunctor.FreeM.Cursor.ForkView.prependOther hne ans =
      classifyForkViewAt (next ans) q_H i cf s k := by
  funext _
  rfl

private theorem classifyForkViewAt_comp_prependSame {ι α : Type} {spec : OracleSpec ι}
    [∀ t, DecidableEq (spec.Range t)] {i : ι} {next : spec.Range i → OracleComp spec α}
    (ans : spec.Range i) (q_H : ℕ)
    (cf : α → Option (Fin (q_H + 1))) (s : Fin (q_H + 1)) (k : Nat) :
    classifyForkViewAt (PFunctor.FreeM.liftBind (P := spec.toPFunctor) i next) q_H i cf s (k + 1) ∘
      PFunctor.FreeM.Cursor.ForkView.prependSame ans =
      classifyForkViewAt (next ans) q_H i cf s k := by
  funext _
  rfl

private theorem located_fork_here {ι α : Type} {spec : OracleSpec ι}
    [∀ t, DecidableEq (spec.Range t)]
    {target : ι} (next : spec.Range target → OracleComp spec α)
    (ans : spec.Range target) (suffix : PFunctor.FreeM.Path (next ans))
    (q_H : ℕ) (cf : α → Option (Fin (q_H + 1))) (s : Fin (q_H + 1)) :
    PFunctor.FreeM.map (P := spec.toPFunctor)
        (classifyForkViewAt (PFunctor.FreeM.liftBind (P := spec.toPFunctor) target next)
          q_H target cf s 0)
        (PFunctor.FreeM.Cursor.Located.here (P := spec.toPFunctor) (target := target)
          next ans suffix).fork =
      PFunctor.FreeM.liftBind (P := spec.toPFunctor) target (fun secondAnswer =>
        PFunctor.FreeM.map (fun secondSuffix =>
          let x₁ := PFunctor.FreeM.output (next ans) suffix
          let x₂ := PFunctor.FreeM.output (next secondAnswer) secondSuffix
          if ans = secondAnswer then none
          else if cf x₁ = some s ∧ cf x₂ = some s then some (x₁, x₂) else none)
          (PFunctor.FreeM.withPath (next secondAnswer))) := by
  dsimp only [PFunctor.FreeM.Cursor.Located.fork, PFunctor.FreeM.Cursor.Located.here,
    PFunctor.FreeM.Cursor.Occurrence.resume, PFunctor.FreeM.map]
  apply congrArg (PFunctor.FreeM.liftBind (P := spec.toPFunctor) target)
  funext secondAnswer
  rw [← PFunctor.FreeM.comp_map]
  rfl

private def forkOrNoneChal {α : Type} {m : OracleComp ChalZModSpec α}
    {path : PFunctor.FreeM.Path m} {k : Nat}
    (f : PFunctor.FreeM.Cursor.ForkView (P := ChalZModSpec.toPFunctor) (Sum.inr ()) m k →
      Option (α × α)) :
    Option (PFunctor.FreeM.Cursor.Located (P := ChalZModSpec.toPFunctor) (Sum.inr ()) m path k) →
      OracleComp ChalZModSpec (Option (α × α))
  | none => pure none
  | some loc => PFunctor.FreeM.map f loc.fork

private theorem elimSide_locateAndClassify (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α : Type} [DecidableEq ForkSpec.Domain] [∀ t, DecidableEq (ForkSpec.Range t)]
    (q_H : ℕ) (cf : α → Option (Fin (q_H + 1))) (s : Fin (q_H + 1))
    (m : OracleComp ForkSpec α) (path : PFunctor.FreeM.Path (elimSide P ddh m)) (k : Nat) :
    (match PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
        m (embedPath P ddh m path) k with
      | none => pure none
      | some loc =>
          elimSide P ddh
            (PFunctor.FreeM.map (classifyForkViewAt m q_H (Sum.inr ()) cf s k)
              loc.fork)) =
      forkOrNoneChal
        (classifyForkViewAt (elimSide P ddh m) q_H (Sum.inr ()) cf s k)
        (PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
          (elimSide P ddh m) path k) := by
  induction m using PFunctor.FreeM.rec generalizing k with
  | pure _ => rfl
  | liftBind a next ih =>
      rcases a with (((n | p) | ⟨X, Y, Z⟩) | u)
      · rcases path with ⟨ans, suffix⟩
        dsimp only [embedPath]
        change _ =
          forkOrNoneChal
            (classifyForkViewAt
              (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n)
                (fun b => elimSide P ddh (next b))) q_H (Sum.inr ()) cf s k)
            (PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
              (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inl n)
                (fun b => elimSide P ddh (next b))) ⟨ans, suffix⟩ k)
        rw [PFunctor.FreeM.Cursor.locateAt?_liftBind_other (by simp),
          PFunctor.FreeM.Cursor.locateAt?_liftBind_other (by simp)]
        have ih' := ih ans suffix k
        rcases h1 : PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
            (next ans) (embedPath P ddh (next ans) suffix) k with _ | loc₁ <;>
          rcases h2 : PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
            (elimSide P ddh (next ans)) suffix k with _ | loc₂
        · rfl
        · rw [h1, h2] at ih'
          dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
          rw [PFunctor.FreeM.Cursor.Located.fork_prependOther, ← PFunctor.FreeM.comp_map,
            classifyForkViewAt_comp_prependOther]
          exact ih'
        · rw [h1, h2] at ih'
          dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
          rw [PFunctor.FreeM.Cursor.Located.fork_prependOther, ← PFunctor.FreeM.comp_map,
            classifyForkViewAt_comp_prependOther]
          exact ih'
        · rw [h1, h2] at ih'
          dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
          rw [PFunctor.FreeM.Cursor.Located.fork_prependOther,
            PFunctor.FreeM.Cursor.Located.fork_prependOther,
            ← PFunctor.FreeM.comp_map, ← PFunctor.FreeM.comp_map,
            classifyForkViewAt_comp_prependOther, classifyForkViewAt_comp_prependOther]
          exact ih'
      · dsimp only [embedPath]
        change _ =
          forkOrNoneChal
            (classifyForkViewAt (elimSide P ddh (next (primEval P p)))
              q_H (Sum.inr ()) cf s k)
            (PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
              (elimSide P ddh (next (primEval P p))) path k)
        rw [PFunctor.FreeM.Cursor.locateAt?_liftBind_other (by simp)]
        have ih' := ih (primEval P p) path k
        rcases h1 : PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
            (next (primEval P p)) (embedPath P ddh (next (primEval P p)) path) k with _ | loc₁
        · rw [h1] at ih'; exact ih'
        · rw [h1] at ih'
          dsimp only [Option.map]
          rw [PFunctor.FreeM.Cursor.Located.fork_prependOther, ← PFunctor.FreeM.comp_map,
            classifyForkViewAt_comp_prependOther]
          exact ih'
      · dsimp only [embedPath]
        change _ =
          forkOrNoneChal
            (classifyForkViewAt (elimSide P ddh (next (ddh X Y Z)))
              q_H (Sum.inr ()) cf s k)
            (PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
              (elimSide P ddh (next (ddh X Y Z))) path k)
        rw [PFunctor.FreeM.Cursor.locateAt?_liftBind_other (by simp)]
        have ih' := ih (ddh X Y Z) path k
        rcases h1 : PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
            (next (ddh X Y Z)) (embedPath P ddh (next (ddh X Y Z)) path) k with _ | loc₁
        · rw [h1] at ih'; exact ih'
        · rw [h1] at ih'
          dsimp only [Option.map]
          rw [PFunctor.FreeM.Cursor.Located.fork_prependOther, ← PFunctor.FreeM.comp_map,
            classifyForkViewAt_comp_prependOther]
          exact ih'
      · cases u
        rcases path with ⟨ans, suffix⟩
        dsimp only [embedPath]
        change _ =
          forkOrNoneChal
            (classifyForkViewAt
              (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ())
                (fun b => elimSide P ddh (next b))) q_H (Sum.inr ()) cf s k)
            (PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
              (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ())
                (fun b => elimSide P ddh (next b))) ⟨ans, suffix⟩ k)
        cases k with
        | zero =>
            rw [PFunctor.FreeM.Cursor.locateAt?_liftBind_same_zero,
              PFunctor.FreeM.Cursor.locateAt?_liftBind_same_zero]
            dsimp only [forkOrNoneChal]
            rw [located_fork_here, located_fork_here]
            dsimp only [elimSide]
            apply congrArg (PFunctor.FreeM.liftBind (P := ChalZModSpec.toPFunctor) (Sum.inr ()))
            funext secondAnswer
            rw [elimSide_map, elimSide_withPath, ← PFunctor.FreeM.comp_map]
            apply congrArg (fun f => PFunctor.FreeM.map f
              (PFunctor.FreeM.withPath (elimSide P ddh (next secondAnswer))))
            funext secondSuffix
            dsimp only [Function.comp_apply]
            by_cases hEq : ans = secondAnswer <;> simp [hEq, output_embedPath]
        | succ k =>
            rw [PFunctor.FreeM.Cursor.locateAt?_liftBind_same_succ,
              PFunctor.FreeM.Cursor.locateAt?_liftBind_same_succ]
            have ih' := ih ans suffix k
            rcases h1 : PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
                (next ans) (embedPath P ddh (next ans) suffix) k with _ | loc₁ <;>
              rcases h2 : PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor)
                (Sum.inr ()) (elimSide P ddh (next ans)) suffix k with _ | loc₂
            · rfl
            · rw [h1, h2] at ih'
              dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
              rw [PFunctor.FreeM.Cursor.Located.fork_prependSame, ← PFunctor.FreeM.comp_map,
                classifyForkViewAt_comp_prependSame]
              exact ih'
            · rw [h1, h2] at ih'
              dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
              rw [PFunctor.FreeM.Cursor.Located.fork_prependSame, ← PFunctor.FreeM.comp_map,
                classifyForkViewAt_comp_prependSame]
              exact ih'
            · rw [h1, h2] at ih'
              dsimp only [Option.map, forkOrNoneChal] at ih' ⊢
              rw [PFunctor.FreeM.Cursor.Located.fork_prependSame,
                PFunctor.FreeM.Cursor.Located.fork_prependSame,
                ← PFunctor.FreeM.comp_map, ← PFunctor.FreeM.comp_map,
                classifyForkViewAt_comp_prependSame, classifyForkViewAt_comp_prependSame]
              exact ih'

/-- Evaluating deterministic side queries via `elimSide` commutes with `OracleComp.contextFork` at
    the challenge oracle `.inr ()`. -/
theorem elimSide_contextFork_eq (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α : Type} [DecidableEq ForkSpec.Domain] [∀ t, DecidableEq (ForkSpec.Range t)]
    (main : OracleComp ForkSpec α) (q_H : ℕ) (cf : α → Option (Fin (q_H + 1))) :
    simulateQ (sideImpl P ddh)
      (OracleComp.contextFork main (forkQbFork q_H) (Sum.inr ()) cf) =
      OracleComp.contextFork (elimSide P ddh main) (forkQbChal q_H) (Sum.inr ()) cf := by
  rw [simulateQ_sideImpl_eq_elimSide, contextFork_eq_bind_withPath, contextFork_eq_bind_withPath,
    elimSide_bind, elimSide_withPath, ← PFunctor.FreeM.bind_pure_comp, PFunctor.FreeM.bind_assoc]
  apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath (elimSide P ddh main)))
  funext path
  simp only [Function.comp_apply, PFunctor.FreeM.pure_bind]
  rw [output_embedPath]
  rcases cf (PFunctor.FreeM.output (elimSide P ddh main) path) with _ | s
  · rfl
  · dsimp only
    have hcfv₁ : OracleComp.classifyForkView main (forkQbFork q_H) (Sum.inr ()) cf s =
        classifyForkViewAt main q_H (Sum.inr ()) cf s s.val := by
      funext v; simp [OracleComp.classifyForkView, classifyForkViewAt]
    have hcfv₂ : OracleComp.classifyForkView (elimSide P ddh main) (forkQbChal q_H) (Sum.inr ()) cf s =
        classifyForkViewAt (elimSide P ddh main) q_H (Sum.inr ()) cf s s.val := by
      funext v; simp [OracleComp.classifyForkView, classifyForkViewAt]
    have h := elimSide_locateAndClassify P ddh q_H cf s main path s.val
    rcases h1 : PFunctor.FreeM.Cursor.locateAt? (P := ForkSpec.toPFunctor) (Sum.inr ())
        main (embedPath P ddh main path) s.val with _ | loc₁ <;>
      rcases h2 : PFunctor.FreeM.Cursor.locateAt? (P := ChalZModSpec.toPFunctor) (Sum.inr ())
        (elimSide P ddh main) path s.val with _ | loc₂
    · rfl
    · rw [h1, h2] at h; dsimp only [forkOrNoneChal] at h ⊢; rw [hcfv₂]; exact h
    · rw [h1, h2] at h; dsimp only [forkOrNoneChal] at h ⊢; rw [hcfv₁]; exact h
    · rw [h1, h2] at h; dsimp only [forkOrNoneChal] at h ⊢; rw [hcfv₁, hcfv₂]; exact h

end SideElim

/-! ## Trace packaging and fork-transcript invariants -/

/-- Transcript returned by a single simulated-signing EUF-CMA execution inside `contextFork`. -/
structure Trace where
  mStar     : Bytes
  sigStar   : Bytes
  wStar     : Bytes
  targetKey : Bytes
  accepted  : Bool
  queryLog  : List Bytes
  deriving DecidableEq

def Trace.hUsed (tr : Trace) : ZMod l25519 :=
  decodeScalarBytes (fitBytesRef 64 tr.wStar)

/-- Fork-index selector locating `tr.targetKey` in `tr.queryLog` when `tr.accepted = true`. -/
def forkPoint (q_H : ℕ) (tr : Trace) : Option (Fin (q_H + 1)) :=
  if tr.accepted then
    if tr.targetKey ∈ tr.queryLog then
      let idx := tr.queryLog.findIdx (· == tr.targetKey)
      if hidx : idx < q_H + 1 then some ⟨idx, hidx⟩ else none
    else none
  else none

private theorem accepted_of_forkPoint_eq_some {q_H : ℕ} {tr : Trace} {s : Fin (q_H + 1)}
    (hs : forkPoint q_H tr = some s) : tr.accepted = true := by
  simp_all [forkPoint]

private theorem forkPoint_getElem?_eq_some_target {q_H : ℕ} {tr : Trace} {s : Fin (q_H + 1)}
    (hs : forkPoint q_H tr = some s) : tr.queryLog[s.val]? = some tr.targetKey := by
  grind [forkPoint]

abbrev SimState3 : Type := List Bytes × sha512RoSpec.QueryCache × List Bytes

abbrev ProgSignQuery : Type := ZMod l25519 × Bytes × Bytes

abbrev ProgSignSpec : OracleSpec ProgSignQuery := ProgSignQuery →ₒ Bytes

abbrev InnerSpec : OracleSpec ((ℕ ⊕ ProgSignQuery) ⊕ Bytes) :=
  (unifSpec + ProgSignSpec) + sha512RoSpec

def progSignStep (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (q : ProgSignQuery) (st : SimState3) : Bytes × SimState3 :=
  let (sVal, m, hDigest) := q
  let (msgs, cache, qlog) := st
  let edPk := (P.montToEd pk bSim).getD (edDummy P)
  let capA := P.compress edPk
  let minusCapA := P.edNeg edPk
  let h := P.scalarFromWide hDigest
  let s := encodeScalarBytes sVal
  let capR := P.compress (P.doubleScalarMulBasepoint h minusCapA s)
  let signBitByte : UInt8 := (bSim &&& 1) <<< 7
  let sig := capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte]
  let cache' := match cache (capR ++ capA ++ m) with
    | some _ => cache
    | none   => cache.cacheQuery (capR ++ capA ++ m) hDigest
  (sig, (m :: msgs, cache', qlog))

private theorem progSignStep_invariants {P : Primitives} (C : XeddsaCurveWitness P)
    (sk : Bytes) {bSim : UInt8} (hbSim : bSim = 0 ∨ bSim = 1)
    (q : ProgSignQuery) (st : SimState3) :
    let st' := (progSignStep P (P.x25519Base sk) bSim q st).2
    st'.2.2 = st.2.2 ∧
      st.2.1 ≤ st'.2.1 ∧
      (∀ msg ∈ st.1, msg ∈ st'.1) ∧
      (∀ bs w, st'.2.1 bs = some w → st.2.1 bs = some w ∨ bs.drop 64 ∈ st'.1) := by
  rcases q with ⟨sVal, m, hDigest⟩
  rcases st with ⟨msgs, cache, qlog⟩
  dsimp only [progSignStep]
  obtain ⟨edPk, hmont, hrep⟩ := C.montToEd_base sk bSim hbSim
  set capA := P.compress ((P.montToEd (P.x25519Base sk) bSim).getD (edDummy P))
  set minusCapA := P.edNeg ((P.montToEd (P.x25519Base sk) bSim).getD (edDummy P))
  set h := P.scalarFromWide hDigest
  set s := encodeScalarBytes sVal
  set capR := P.compress (P.doubleScalarMulBasepoint h minusCapA s)
  have hedPk_eq : (P.montToEd (P.x25519Base sk) bSim).getD (edDummy P) = edPk := by
    simp [hmont]
  have hcapA_len : capA.length = 32 := by
    dsimp only [capA]
    rw [hedPk_eq, C.compress_of_represents hrep]
    exact C.compressEd_len _
  have hcapR_len : capR.length = 32 := by
    dsimp only [capR, minusCapA, h, s]
    rw [hedPk_eq, C.scalarWide_eq hDigest]
    have hdsmb := C.dsmb_represents (decodeScalarBytes (fitBytesRef 64 hDigest)) sVal
      (C.edNeg_represents hrep)
    rw [C.compress_of_represents hdsmb]
    exact C.compressEd_len _
  have hdrop64 : (capR ++ capA ++ m).drop 64 = m := by
    have h64 : (capR ++ capA).length = 64 := by simp [hcapR_len, hcapA_len]
    rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
      List.nil_append]
  refine ⟨rfl, ?_, fun msg hmem => List.mem_cons_of_mem m hmem, ?_⟩
  · intro bs w hw
    cases hc : cache (capR ++ capA ++ m) with
    | some v => simpa [hc] using hw
    | none =>
        by_cases heq : bs = capR ++ capA ++ m
        · subst heq; rw [hc] at hw; cases hw
        · simpa [QueryCache.cacheQuery_of_ne cache hDigest heq] using hw
  · intro bs w hw
    cases hc : cache (capR ++ capA ++ m) with
    | some v =>
        simp only [hc] at hw
        exact Or.inl hw
    | none =>
        by_cases heq : bs = capR ++ capA ++ m
        · subst heq
          exact Or.inr (by rw [hdrop64]; exact List.mem_cons_self)
        · rw [hc] at hw
          rw [QueryCache.cacheQuery_of_ne cache hDigest heq] at hw
          exact Or.inl hw

noncomputable def liftUnifChal {α : Type} (oa : ProbComp α) : OracleComp ChalZModSpec α :=
  simulateQ (QueryImpl.ofLift unifSpec (OracleComp ChalZModSpec)) oa

noncomputable def liftUnifFork {α : Type} (oa : ProbComp α) : OracleComp ForkSpec α :=
  simulateQ (QueryImpl.ofLift unifSpec (OracleComp ForkSpec)) oa

private theorem elimSide_pure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α : Type} (x : α) :
    elimSide P ddh (pure x) = pure x := rfl

private theorem elimSide_monad_bind (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    {α β : Type} (m : OracleComp ForkSpec α) (f : α → OracleComp ForkSpec β) :
    elimSide P ddh (m >>= f) = (elimSide P ddh m >>= fun a => elimSide P ddh (f a)) := by
  rw [← simulateQ_sideImpl_eq_elimSide, simulateQ_bind]
  simp only [simulateQ_sideImpl_eq_elimSide]

private theorem elimSide_query_unif (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (n : ℕ) :
    elimSide P ddh (liftM (ForkSpec.query (Sum.inl (Sum.inl (Sum.inl n))))) =
      liftM (ChalZModSpec.query (Sum.inl n)) := by
  rw [← simulateQ_sideImpl_eq_elimSide]
  exact simulateQ_spec_query (sideImpl P ddh) _

private theorem elimSide_query_prim (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (p : PrimQuery) :
    elimSide P ddh (liftM (ForkSpec.query (Sum.inl (Sum.inl (Sum.inr p))))) =
      pure (primEval P p) := by
  rw [← simulateQ_sideImpl_eq_elimSide]
  exact simulateQ_spec_query (sideImpl P ddh) _

private theorem elimSide_query_ddh (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (X Y Z : Bytes) :
    elimSide P ddh (liftM (ForkSpec.query (Sum.inl (Sum.inr (X, Y, Z))))) =
      pure (ddh X Y Z) := by
  rw [← simulateQ_sideImpl_eq_elimSide]
  exact simulateQ_spec_query (sideImpl P ddh) _

private theorem elimSide_query_chal (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) :
    elimSide P ddh (liftM (ForkSpec.query (Sum.inr ()))) =
      liftM (ChalZModSpec.query (Sum.inr ())) := by
  rw [← simulateQ_sideImpl_eq_elimSide]
  exact simulateQ_spec_query (sideImpl P ddh) _

private theorem elimSide_liftUnifFork (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) {α : Type} (oa : ProbComp α) :
    elimSide P isValidDhTriple (liftUnifFork oa) = liftUnifChal oa := by
  rw [← simulateQ_sideImpl_eq_elimSide]
  unfold liftUnifFork liftUnifChal
  rw [← QueryImpl.simulateQ_compose]
  congr 1

private theorem simulateQ_liftChalImpl_liftProbToChal {α : Type} (oa : ProbComp α) :
    simulateQ liftChalImpl (liftProbToChal oa) = liftUnifChal oa := by
  unfold liftProbToChal liftUnifChal
  rw [← QueryImpl.simulateQ_compose]
  congr 1

noncomputable def trackedRoImpl3 :
    QueryImpl sha512RoSpec (StateT SimState3 (OracleComp ChalZModSpec)) :=
  fun bs => do
    let (msgs, cache, qlog) ← get
    match cache bs with
    | some w => pure w
    | none =>
        if isH1Input bs then
          let w ← liftM (m := OracleComp ChalZModSpec) (liftUnifChal sampleRandom64)
          set (msgs, cache.cacheQuery bs w, qlog)
          pure w
        else
          let h ← liftM (m := OracleComp ChalZModSpec) (ChalZModSpec.query (Sum.inr ()))
          let w ← liftM (m := OracleComp ChalZModSpec) (liftUnifChal (liftChalTo64 h))
          set (msgs, cache.cacheQuery bs w, qlog ++ [bs])
          pure w

noncomputable def trackedInnerImpl (P : Primitives) (pk : Bytes) (bSim : UInt8) :
    QueryImpl InnerSpec (StateT SimState3 (OracleComp ChalZModSpec)) :=
  (((QueryImpl.ofLift unifSpec (OracleComp ChalZModSpec)).liftTarget
      (StateT SimState3 (OracleComp ChalZModSpec))) +
    (fun q => StateT.mk fun st => pure (progSignStep P pk bSim q st) :
      QueryImpl ProgSignSpec (StateT SimState3 (OracleComp ChalZModSpec)))) +
    trackedRoImpl3

noncomputable def advToInnerImpl (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl XeddsaRomOracleSpec (OracleComp InnerSpec)
  | .inl (.inl (.inl n)) =>
      liftM (InnerSpec.query (Sum.inl (Sum.inl n)))
  | .inl (.inl (.inr p)) =>
      simulateQ (fun bs => liftM (InnerSpec.query (Sum.inr bs))) (primRoStep P p)
  | .inl (.inr bs) =>
      liftM (InnerSpec.query (Sum.inr bs))
  | .inr (.inl (.sign m)) => do
      let sVal ← simulateQ (fun n => liftM (InnerSpec.query (Sum.inl (Sum.inl n))))
        ($ᵗ (ZMod l25519))
      let hDigest ← simulateQ (fun n => liftM (InnerSpec.query (Sum.inl (Sum.inl n))))
        sampleRandom64
      liftM (InnerSpec.query (Sum.inl (Sum.inr (sVal, m, hDigest))))
  | .inr (.inr (X, Y, Z)) =>
      pure (isValidDhTriple X Y Z)

noncomputable def innerFull (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (A : GapSigEufCmaRoAdv) :
    OracleComp InnerSpec (Bytes × Bytes × Option Bytes) := do
  let (mStar, sigStar) ← simulateQ (advToInnerImpl P isValidDhTriple) (A.run pk)
  match xeddsaVerifyChalInput? P pk mStar sigStar with
  | none => pure (mStar, sigStar, none)
  | some chalIn =>
      let wStar ← liftM (InnerSpec.query (Sum.inr chalIn))
      pure (mStar, sigStar, some wStar)

def buildTrace (P : Primitives) (pk : Bytes) :
    (Bytes × Bytes × Option Bytes) × SimState3 → Trace
  | ((mStar, sigStar, none), (_msgs, _cache, qlog)) =>
      { mStar := mStar
        sigStar := sigStar
        wStar := []
        targetKey := []
        accepted := false
        queryLog := qlog }
  | ((mStar, sigStar, some wStar), (msgs, _cache, qlog)) =>
      let chalIn := (xeddsaVerifyChalInput? P pk mStar sigStar).getD []
      let ok := xeddsaVerifyWithDigest P pk mStar sigStar wStar
      { mStar := mStar
        sigStar := sigStar
        wStar := wStar
        targetKey := chalIn
        accepted := (ok && decide (mStar ∉ msgs))
        queryLog := qlog }

/-- Simulated-signing EUF-CMA trace computation over `ChalZModSpec`. -/
noncomputable def wrappedTrace (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    OracleComp ChalZModSpec Trace :=
  buildTrace P pk <$>
    (simulateQ (trackedInnerImpl P pk bSim) (innerFull P isValidDhTriple pk A)).run ([], ∅, [])

noncomputable def rawRoImpl3 :
    QueryImpl sha512RoSpec (StateT SimState3 (OracleComp ForkSpec)) :=
  fun bs => do
    let (msgs, cache, qlog) ← get
    match cache bs with
    | some w => pure w
    | none =>
        if isH1Input bs then
          let w ← liftM (m := OracleComp ForkSpec) (liftUnifFork sampleRandom64)
          set (msgs, cache.cacheQuery bs w, qlog)
          pure w
        else
          let h ← liftM (m := OracleComp ForkSpec) (ForkSpec.query (Sum.inr ()))
          let w ← liftM (m := OracleComp ForkSpec) (liftUnifFork (liftChalTo64 h))
          set (msgs, cache.cacheQuery bs w, qlog ++ [bs])
          pure w

noncomputable def rawPrimImpl3 (P : Primitives) :
    QueryImpl primSpec (StateT SimState3 (OracleComp ForkSpec))
  | .sigSign sk m rand  => simulateQ rawRoImpl3 (xeddsaSignRo P sk m rand)
  | .sigVerify pk m sig => simulateQ rawRoImpl3 (xeddsaVerifyRo P pk m sig)
  | q                   =>
      liftM (m := OracleComp ForkSpec) (ForkSpec.query (Sum.inl (Sum.inl (Sum.inr q))))

noncomputable def rawAdvImpl (P : Primitives) (pk : Bytes) (bSim : UInt8) :
    QueryImpl XeddsaRomOracleSpec (StateT SimState3 (OracleComp ForkSpec))
  | .inl (.inl (.inl n)) =>
      liftM (m := OracleComp ForkSpec) (ForkSpec.query (Sum.inl (Sum.inl (Sum.inl n))))
  | .inl (.inl (.inr p)) =>
      rawPrimImpl3 P p
  | .inl (.inr bs) =>
      rawRoImpl3 bs
  | .inr (.inl (.sign m)) => do
      let sVal ← liftM (m := OracleComp ForkSpec) (liftUnifFork ($ᵗ (ZMod l25519)))
      let hDigest ← liftM (m := OracleComp ForkSpec) (liftUnifFork sampleRandom64)
      StateT.mk fun st => pure (progSignStep P pk bSim (sVal, m, hDigest) st)
  | .inr (.inr (X, Y, Z)) =>
      liftM (m := OracleComp ForkSpec) (ForkSpec.query (Sum.inl (Sum.inr (X, Y, Z))))

noncomputable def rawFull (P : Primitives) (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    StateT SimState3 (OracleComp ForkSpec) (Bytes × Bytes × Option Bytes) := do
  let out ← simulateQ (rawAdvImpl P pk bSim) (A.run pk)
  match xeddsaVerifyChalInput? P pk out.1 out.2 with
  | none => pure (out.1, out.2, none)
  | some chalIn =>
      let wStar ← rawRoImpl3 chalIn
      pure (out.1, out.2, some wStar)

/-- Live simulated-signing EUF-CMA trace computation over `ForkSpec` executed inside `forkGapDhAdv`
    via `OracleComp.contextFork`. -/
noncomputable def rawTrace (P : Primitives) (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    OracleComp ForkSpec Trace :=
  buildTrace P pk <$> (rawFull P pk bSim A).run ([], ∅, [])

private theorem elimSide_rawRoImpl3_run (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (bs : Bytes) (st : SimState3) :
    elimSide P isValidDhTriple ((rawRoImpl3 bs).run st) = (trackedRoImpl3 bs).run st := by
  rcases st with ⟨msgs, cache, qlog⟩
  unfold rawRoImpl3 trackedRoImpl3
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h : cache bs with
  | some w => rfl
  | none =>
      dsimp only
      split_ifs
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, elimSide_monad_bind, elimSide_pure, elimSide_liftUnifFork]
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, elimSide_monad_bind, elimSide_pure, elimSide_query_chal,
          elimSide_liftUnifFork]
        rfl

private theorem elimSide_simulateQ_rawRoImpl3_run (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) {α : Type}
    (oa : OracleComp sha512RoSpec α) (st : SimState3) :
    elimSide P isValidDhTriple ((simulateQ rawRoImpl3 oa).run st) =
      (simulateQ trackedRoImpl3 oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => rfl
  | query_bind bs mx ih =>
      rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
        elimSide_monad_bind, elimSide_rawRoImpl3_run]
      exact bind_congr fun z => ih z.1 z.2

private theorem simulateQ_trackedInnerImpl_liftRo {α : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (oa : OracleComp sha512RoSpec α) (st : SimState3) :
    (simulateQ (trackedInnerImpl P pk bSim)
      (simulateQ (fun bs => liftM (InnerSpec.query (Sum.inr bs))) oa)).run st =
      (simulateQ trackedRoImpl3 oa).run st := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext bs
  rw [QueryImpl.apply_compose, simulateQ_spec_query]
  rfl

private theorem simulateQ_trackedInnerImpl_liftUnif {α : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (oa : ProbComp α) (st : SimState3) :
    (simulateQ (trackedInnerImpl P pk bSim)
      (simulateQ (fun n => liftM (InnerSpec.query (Sum.inl (Sum.inl n)))) oa)).run st =
      (do let u ← liftUnifChal oa; pure (u, st)) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => simp [liftUnifChal, simulateQ_pure]
  | query_bind n mx ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (((trackedInnerImpl P pk bSim) (Sum.inl (Sum.inl n))).run st >>= _) =
        ((liftM (ChalZModSpec.query (Sum.inl n)) >>= fun u =>
          liftUnifChal (mx u)) >>= fun u => pure (u, st))
      simp only [trackedInnerImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, OracleComp.liftM_run_StateT, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u st

theorem elimSide_rawTrace_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    elimSide P isValidDhTriple (rawTrace P pk bSim A) =
      wrappedTrace P isValidDhTriple pk bSim A := by
  have hstep : ∀ t (st : SimState3),
      elimSide P isValidDhTriple (((rawAdvImpl P pk bSim) t).run st) =
        ((simulateQ (trackedInnerImpl P pk bSim) (advToInnerImpl P isValidDhTriple t)).run st) := by
    intro t st
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · simp only [rawAdvImpl, advToInnerImpl, OracleComp.liftM_run_StateT, simulateQ_spec_query,
        trackedInnerImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, elimSide_monad_bind, elimSide_pure]
      rfl
    · cases p <;>
        first
        | (simp only [rawAdvImpl, rawPrimImpl3, advToInnerImpl, primRoStep,
            simulateQ_trackedInnerImpl_liftRo, elimSide_simulateQ_rawRoImpl3_run]; done)
        | (simp only [rawAdvImpl, rawPrimImpl3, advToInnerImpl, primRoStep,
            OracleComp.liftM_run_StateT, simulateQ_pure, StateT.run_pure,
            elimSide_monad_bind, elimSide_pure];
           rfl)
    · simp only [rawAdvImpl, advToInnerImpl, simulateQ_spec_query, trackedInnerImpl,
        QueryImpl.add_apply_inr]
      exact elimSide_rawRoImpl3_run P isValidDhTriple bs st
    · cases qSig with
      | sign m =>
          simp only [rawAdvImpl, advToInnerImpl, StateT.run_bind, OracleComp.liftM_run_StateT,
            StateT.run_mk, simulateQ_bind, simulateQ_trackedInnerImpl_liftUnif, bind_assoc,
            pure_bind, simulateQ_spec_query, elimSide_monad_bind, elimSide_liftUnifFork,
            elimSide_pure]
          simp only [trackedInnerImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
            StateT.run_mk]
    · simp only [rawAdvImpl, advToInnerImpl, OracleComp.liftM_run_StateT, simulateQ_pure,
        StateT.run_pure, elimSide_monad_bind, elimSide_pure]
      rfl
  have hrun : ∀ {α : Type} (oa : OracleComp XeddsaRomOracleSpec α) (st : SimState3),
      elimSide P isValidDhTriple ((simulateQ (rawAdvImpl P pk bSim) oa).run st) =
        (simulateQ (trackedInnerImpl P pk bSim)
          (simulateQ (advToInnerImpl P isValidDhTriple) oa)).run st := by
    intro α oa st
    induction oa using OracleComp.inductionOn generalizing st with
    | pure x => rfl
    | query_bind t mx ih =>
        rw [OracleComp.run_simulateQ_query_bind, simulateQ_query_bind, simulateQ_bind,
          StateT.run_bind, elimSide_monad_bind, hstep t st]
        exact bind_congr fun z => ih z.1 z.2
  unfold rawTrace wrappedTrace rawFull innerFull
  simp only [map_eq_bind_pure_comp, Function.comp_def, elimSide_monad_bind, elimSide_pure,
    simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [hrun (A.run pk) ([], ∅, [])]
  refine bind_congr fun ⟨⟨mStar, sigStar⟩, st₁⟩ => ?_
  dsimp only
  cases hchal : xeddsaVerifyChalInput? P pk mStar sigStar with
  | none => rfl
  | some chalIn =>
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, trackedInnerImpl,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
        elimSide_monad_bind, elimSide_pure, elimSide_rawRoImpl3_run]
      rfl

private theorem proj_trackedRoImpl3_run (bs : Bytes) (st : SimState3) :
    (fun z : Bytes × SimState3 => (z.1, z.2.2.1)) <$> (trackedRoImpl3 bs).run st =
      simulateQ liftChalImpl ((splitRoImpl bs).run st.2.1) := by
  rcases st with ⟨msgs, cache, qlog⟩
  unfold trackedRoImpl3 splitRoImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, QueryImpl.withCaching_apply]
  cases h : cache bs with
  | some w => simp [simulateQ_pure]
  | none =>
      dsimp only [splitRoBaseImpl]
      split_ifs
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, StateT.run_modifyGet,
          OracleComp.liftM_run_StateT, bind_assoc, pure_bind, map_eq_bind_pure_comp,
          Function.comp_apply, simulateQ_bind, simulateQ_pure,
          simulateQ_liftChalImpl_liftProbToChal]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, StateT.run_modifyGet,
          OracleComp.liftM_run_StateT, bind_assoc, pure_bind, map_eq_bind_pure_comp,
          Function.comp_apply, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, liftChalImpl,
          liftUnifChal]

private theorem proj_simulateQ_trackedRoImpl3_run {α : Type}
    (oa : OracleComp sha512RoSpec α) (st : SimState3) :
    (fun z : α × SimState3 => (z.1, z.2.2.1)) <$> (simulateQ trackedRoImpl3 oa).run st =
      simulateQ liftChalImpl ((simulateQ splitRoImpl oa).run st.2.1) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => simp [simulateQ_pure]
  | query_bind bs mx ih =>
      rw [OracleComp.run_simulateQ_query_bind, OracleComp.run_simulateQ_query_bind,
        simulateQ_bind, map_bind]
      have h1 := proj_trackedRoImpl3_run bs st
      rw [← h1, bind_map_left]
      exact bind_congr fun z => ih z.1 z.2

private theorem trackedRoImpl3_msgs_eq {bs : Bytes} {st : SimState3}
    {z : Bytes × SimState3} (hz : z ∈ support ((trackedRoImpl3 bs).run st)) :
    z.2.1 = st.1 := by
  rcases st with ⟨m₀, c₀, l₀⟩
  unfold trackedRoImpl3 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hc : c₀ bs with
  | some w =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
  | none =>
      simp only [hc] at hz
      split_ifs at hz
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, _, rfl⟩ := hz; rfl
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨_, _, _, _, rfl⟩ := hz; rfl

private theorem map_congr_support {α β : Type}
    {oa : OracleComp ChalZModSpec α} {f g : α → β} (h : ∀ a ∈ support oa, f a = g a) :
    f <$> oa = g <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [h x (by simp)]
  | query_bind t mx ih =>
      simp only [map_bind]
      refine bind_congr fun u => ih u fun a ha => h a ?_
      rw [support_bind]
      exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨by simp, ha⟩⟩

private theorem simulateQ_trackedRoImpl3_msgs_eq {α : Type}
    {oa : OracleComp sha512RoSpec α} {st : SimState3}
    {z : α × SimState3} (hz : z ∈ support ((simulateQ trackedRoImpl3 oa).run st)) :
    z.2.1 = st.1 := by
  induction oa using OracleComp.inductionOn generalizing st z with
  | pure _ =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
  | query_bind bs mx ih =>
      rw [OracleComp.run_simulateQ_query_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨z₁, hz₁, hz₂⟩ := hz
      exact (ih z₁.1 hz₂).trans (trackedRoImpl3_msgs_eq hz₁)

theorem map_accepted_wrappedTrace_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) :
    (fun tr => tr.accepted) <$> wrappedTrace P isValidDhTriple pk bSim A =
      simulateQ liftChalImpl (simWithChalDigest P isValidDhTriple pk bSim A) := by
  let proj {α : Type} : α × SimState3 → (α × List Bytes) × sha512RoSpec.QueryCache :=
    fun z => ((z.1, z.2.1), z.2.2.1)
  let sigImplC : QueryImpl sigOracleSpec (StateT (List Bytes) ChalRoComp) :=
    fun (.sign m) => do
      let sig ← liftM (m := ChalRoComp) (xeddsaSimSignChal P pk bSim m)
      modify (m :: ·)
      return sig
  let ddhImplC : QueryImpl gapDhOracleSpec (StateT (List Bytes) ChalRoComp) :=
    fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
  let fullImplC :=
    (primBaseSplitRoImpl P).liftTarget (StateT (List Bytes) ChalRoComp) + (sigImplC + ddhImplC)
  have hbind_pure {α β : Type} (m : OracleComp ChalZModSpec α) (f : α → β) :
      (m >>= fun x => pure (f x)) = f <$> m := by
    simp [map_eq_bind_pure_comp]
  have hstep : ∀ t (st : SimState3),
      proj <$> ((simulateQ (trackedInnerImpl P pk bSim) (advToInnerImpl P isValidDhTriple t)).run st) =
        simulateQ liftChalImpl (((fullImplC t).run st.1).run st.2.1) := by
    intro t ⟨msgs, cache, qlog⟩
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · simp only [advToInnerImpl, simulateQ_spec_query, trackedInnerImpl, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, OracleComp.liftM_run_StateT, fullImplC,
        primBaseSplitRoImpl, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
        simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, Function.comp_apply, proj]
      change (_ >>= _) = (simulateQ liftChalImpl (liftM (ChalDigestSpec.query (Sum.inl n))) >>= _)
      rw [simulateQ_spec_query]
      rfl
    · simp only [advToInnerImpl, simulateQ_trackedInnerImpl_liftRo, fullImplC,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, primBaseSplitRoImpl,
        QueryImpl.add_apply_inr, OracleComp.liftM_run_StateT, StateT.run_bind, StateT.run_pure,
        primSplitRoImpl, simulateQ_bind, simulateQ_pure]
      have hro := proj_simulateQ_trackedRoImpl3_run (primRoStep P p) (msgs, cache, qlog)
      dsimp only at hro
      rw [hbind_pure, ← hro, Functor.map_map]
      exact map_congr_support fun z hz => by
        simp [proj, simulateQ_trackedRoImpl3_msgs_eq hz]
    · simp only [advToInnerImpl, simulateQ_spec_query, trackedInnerImpl, QueryImpl.add_apply_inr,
        fullImplC, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, primBaseSplitRoImpl,
        OracleComp.liftM_run_StateT, StateT.run_bind, StateT.run_pure, simulateQ_bind,
        simulateQ_pure]
      have hro := proj_trackedRoImpl3_run bs (msgs, cache, qlog)
      dsimp only at hro
      rw [hbind_pure, ← hro, Functor.map_map]
      exact map_congr_support fun z hz => by
        simp [proj, trackedRoImpl3_msgs_eq hz]
    · cases qSig with
      | sign m =>
          simp only [advToInnerImpl, fullImplC, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
            sigImplC, xeddsaSimSignChal]
          simp only [simulateQ_bind, StateT.run_bind, simulateQ_trackedInnerImpl_liftUnif,
            bind_assoc, pure_bind, simulateQ_spec_query, OracleComp.liftM_run_StateT,
            StateT.run_modify, StateT.run_pure, simulateQ_pure,
            simulateQ_liftChalImpl_liftProbToChal]
          simp only [trackedInnerImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
            StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
            proj, progSignStep]
    · simp [advToInnerImpl, fullImplC, ddhImplC, simulateQ_pure, proj]
  have hrun : ∀ {α : Type} (oa : OracleComp XeddsaRomOracleSpec α) (st : SimState3),
      proj <$> ((simulateQ (trackedInnerImpl P pk bSim)
          (simulateQ (advToInnerImpl P isValidDhTriple) oa)).run st) =
        simulateQ liftChalImpl (((simulateQ fullImplC oa).run st.1).run st.2.1) := by
    intro α oa st
    induction oa using OracleComp.inductionOn generalizing st with
    | pure x => simp [simulateQ_pure, proj]
    | query_bind t mx ih =>
        rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind,
          OracleComp.run_simulateQ_query_bind, StateT.run_bind, simulateQ_bind, map_bind,
          ← hstep t st, bind_map_left]
        exact bind_congr fun z => ih z.1 z.2
  unfold wrappedTrace innerFull simWithChalDigest
  simp only [Functor.map_map, StateT.run'_eq, simulateQ_map, StateT.run_bind, StateT.run_pure,
    simulateQ_bind, simulateQ_pure]
  have hrun0 := hrun (A.run pk) ([], ∅, [])
  dsimp only at hrun0
  rw [map_bind]
  conv_rhs => rw [map_bind]
  change (_ >>= _) =
    (simulateQ liftChalImpl (((simulateQ fullImplC (A.run pk)).run []).run ∅) >>= _)
  rw [← hrun0, bind_map_left]
  refine bind_congr fun ⟨⟨mStar, sigStar⟩, ⟨msgs, cache, qlog⟩⟩ => ?_
  dsimp only [proj]
  rw [xeddsaVerifyRo_eq]
  cases hchal : xeddsaVerifyChalInput? P pk mStar sigStar with
  | none =>
      simp [buildTrace, simulateQ_pure]
  | some chalIn =>
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, trackedInnerImpl,
        QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      have hro := proj_trackedRoImpl3_run chalIn (msgs, cache, qlog)
      dsimp only at hro
      rw [hbind_pure, hbind_pure, ← hro]
      simp only [Functor.map_map]
      exact map_congr_support fun z hz => by
        simp [buildTrace, hchal, trackedRoImpl3_msgs_eq hz]

private theorem isQueryBoundP_liftUnifChal {α : Type} (oa : ProbComp α) :
    OracleComp.IsQueryBoundP (liftUnifChal oa) (· = Sum.inr ()) 0 := by
  unfold liftUnifChal
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind n mx ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift]
      change OracleComp.IsQueryBoundP
        (liftM (ChalZModSpec.query (Sum.inl n)) >>= fun u =>
          simulateQ (QueryImpl.ofLift unifSpec (OracleComp ChalZModSpec)) (mx u))
        (· = Sum.inr ()) 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

private theorem isQueryBoundP_simulateQ_liftChalImpl {α : Type}
    {oa : OracleComp ChalDigestSpec α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa (· = Sum.inr ()) n) :
    OracleComp.IsQueryBoundP (simulateQ liftChalImpl oa) (· = Sum.inr ()) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rcases t with (k | ⟨⟩)
      · simp only [simulateQ_bind, simulateQ_spec_query, liftChalImpl]
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun u => ih u (by simpa using h.2 u)⟩
      · have hpos : 0 < n := h.1.resolve_left (by simp)
        simp only [simulateQ_bind, simulateQ_spec_query, liftChalImpl, bind_assoc]
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr hpos, fun hchal => ?_⟩
        simp only [↓reduceIte]
        refine (OracleComp.isQueryBoundP_bind (n := 0) (m := n - 1)
          (isQueryBoundP_liftUnifChal (liftChalTo64 hchal)) ?_).mono (by omega)
        intro w _
        exact ih w (by simpa using h.2 w)

theorem wrappedTrace_isQueryBoundP (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    OracleComp.IsQueryBoundP (wrappedTrace P isValidDhTriple pk bSim A)
      (· = Sum.inr ()) (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign + 1) := by
  rw [← OracleComp.isQueryBoundP_map_iff (f := fun tr : Trace => tr.accepted),
    map_accepted_wrappedTrace_eq]
  exact isQueryBoundP_simulateQ_liftChalImpl
    (simWithChalDigest_isQueryBoundP P isValidDhTriple pk bSim hA)

def isForkDdhQuery : ForkSpec.Domain → Bool
  | .inl (.inr _) => true
  | _             => false

def isForkPrimQuery : ForkSpec.Domain → Bool
  | .inl (.inl (.inr _)) => true
  | _                    => false

private theorem isQueryBoundP_liftUnifFork {α : Type} (oa : ProbComp α)
    (pred : ForkSpec.Domain → Prop) [DecidablePred pred]
    (hpred : ∀ n, ¬ pred (Sum.inl (Sum.inl (Sum.inl n)))) :
    OracleComp.IsQueryBoundP (liftUnifFork oa) pred 0 := by
  unfold liftUnifFork
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind n mx ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift]
      change OracleComp.IsQueryBoundP
        (liftM (ForkSpec.query (Sum.inl (Sum.inl (Sum.inl n)))) >>= fun u =>
          simulateQ (QueryImpl.ofLift unifSpec (OracleComp ForkSpec)) (mx u))
        pred 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hpred n), fun u => by simpa using ih u⟩

private theorem isQueryBoundP_rawRoImpl3_zero (bs : Bytes) (st : SimState3)
    (pred : ForkSpec.Domain → Prop) [DecidablePred pred]
    (hunif : ∀ n, ¬ pred (Sum.inl (Sum.inl (Sum.inl n))))
    (hchal : ¬ pred (Sum.inr ())) :
    OracleComp.IsQueryBoundP ((rawRoImpl3 bs).run st) pred 0 := by
  rcases st with ⟨msgs, cache, qlog⟩
  unfold rawRoImpl3
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hc : cache bs with
  | some w => simp
  | none =>
      dsimp only
      split_ifs
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind]
        refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_liftUnifFork sampleRandom64 pred hunif) ?_).mono (by omega)
        intro _ _; simp
      · simp only [StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind]
        change OracleComp.IsQueryBoundP (liftM (ForkSpec.query (Sum.inr ())) >>= _) pred 0
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl hchal, fun h => ?_⟩
        refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_liftUnifFork (liftChalTo64 h) pred hunif) ?_).mono (by omega)
        intro _ _; simp

private theorem isQueryBoundP_simulateQ_rawRoImpl3_zero {α : Type}
    (oa : OracleComp sha512RoSpec α) (st : SimState3)
    (pred : ForkSpec.Domain → Prop) [DecidablePred pred]
    (hunif : ∀ n, ¬ pred (Sum.inl (Sum.inl (Sum.inl n))))
    (hchal : ¬ pred (Sum.inr ())) :
    OracleComp.IsQueryBoundP ((simulateQ rawRoImpl3 oa).run st) pred 0 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure _ => simp [simulateQ_pure]
  | query_bind bs mx ih =>
      rw [OracleComp.run_simulateQ_query_bind]
      refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_rawRoImpl3_zero bs st pred hunif hchal) ?_).mono (by omega)
      intro z _; exact ih z.1 z.2

private theorem isQueryBoundP_run_of_step_fork {α : Type}
    {p : XeddsaRomOracleSpec.Domain → Prop} [DecidablePred p]
    {q : ForkSpec.Domain → Prop} [DecidablePred q]
    {impl : QueryImpl XeddsaRomOracleSpec (StateT SimState3 (OracleComp ForkSpec))}
    {oa : OracleComp XeddsaRomOracleSpec α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep : ∀ t st, OracleComp.IsQueryBoundP ((impl t).run st) q (if p t then 1 else 0)) :
    ∀ st, OracleComp.IsQueryBoundP ((simulateQ impl oa).run st) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => intro st; simp [simulateQ_pure]
  | query_bind t mx ih =>
      intro st
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [OracleComp.run_simulateQ_query_bind]
      have hb := OracleComp.isQueryBoundP_bind (hstep t st) fun z _ => ih z.1 (h.2 z.1) z.2
      refine hb.mono ?_
      by_cases hpt : p t
      · have hpos : 0 < n := h.1.resolve_left (not_not.mpr hpt)
        simp only [hpt, ↓reduceIte]; omega
      · simp [hpt]

theorem rawTrace_isQueryBoundP_ddh (P : Primitives) (pk : Bytes) (bSim : UInt8)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    OracleComp.IsQueryBoundP (rawTrace P pk bSim A)
      (fun q => isForkDdhQuery q = true) A.q_ddh := by
  let pDdh : ForkSpec.Domain → Prop := fun q => isForkDdhQuery q = true
  unfold rawTrace rawFull
  rw [OracleComp.isQueryBoundP_map_iff, StateT.run_bind]
  refine (OracleComp.isQueryBoundP_bind (p := pDdh) (n := A.q_ddh) (m := 0) ?_ ?_).mono (by omega)
  · refine isQueryBoundP_run_of_step_fork (q := pDdh) (hA.2.1 pk) ?_ ([], ∅, [])
    intro t st
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · simp only [isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl,
        OracleComp.liftM_run_StateT]
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [pDdh, isForkDdhQuery]), fun _ => trivial⟩
    · simp only [isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl]
      cases p <;>
        simp only [rawPrimImpl3, OracleComp.liftM_run_StateT] <;>
        first
        | exact isQueryBoundP_simulateQ_rawRoImpl3_zero _ st pDdh
            (by simp [pDdh, isForkDdhQuery]) (by simp [pDdh, isForkDdhQuery])
        | (rw [OracleComp.isQueryBoundP_query_bind_iff];
           exact ⟨Or.inl (by simp [pDdh, isForkDdhQuery]), fun _ => trivial⟩)
    · simp only [isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl]
      exact isQueryBoundP_rawRoImpl3_zero bs st pDdh (by simp [pDdh, isForkDdhQuery])
        (by simp [pDdh, isForkDdhQuery])
    · cases qSig with
      | sign m =>
          simp only [isRomDdhChalQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl,
            StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_mk, bind_assoc, pure_bind]
          refine (OracleComp.isQueryBoundP_bind (p := pDdh) (n := 0) (m := 0)
            (isQueryBoundP_liftUnifFork ($ᵗ (ZMod l25519)) pDdh (by simp [pDdh, isForkDdhQuery]))
            ?_).mono (by omega)
          intro _ _
          refine (OracleComp.isQueryBoundP_bind (p := pDdh) (n := 0) (m := 0)
            (isQueryBoundP_liftUnifFork sampleRandom64 pDdh (by simp [pDdh, isForkDdhQuery]))
            ?_).mono (by omega)
          intro _ _; simp
    · simp only [isRomDdhChalQuery, ↓reduceIte, rawAdvImpl, OracleComp.liftM_run_StateT]
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr (by omega), fun _ => trivial⟩
  · rintro ⟨⟨mStar, sigStar⟩, st₁⟩ _
    dsimp only
    cases xeddsaVerifyChalInput? P pk mStar sigStar with
    | none => simp
    | some chalIn =>
        rw [StateT.run_bind]
        refine (OracleComp.isQueryBoundP_bind (p := pDdh) (n := 0) (m := 0)
          (isQueryBoundP_rawRoImpl3_zero chalIn st₁ pDdh (by simp [pDdh, isForkDdhQuery])
            (by simp [pDdh, isForkDdhQuery])) ?_).mono (by omega)
        intro _ _; simp

theorem rawTrace_isQueryBoundP_prim (P : Primitives) (pk : Bytes) (bSim : UInt8)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    OracleComp.IsQueryBoundP (rawTrace P pk bSim A)
      (fun q => isForkPrimQuery q = true) A.q_prim := by
  let pPrim : ForkSpec.Domain → Prop := fun q => isForkPrimQuery q = true
  unfold rawTrace rawFull
  rw [OracleComp.isQueryBoundP_map_iff, StateT.run_bind]
  refine (OracleComp.isQueryBoundP_bind (p := pPrim) (n := A.q_prim) (m := 0) ?_ ?_).mono (by omega)
  · refine isQueryBoundP_run_of_step_fork (q := pPrim) (hA.2.2.1 pk) ?_ ([], ∅, [])
    intro t st
    rcases t with (((n | p) | bs) | (qSig | ⟨X, Y, Z⟩))
    · simp only [isRomPrimQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl,
        OracleComp.liftM_run_StateT]
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [pPrim, isForkPrimQuery]), fun _ => trivial⟩
    · simp only [isRomPrimQuery, ↓reduceIte, rawAdvImpl]
      cases p <;>
        simp only [rawPrimImpl3, OracleComp.liftM_run_StateT] <;>
        first
        | exact (isQueryBoundP_simulateQ_rawRoImpl3_zero _ st pPrim
            (by simp [pPrim, isForkPrimQuery]) (by simp [pPrim, isForkPrimQuery])).mono (by omega)
        | (rw [OracleComp.isQueryBoundP_query_bind_iff];
           exact ⟨Or.inr (by omega), fun _ => trivial⟩)
    · simp only [isRomPrimQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl]
      exact isQueryBoundP_rawRoImpl3_zero bs st pPrim (by simp [pPrim, isForkPrimQuery])
        (by simp [pPrim, isForkPrimQuery])
    · cases qSig with
      | sign m =>
          simp only [isRomPrimQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl,
            StateT.run_bind, OracleComp.liftM_run_StateT, StateT.run_mk, bind_assoc, pure_bind]
          refine (OracleComp.isQueryBoundP_bind (p := pPrim) (n := 0) (m := 0)
            (isQueryBoundP_liftUnifFork ($ᵗ (ZMod l25519)) pPrim (by simp [pPrim, isForkPrimQuery]))
            ?_).mono (by omega)
          intro _ _
          refine (OracleComp.isQueryBoundP_bind (p := pPrim) (n := 0) (m := 0)
            (isQueryBoundP_liftUnifFork sampleRandom64 pPrim (by simp [pPrim, isForkPrimQuery]))
            ?_).mono (by omega)
          intro _ _; simp
    · simp only [isRomPrimQuery, Bool.false_eq_true, ↓reduceIte, rawAdvImpl,
        OracleComp.liftM_run_StateT]
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [pPrim, isForkPrimQuery]), fun _ => trivial⟩
  · rintro ⟨⟨mStar, sigStar⟩, st₁⟩ _
    dsimp only
    cases xeddsaVerifyChalInput? P pk mStar sigStar with
    | none => simp
    | some chalIn =>
        rw [StateT.run_bind]
        refine (OracleComp.isQueryBoundP_bind (p := pPrim) (n := 0) (m := 0)
          (isQueryBoundP_rawRoImpl3_zero chalIn st₁ pPrim (by simp [pPrim, isForkPrimQuery])
            (by simp [pPrim, isForkPrimQuery])) ?_).mono (by omega)
        intro _ _; simp

/-! ## Logging-oracle coupling invariants and contextual-fork soundness -/

section Coupling

private theorem log_countQ_le_of_isQueryBoundP {α : Type}
    {oa : OracleComp ChalZModSpec α} {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa (· = Sum.inr ()) n)
    {x : α} {log : QueryLog ChalZModSpec}
    (hx : (x, log) ∈ support (simulateQ ChalZModSpec.loggingOracle oa).run) :
    log.countQ (· = Sum.inr ()) ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n x log with
  | pure a =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl⟩
      simp [QueryLog.countQ]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hx
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at hx
      obtain ⟨u, _, ⟨x', log'⟩, hlog', hpair⟩ := hx
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      rcases t with (k | u_unit)
      · have hih := ih u (by simpa using h.2 u) hlog'
        simpa [QueryLog.countQ, QueryLog.getQ_cons] using hih
      · cases u_unit
        have hpos : 0 < n := h.1.resolve_left (by simp)
        have hih := ih u (by simpa using h.2 u) hlog'
        have hcons :
            QueryLog.countQ (spec := ChalZModSpec) (⟨Sum.inr (), u⟩ :: log') (· = Sum.inr ()) =
              log'.countQ (· = Sum.inr ()) + 1 := by
          simp [QueryLog.countQ, QueryLog.getQ_cons]
        rw [hcons]
        omega

private theorem exists_log_of_mem_support {α : Type} {oa : OracleComp ChalZModSpec α}
    {x : α} (hx : x ∈ support oa) :
    ∃ log, (x, log) ∈ support (simulateQ ChalZModSpec.loggingOracle oa).run := by
  induction oa using OracleComp.inductionOn generalizing x with
  | pure a =>
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨[], by simp⟩
  | query_bind t mx ih =>
      rw [support_bind] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨u, _, hxu⟩ := hx
      obtain ⟨log', hlog'⟩ := ih u hxu
      refine ⟨⟨t, u⟩ :: log', ?_⟩
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind]
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image]
      exact ⟨u, by simp, (x, log'), hlog', rfl⟩

private theorem countQ_eq_zero_of_forall_ne {l : QueryLog ChalZModSpec}
    (hl : ∀ e ∈ l, e.1 ≠ Sum.inr ()) :
    l.countQ (· = Sum.inr ()) = 0 := by
  induction l with
  | nil => simp [QueryLog.countQ]
  | cons hd tl ih =>
      have hne : hd.1 ≠ Sum.inr () := hl hd List.mem_cons_self
      have htl : ∀ e ∈ tl, e.1 ≠ Sum.inr () := fun e he => hl e (List.mem_cons_of_mem hd he)
      simpa [QueryLog.countQ, QueryLog.getQ_cons, hne] using ih htl

private theorem getQueryValue?_append_of_eq_some
    {w sfx : QueryLog ChalZModSpec} {i : ℕ} {v : ZMod l25519}
    (h : QueryLog.getQueryValue? w (Sum.inr ()) i = some v) :
    QueryLog.getQueryValue? (w ++ sfx) (Sum.inr ()) i = some v := by
  induction w generalizing i with
  | nil => simp [QueryLog.getQueryValue?] at h
  | cons entry w' ih =>
      rcases entry with ⟨t, u⟩
      rcases t with (k | ⟨⟩)
      · rw [QueryLog.getQueryValue?_cons_of_ne _ _ _ _ (by simp)] at h
        rw [List.cons_append, QueryLog.getQueryValue?_cons_of_ne _ _ _ _ (by simp)]
        exact ih h
      · cases i with
        | zero =>
            rw [QueryLog.getQueryValue?_cons_self_zero] at h
            rw [List.cons_append, QueryLog.getQueryValue?_cons_self_zero]
            exact h
        | succ i' =>
            rw [QueryLog.getQueryValue?_cons_self_succ] at h
            rw [List.cons_append, QueryLog.getQueryValue?_cons_self_succ]
            exact ih h

private theorem liftUnifChal_pure {α : Type} (a : α) :
    liftUnifChal (pure a) = pure a := by
  simp [liftUnifChal]

private theorem liftUnifChal_query_bind {α : Type} (k : ℕ) (mx : Fin (k + 1) → ProbComp α) :
    liftUnifChal (liftM (unifSpec.query k) >>= mx) =
      (liftM (ChalZModSpec.query (Sum.inl k)) >>= fun u => liftUnifChal (mx u)) := by
  unfold liftUnifChal
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift]
  rfl

private theorem liftUnifChal_log_spec {α : Type} {oa : ProbComp α}
    {x : α} {l : QueryLog ChalZModSpec}
    (h : (x, l) ∈ support (simulateQ ChalZModSpec.loggingOracle (liftUnifChal oa)).run) :
    x ∈ support oa ∧ ∀ e ∈ l, e.1 ≠ Sum.inr () := by
  induction oa using OracleComp.inductionOn generalizing x l with
  | pure a =>
      simp only [liftUnifChal_pure, simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by simp, fun _ hm => by cases hm⟩
  | query_bind k mx ih =>
      rw [liftUnifChal_query_bind, OracleComp.run_simulateQ_loggingOracle_query_bind] at h
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at h
      obtain ⟨u, _, ⟨x', l'⟩, hl', hpair⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨hx', hne'⟩ := ih u hl'
      refine ⟨?_, ?_⟩
      · rw [support_bind]
        exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨by simp, hx'⟩⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | htl
        · simp
        · exact hne' e htl

private theorem liftUnifChal_log_prefix_det {α : Type} {oa : ProbComp α}
    {x₁ x₂ : α} {l₁ l₂ s₁ s₂ : QueryLog ChalZModSpec}
    (h₁ : (x₁, l₁) ∈ support (simulateQ ChalZModSpec.loggingOracle (liftUnifChal oa)).run)
    (h₂ : (x₂, l₂) ∈ support (simulateQ ChalZModSpec.loggingOracle (liftUnifChal oa)).run)
    (heq : l₁ ++ s₁ = l₂ ++ s₂) :
    x₁ = x₂ ∧ l₁ = l₂ ∧ s₁ = s₂ := by
  induction oa using OracleComp.inductionOn generalizing x₁ x₂ l₁ l₂ s₁ s₂ with
  | pure a =>
      simp only [liftUnifChal_pure, simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
      rcases h₁ with ⟨rfl, rfl⟩
      rcases h₂ with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, by simpa using heq⟩
  | query_bind k mx ih =>
      rw [liftUnifChal_query_bind, OracleComp.run_simulateQ_loggingOracle_query_bind] at h₁ h₂
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨u₁, _, ⟨x₁', l₁'⟩, hl₁', hp₁⟩ := h₁
      obtain ⟨u₂, _, ⟨x₂', l₂'⟩, hl₂', hp₂⟩ := h₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp₂
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨hhead, htail⟩ := heq
      have hu : u₁ = u₂ := eq_of_heq (Sigma.mk.inj hhead).2
      subst hu
      obtain ⟨rfl, rfl, rfl⟩ := ih u₁ hl₁' hl₂' htail
      exact ⟨rfl, rfl, rfl⟩

private theorem all_inl_append_eq_append_inr
    {uLog tail p rest : QueryLog ChalZModSpec} {v : ZMod l25519}
    (hl : ∀ e ∈ uLog, e.1 ≠ Sum.inr ())
    (heq : uLog ++ tail = p ++ (⟨Sum.inr (), v⟩ :: rest)) :
    ∃ p', p = uLog ++ p' ∧ tail = p' ++ (⟨Sum.inr (), v⟩ :: rest) := by
  induction uLog generalizing p with
  | nil => exact ⟨p, rfl, by simpa using heq⟩
  | cons hd tl ih =>
      cases p with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
          exact absurd (congrArg Sigma.fst heq.1) (hl hd List.mem_cons_self)
      | cons ph pt =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, htail⟩ := heq
          obtain ⟨p', rfl, htail'⟩ :=
            ih (fun e he => hl e (List.mem_cons_of_mem hd he)) htail
          exact ⟨p', rfl, htail'⟩

private theorem support_step_unif (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (n : ℕ) (st : SimState3)
    {z : (Fin (n + 1) × SimState3) × QueryLog ChalZModSpec}
    (hz : z ∈ support (simulateQ ChalZModSpec.loggingOracle
      (((trackedInnerImpl P pk bSim) (Sum.inl (Sum.inl n))).run st)).run) :
    ∃ u : Fin (n + 1), z = ((u, st), [⟨Sum.inl n, u⟩]) := by
  have hrun : ((trackedInnerImpl P pk bSim) (Sum.inl (Sum.inl n))).run st =
      (liftM (ChalZModSpec.query (Sum.inl n)) >>= fun u => pure (u, st)) := by
    simp only [trackedInnerImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, OracleComp.liftM_run_StateT]
    rfl
  rw [hrun, OracleComp.run_simulateQ_loggingOracle_query_bind] at hz
  simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image,
    simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨u, _, _, rfl, rfl⟩ := hz
  exact ⟨u, rfl⟩

private theorem support_step_progSign (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (q : ProgSignQuery) (st : SimState3)
    {z : (Bytes × SimState3) × QueryLog ChalZModSpec}
    (hz : z ∈ support (simulateQ ChalZModSpec.loggingOracle
      (((trackedInnerImpl P pk bSim) (Sum.inl (Sum.inr q))).run st)).run) :
    z = (progSignStep P pk bSim q st, []) := by
  have hrun : ((trackedInnerImpl P pk bSim) (Sum.inl (Sum.inr q))).run st =
      pure (progSignStep P pk bSim q st) := by
    simp [trackedInnerImpl]
  rw [hrun] at hz
  simpa [simulateQ_pure, WriterT.run_pure'] using hz

private theorem support_step_ro (bs : Bytes) (st : SimState3)
    {z : (Bytes × SimState3) × QueryLog ChalZModSpec}
    (hz : z ∈ support (simulateQ ChalZModSpec.loggingOracle ((trackedRoImpl3 bs).run st)).run) :
    (∃ w, st.2.1 bs = some w ∧ z = ((w, st), [])) ∨
    (st.2.1 bs = none ∧ isH1Input bs = true ∧
      ∃ w uLog,
        (w, uLog) ∈ support (simulateQ ChalZModSpec.loggingOracle
          (liftUnifChal sampleRandom64)).run ∧
        z = ((w, (st.1, st.2.1.cacheQuery bs w, st.2.2)), uLog)) ∨
    (st.2.1 bs = none ∧ isH1Input bs = false ∧
      ∃ h w uLog,
        (w, uLog) ∈ support (simulateQ ChalZModSpec.loggingOracle
          (liftUnifChal (liftChalTo64 h))).run ∧
        z = ((w, (st.1, st.2.1.cacheQuery bs w, st.2.2 ++ [bs])), ⟨Sum.inr (), h⟩ :: uLog)) := by
  rcases st with ⟨msgs, cache, qlog⟩
  have hempty : (∅ : QueryLog ChalZModSpec) = [] := rfl
  unfold trackedRoImpl3 at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hc : cache bs with
  | some w =>
      simp only [hc, StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hz
      exact Or.inl ⟨w, rfl, hz⟩
  | none =>
      simp only [hc] at hz
      by_cases hh1 : isH1Input bs = true
      · simp only [hh1, ↓reduceIte, StateT.run_bind, OracleComp.liftM_run_StateT,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind,
          WriterT.run_bind', support_bind, Set.mem_iUnion, support_map, Set.mem_image,
          simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨⟨w, uLog⟩, hw, _, rfl, hzeq⟩ := hz
        dsimp only [Prod.map, id] at hzeq
        simp only [hempty, List.append_nil] at hzeq
        exact Or.inr (Or.inl ⟨rfl, hh1, w, uLog, hw, hzeq.symm⟩)
      · have hh1_f : isH1Input bs = false := Bool.eq_false_iff.mpr hh1
        simp only [hh1_f, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          OracleComp.liftM_run_StateT, StateT.run_set, StateT.run_pure, bind_assoc,
          pure_bind] at hz
        change z ∈ support (simulateQ ChalZModSpec.loggingOracle
          (liftM (ChalZModSpec.query (Sum.inr ())) >>= fun h =>
            liftUnifChal (liftChalTo64 h) >>= fun w =>
              pure (w, (msgs, cache.cacheQuery bs w, qlog ++ [bs])))).run at hz
        rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hz
        simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image,
          simulateQ_bind, WriterT.run_bind', simulateQ_pure, WriterT.run_pure',
          support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨h, _, pw, ⟨⟨w, uLog⟩, hw, _, rfl, hpw⟩, hzeq⟩ := hz
        dsimp only [Prod.map, id] at hpw hzeq
        simp only [hempty, List.append_nil] at hpw
        subst hpw
        exact Or.inr (Or.inr ⟨rfl, hh1_f, h, w, uLog, hw, hzeq.symm⟩)

private theorem preservesInv_inner {γ : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (Inv : SimState3 → QueryLog ChalZModSpec → Prop)
    (hstep : ∀ t (s : SimState3) (w : QueryLog ChalZModSpec),
      Inv s w →
      ∀ z ∈ support (simulateQ ChalZModSpec.loggingOracle
        (((trackedInnerImpl P pk bSim) t).run s)).run,
      Inv z.1.2 (w ++ z.2))
    (Y : OracleComp InnerSpec γ) (s₀ : SimState3) (w₀ : QueryLog ChalZModSpec)
    (hinit : Inv s₀ w₀)
    {z : (γ × SimState3) × QueryLog ChalZModSpec}
    (hz : z ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P pk bSim) Y).run s₀)).run) :
    Inv z.1.2 (w₀ ++ z.2) := by
  induction Y using OracleComp.inductionOn generalizing s₀ w₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinit
  | query_bind t oa ih =>
      rw [OracleComp.run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, rfl⟩ := hz
      simp only [Prod.map_fst, Prod.map_snd, id_eq, ← List.append_assoc]
      exact ih us_w.1.1 (s₀ := us_w.1.2) (w₀ := w₀ ++ us_w.2)
        (hstep t s₀ w₀ hinit us_w hus_w) hpw

private theorem inner_queryLog_length_eq {γ : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (Y : OracleComp InnerSpec γ) (s₀ : SimState3)
    {z : γ × SimState3} {outerLog : QueryLog ChalZModSpec}
    (hz : (z, outerLog) ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P pk bSim) Y).run s₀)).run) :
    z.2.2.2.length = s₀.2.2.length + outerLog.countQ (· = Sum.inr ()) := by
  have h := preservesInv_inner P pk bSim
    (Inv := fun s w => s.2.2.length = s₀.2.2.length + w.countQ (· = Sum.inr ()))
    (hstep := ?_) Y s₀ [] (by simp [QueryLog.countQ]) hz
  · simpa [List.nil_append] using h
  · intro t s w hI z' hz'
    rcases t with ((n | q) | bs)
    · obtain ⟨u, rfl⟩ := support_step_unif P pk bSim n s hz'
      simpa [QueryLog.countQ_append, QueryLog.countQ, QueryLog.getQ_cons] using hI
    · obtain rfl := support_step_progSign P pk bSim q s hz'
      have hlen_eq : (progSignStep P pk bSim q s).2.2.2 = s.2.2 := rfl
      simpa [hlen_eq] using hI
    · simp only [trackedInnerImpl, QueryImpl.add_apply_inr] at hz'
      rcases support_step_ro bs s hz' with
        ⟨_, _, rfl⟩ | ⟨_, _, w_new, uLog, huLog, rfl⟩ | ⟨_, _, h_new, w_new, uLog, huLog, rfl⟩
      · simpa using hI
      · have hzero := countQ_eq_zero_of_forall_ne (liftUnifChal_log_spec huLog).2
        simpa [QueryLog.countQ_append, hzero] using hI
      · have hzero := countQ_eq_zero_of_forall_ne (liftUnifChal_log_spec huLog).2
        have h1 : QueryLog.countQ (spec := ChalZModSpec) (⟨Sum.inr (), h_new⟩ :: uLog)
            (· = Sum.inr ()) = 1 := by
          simp [QueryLog.countQ, QueryLog.getQ_cons] at hzero ⊢
          exact hzero
        simp only [List.length_append, List.length_singleton, QueryLog.countQ_append, h1, hI]
        omega

private theorem inner_queryLog_extends {γ : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (Y : OracleComp InnerSpec γ) (s₀ : SimState3)
    {z : γ × SimState3} {outerLog : QueryLog ChalZModSpec}
    (hz : (z, outerLog) ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P pk bSim) Y).run s₀)).run) :
    z.2.2.2.take s₀.2.2.length = s₀.2.2 := by
  have h := preservesInv_inner P pk bSim
    (Inv := fun s _ => ∃ sfx, s.2.2 = s₀.2.2 ++ sfx)
    (hstep := ?_) Y s₀ [] ⟨[], by simp⟩ hz
  · obtain ⟨sfx, hsfx⟩ := h
    rw [hsfx]
    exact List.take_left
  · intro t s _ ⟨sfx, hsfx⟩ z' hz'
    rcases t with ((n | q) | bs)
    · obtain ⟨_, rfl⟩ := support_step_unif P pk bSim n s hz'
      exact ⟨sfx, hsfx⟩
    · obtain rfl := support_step_progSign P pk bSim q s hz'
      exact ⟨sfx, hsfx⟩
    · simp only [trackedInnerImpl, QueryImpl.add_apply_inr] at hz'
      rcases support_step_ro bs s hz' with
        ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩
      · exact ⟨sfx, hsfx⟩
      · exact ⟨sfx, hsfx⟩
      · exact ⟨sfx ++ [bs], by rw [hsfx, List.append_assoc]⟩

private theorem wrappedTrace_queryLog_length_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv)
    {tr : Trace} {outerLog : QueryLog ChalZModSpec}
    (htr : (tr, outerLog) ∈ support
      (OracleComp.replayFirstRun (wrappedTrace P isValidDhTriple pk bSim A))) :
    tr.queryLog.length = outerLog.countQ (· = Sum.inr ()) := by
  unfold OracleComp.replayFirstRun OracleComp.withQueryLog wrappedTrace at htr
  simp only [simulateQ_map, WriterT.run_map', support_map, Set.mem_image] at htr
  obtain ⟨⟨⟨out, st⟩, log⟩, hmem, heq⟩ := htr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hlen : (buildTrace P pk (out, st)).queryLog = st.2.2 := by
    rcases out with ⟨mStar, sigStar, _ | wStar⟩ <;> rfl
  rw [hlen]
  simpa using inner_queryLog_length_eq P pk bSim
    (innerFull P isValidDhTriple pk A) ([], ∅, []) hmem

theorem wrappedTrace_forkPoint_cfReachable (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) (q_H : ℕ) :
    OracleComp.CfReachable (wrappedTrace P isValidDhTriple pk bSim A)
      (forkQbChal q_H) (Sum.inr ()) (forkPoint q_H) := by
  intro tr log htr s hs
  have hslt : (s : ℕ) < log.countQ (· = Sum.inr ()) :=
    wrappedTrace_queryLog_length_eq P isValidDhTriple pk bSim A htr ▸
      (List.getElem?_eq_some_iff.mp (forkPoint_getElem?_eq_some_target hs)).1
  exact QueryLog.getQueryValue?_isSome_of_lt log (Sum.inr ()) (s : ℕ) hslt

private theorem inner_honest_invariant {γ : Type} {P : Primitives}
    (C : XeddsaCurveWitness P) (sk : Bytes) {bSim : UInt8}
    (hbSim : bSim = 0 ∨ bSim = 1)
    (Y : OracleComp InnerSpec γ)
    {z : γ × SimState3} {outerLog : QueryLog ChalZModSpec}
    (hz : (z, outerLog) ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P (P.x25519Base sk) bSim) Y).run ([], ∅, []))).run) :
    let st := z.2
    st.2.2.length = outerLog.countQ (· = Sum.inr ()) ∧
    (∀ i (hi : i < st.2.2.length),
      ∃ d h,
        st.2.1 (st.2.2[i]'hi) = some d ∧
        decodeScalarBytes (fitBytesRef 64 d) = h ∧
        QueryLog.getQueryValue? outerLog (Sum.inr ()) i = some h) ∧
    (∀ bs d, st.2.1 bs = some d → bs ∈ st.2.2 ∨ isH1Input bs = true ∨ bs.drop 64 ∈ st.1) := by
  let pk := P.x25519Base sk
  let Inv : SimState3 → QueryLog ChalZModSpec → Prop := fun st w =>
    st.2.2.length = w.countQ (· = Sum.inr ()) ∧
    (∀ i (hi : i < st.2.2.length),
      ∃ d h,
        st.2.1 (st.2.2[i]'hi) = some d ∧
        decodeScalarBytes (fitBytesRef 64 d) = h ∧
        QueryLog.getQueryValue? w (Sum.inr ()) i = some h) ∧
    (∀ bs d, st.2.1 bs = some d → bs ∈ st.2.2 ∨ isH1Input bs = true ∨ bs.drop 64 ∈ st.1)
  have h := preservesInv_inner P pk bSim Inv ?_ Y ([], ∅, []) []
    ⟨by simp [QueryLog.countQ], fun i hi => by simp at hi, fun bs d hd => by simp at hd⟩ hz
  · simpa [Inv, List.nil_append] using h
  · intro t s w ⟨hlen, hlock, hprov⟩ z' hz'
    rcases t with ((n | q) | bs)
    · obtain ⟨u, rfl⟩ := support_step_unif P pk bSim n s hz'
      refine ⟨?_, ?_, hprov⟩
      · simpa [QueryLog.countQ_append, QueryLog.countQ, QueryLog.getQ_cons] using hlen
      · intro i hi
        obtain ⟨d, h, hc, hdec, hqv⟩ := hlock i hi
        exact ⟨d, h, hc, hdec, getQueryValue?_append_of_eq_some hqv⟩
    · obtain rfl := support_step_progSign P pk bSim q s hz'
      obtain ⟨hqlog_eq, hcache_le, hmsgs_sub, hnew⟩ := progSignStep_invariants C sk hbSim q s
      set s' := (progSignStep P pk bSim q s).2
      simp only [List.append_nil]
      refine ⟨(congrArg List.length hqlog_eq).trans hlen, ?_, ?_⟩
      · intro i hi
        have hi_s : i < s.2.2.length := hqlog_eq ▸ hi
        obtain ⟨d, h, hc, hdec, hqv⟩ := hlock i hi_s
        refine ⟨d, h, ?_, hdec, hqv⟩
        have hidx : s'.2.2[i]'hi = s.2.2[i]'hi_s := List.getElem_of_eq hqlog_eq _
        rw [hidx]
        exact hcache_le hc
      · intro bs d hd
        rcases hnew bs d hd with hd_old | hdrop
        · rcases hprov bs d hd_old with hmem | hh1 | hm_old
          · exact Or.inl (hqlog_eq.symm ▸ hmem)
          · exact Or.inr (Or.inl hh1)
          · exact Or.inr (Or.inr (hmsgs_sub _ hm_old))
        · exact Or.inr (Or.inr hdrop)
    · simp only [trackedInnerImpl, QueryImpl.add_apply_inr] at hz'
      rcases support_step_ro bs s hz' with
        ⟨_, _, rfl⟩ | ⟨hnone, hh1, w_new, uLog, huLog, rfl⟩ |
          ⟨hnone, hh1_f, h_new, w_new, uLog, huLog, rfl⟩
      · simpa [Inv] using And.intro hlen (And.intro hlock hprov)
      · have hzero := countQ_eq_zero_of_forall_ne (liftUnifChal_log_spec huLog).2
        refine ⟨by simpa [QueryLog.countQ_append, hzero] using hlen, ?_, ?_⟩
        · intro i hi
          obtain ⟨d, h, hc, hdec, hqv⟩ := hlock i hi
          have hne : s.2.2[i]'hi ≠ bs := by
            intro heq; rw [heq, hnone] at hc; cases hc
          exact ⟨d, h, by rwa [QueryCache.cacheQuery_of_ne _ _ hne], hdec,
            getQueryValue?_append_of_eq_some hqv⟩
        · intro bs' d hd
          by_cases heq : bs' = bs
          · subst heq; exact Or.inr (Or.inl hh1)
          · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hd
            exact hprov bs' d hd
      · obtain ⟨hw_mem, huLog_ne⟩ := liftUnifChal_log_spec huLog
        have hzero := countQ_eq_zero_of_forall_ne huLog_ne
        have hdec_new : decodeScalarBytes (fitBytesRef 64 w_new) = h_new :=
          decodeScalarBytes_fit64_liftChalTo64 hw_mem
        have h1 : QueryLog.countQ (spec := ChalZModSpec) (⟨Sum.inr (), h_new⟩ :: uLog)
            (· = Sum.inr ()) = 1 := by
          simp [QueryLog.countQ, QueryLog.getQ_cons] at hzero ⊢
          exact hzero
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_singleton, QueryLog.countQ_append, h1, hlen]
        · intro i hi
          have hi' : i < s.2.2.length + 1 := by
            simpa [List.length_append] using hi
          by_cases hlt : i < s.2.2.length
          · obtain ⟨d, h, hc, hdec, hqv⟩ := hlock i hlt
            have hidx : (s.2.2 ++ [bs])[i]'hi = s.2.2[i]'hlt :=
              List.getElem_append_left hlt
            have hne : s.2.2[i]'hlt ≠ bs := by
              intro heq; rw [heq, hnone] at hc; cases hc
            refine ⟨d, h, ?_, hdec, getQueryValue?_append_of_eq_some hqv⟩
            rw [hidx, QueryCache.cacheQuery_of_ne _ _ hne]
            exact hc
          · have hi_eq : i = s.2.2.length := by omega
            subst hi_eq
            have hidx : (s.2.2 ++ [bs])[s.2.2.length]'hi = bs := by
              rw [List.getElem_append_right (Nat.le_refl _)]
              simp
            refine ⟨w_new, h_new, ?_, hdec_new, ?_⟩
            · rw [hidx]
              exact QueryCache.cacheQuery_self s.2.1 bs w_new
            · rw [hlen]
              exact QueryLog.getQueryValue?_append_self_at_countQ w uLog (Sum.inr ()) h_new
        · intro bs' d hd
          by_cases heq : bs' = bs
          · subst heq
            exact Or.inl (List.mem_append_right _ (List.mem_singleton_self bs'))
          · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hd
            rcases hprov bs' d hd with hmem | hh1' | hm
            · exact Or.inl (List.mem_append_left _ hmem)
            · exact Or.inr (Or.inl hh1')
            · exact Or.inr (Or.inr hm)

private theorem trackedRoImpl3_cache_eq_some {bs : Bytes} {st : SimState3}
    {z : (Bytes × SimState3) × QueryLog ChalZModSpec}
    (hz : z ∈ support (simulateQ ChalZModSpec.loggingOracle ((trackedRoImpl3 bs).run st)).run) :
    z.1.2.2.1 bs = some z.1.1 := by
  rcases support_step_ro bs st hz with
    ⟨w, hc, rfl⟩ | ⟨_, _, w, _, _, rfl⟩ | ⟨_, _, _, w, _, _, rfl⟩
  · exact hc
  · exact QueryCache.cacheQuery_self st.2.1 bs w
  · exact QueryCache.cacheQuery_self st.2.1 bs w

private theorem innerFull_final_cache {P : Primitives}
    {isValidDhTriple : Bytes → Bytes → Bytes → Bool}
    {pk : Bytes} {bSim : UInt8} {A : GapSigEufCmaRoAdv}
    {mStar sigStar wStar : Bytes} {st : SimState3} {outerLog : QueryLog ChalZModSpec}
    (hz : (((mStar, sigStar, some wStar), st), outerLog) ∈ support
      (simulateQ ChalZModSpec.loggingOracle
        ((simulateQ (trackedInnerImpl P pk bSim)
          (innerFull P isValidDhTriple pk A)).run ([], ∅, []))).run) :
    ∃ chalIn, xeddsaVerifyChalInput? P pk mStar sigStar = some chalIn ∧
      st.2.1 chalIn = some wStar := by
  unfold innerFull at hz
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind', support_bind] at hz
  simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
  obtain ⟨⟨⟨⟨m₁, s₁⟩, st₁⟩, log₁⟩, _, pw, hpw, hpair⟩ := hz
  have hpw1 : pw.1 = ((mStar, sigStar, some wStar), st) := congrArg Prod.fst hpair
  dsimp only at hpw
  rcases hchal : xeddsaVerifyChalInput? P pk m₁ s₁ with _ | chalIn
  · rw [hchal] at hpw
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
      support_pure, Set.mem_singleton_iff] at hpw
    rw [hpw] at hpw1
    simp at hpw1
  · rw [hchal] at hpw
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      trackedInnerImpl, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure,
      WriterT.run_bind', support_bind, Set.mem_iUnion, support_map, Set.mem_image,
      WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hpw
    obtain ⟨ro_w, hro_w, _, rfl, hpw_eq⟩ := hpw
    have hpw_fst : ((m₁, s₁, some ro_w.1.1), ro_w.1.2) = pw.1 := congrArg Prod.fst hpw_eq
    rw [← hpw_fst] at hpw1
    simp only [Prod.mk.injEq, Option.some.injEq] at hpw1
    rcases hpw1 with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨chalIn, hchal, trackedRoImpl3_cache_eq_some hro_w⟩

private theorem wrappedTrace_replayFirstRun_props {P : Primitives}
    (C : XeddsaCurveWitness P) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) {bSim : UInt8} (hbSim : bSim = 0 ∨ bSim = 1)
    (A : GapSigEufCmaRoAdv) (q_H : ℕ)
    {tr : Trace} {outerLog : QueryLog ChalZModSpec}
    (htr : (tr, outerLog) ∈ support
      (OracleComp.replayFirstRun (wrappedTrace P isValidDhTriple (P.x25519Base sk) bSim A)))
    (hacc : tr.accepted = true) :
    tr.queryLog.length = outerLog.countQ (· = Sum.inr ()) ∧
    tr.targetKey ∈ tr.queryLog ∧
    xeddsaVerifyChalInput? P (P.x25519Base sk) tr.mStar tr.sigStar = some tr.targetKey ∧
    xeddsaVerifyWithDigest P (P.x25519Base sk) tr.mStar tr.sigStar tr.wStar = true ∧
    (∀ s : Fin (q_H + 1), forkPoint q_H tr = some s →
      QueryLog.getQueryValue? outerLog (Sum.inr ()) s.val = some tr.hUsed) := by
  let pk := P.x25519Base sk
  unfold OracleComp.replayFirstRun OracleComp.withQueryLog wrappedTrace at htr
  simp only [simulateQ_map, WriterT.run_map', support_map, Set.mem_image] at htr
  obtain ⟨⟨⟨⟨mStar, sigStar, wStar?⟩, st⟩, log⟩, hmem, heq⟩ := htr
  obtain ⟨htr_eq, rfl⟩ := Prod.mk.inj heq
  cases wStar? with
  | none =>
      rw [← htr_eq] at hacc
      simp [buildTrace] at hacc
  | some wStar =>
      obtain ⟨chalIn, hchal, hcache_star⟩ := innerFull_final_cache hmem
      obtain ⟨hlen, hlock, hprov⟩ := inner_honest_invariant C sk hbSim
        (innerFull P isValidDhTriple pk A) hmem
      rw [← htr_eq] at hacc ⊢
      dsimp only [buildTrace] at hacc ⊢
      rw [hchal]
      simp only [Option.getD_some]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
      obtain ⟨hver, hfresh⟩ := hacc
      obtain ⟨_, y, _, hchal_y, _, hnoH1, hdrop64⟩ := xeddsaVerifyWithDigest_spec C hver
      have hchal_eq : chalIn = sigStar.take 32 ++ C.compressEd y ++ mStar :=
        Option.some.inj (hchal.symm.trans hchal_y)
      have hmem_qlog : chalIn ∈ st.2.2 := by
        rcases hprov chalIn wStar hcache_star with hq | hh1 | hmsg
        · exact hq
        · rw [hchal_eq, hnoH1] at hh1; cases hh1
        · rw [hchal_eq, hdrop64] at hmsg; exact absurd hmsg hfresh
      refine ⟨hlen, hmem_qlog, trivial, hver, ?_⟩
      intro s hs
      have hget : st.2.2[s.val]? = some chalIn := by
        simpa [buildTrace, hchal] using forkPoint_getElem?_eq_some_target hs
      obtain ⟨hslt, hs_elem⟩ := List.getElem?_eq_some_iff.mp hget
      obtain ⟨d, h, hd_cache, hd_dec, hqv⟩ := hlock s.val hslt
      rw [hs_elem, hcache_star] at hd_cache
      obtain rfl := Option.some.inj hd_cache
      simpa [Trace.hUsed, buildTrace, hd_dec] using hqv

theorem wrappedTrace_forkPoint_isSome_eq_accepted {P : Primitives}
    (C : XeddsaCurveWitness P) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) {bSim : UInt8} (hbSim : bSim = 0 ∨ bSim = 1)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded)
    {tr : Trace}
    (htr : tr ∈ support (wrappedTrace P isValidDhTriple (P.x25519Base sk) bSim A)) :
    (forkPoint (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) tr).isSome = tr.accepted := by
  let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
  cases hacc : tr.accepted with
  | false =>
      simp [forkPoint, hacc]
  | true =>
      obtain ⟨outerLog, hlog⟩ := exists_log_of_mem_support htr
      have hcount_le : outerLog.countQ (· = Sum.inr ()) ≤ q_H + 1 :=
        log_countQ_le_of_isQueryBoundP
          (wrappedTrace_isQueryBoundP P isValidDhTriple (P.x25519Base sk) bSim hA) hlog
      obtain ⟨hlen, hmem_qlog, _, _, _⟩ :=
        wrappedTrace_replayFirstRun_props C isValidDhTriple sk hbSim A q_H hlog hacc
      have hfind_lt : ∀ (l : List Bytes) (k : Bytes), k ∈ l → l.findIdx (· == k) < l.length := by
        intro l k hk
        induction l with
        | nil => cases hk
        | cons hd tl ih =>
            simp only [List.findIdx_cons]
            by_cases h : (hd == k) = true
            · simp [h]
            · have hf : (hd == k) = false := Bool.eq_false_iff.mpr h
              rcases List.mem_cons.mp hk with rfl | htl
              · simp at h
              · simpa [hf] using Nat.succ_lt_succ (ih htl)
      have hidx_lt : tr.queryLog.findIdx (· == tr.targetKey) < q_H + 1 :=
        Nat.lt_of_lt_of_le (hfind_lt tr.queryLog tr.targetKey hmem_qlog) (hlen ▸ hcount_le)
      simp only [forkPoint, hacc, ↓reduceIte, hmem_qlog]
      split_ifs with hidx
      · rfl
      · exact absurd hidx_lt hidx

private theorem inner_prefix_det_one_more_inr {γ : Type}
    (P : Primitives) (pk : Bytes) (bSim : UInt8)
    (Y : OracleComp InnerSpec γ) (st : SimState3)
    {z₁ z₂ : γ × SimState3}
    {outerLog₁ outerLog₂ : QueryLog ChalZModSpec}
    (h₁ : (z₁, outerLog₁) ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P pk bSim) Y).run st)).run)
    (h₂ : (z₂, outerLog₂) ∈ support (simulateQ ChalZModSpec.loggingOracle
      ((simulateQ (trackedInnerImpl P pk bSim) Y).run st)).run)
    (p : QueryLog ChalZModSpec)
    {v₁ v₂ : ZMod l25519} {rest₁ rest₂ : QueryLog ChalZModSpec}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    z₁.2.2.2.take (st.2.2.length + p.countQ (· = Sum.inr ()) + 1) =
      z₂.2.2.2.take (st.2.2.length + p.countQ (· = Sum.inr ()) + 1) := by
  induction Y using OracleComp.inductionOn generalizing
      st z₁ z₂ outerLog₁ outerLog₂ p v₁ v₂ rest₁ rest₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      simp at hlog₁
  | query_bind t oa ih =>
      rw [OracleComp.run_simulateQ_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      dsimp only [Prod.map, id] at hz_eq₁ hz_eq₂
      obtain ⟨rfl, hz_eq2₁⟩ := Prod.mk.inj hz_eq₁
      obtain ⟨rfl, hz_eq2₂⟩ := Prod.mk.inj hz_eq₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁) :=
        hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂) :=
        hz_eq2₂.trans hlog₂
      rcases t with ((n | q) | bs)
      · obtain ⟨u₁, rfl⟩ := support_step_unif P pk bSim n st hus_w₁
        obtain ⟨u₂, rfl⟩ := support_step_unif P pk bSim n st hus_w₂
        cases p with
        | nil =>
            simp only [List.singleton_append, List.nil_append, List.cons.injEq] at houter₁_eq
            exact absurd (congrArg Sigma.fst houter₁_eq.1) (by simp)
        | cons ph pt =>
            simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
            obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
            obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
            have hu : u₁ = u₂ := eq_of_heq (Sigma.mk.inj (hhead₁.trans hhead₂.symm)).2
            subst hu
            have hph_ne : ph.1 ≠ Sum.inr () := by
              rw [← hhead₁]; simp
            have hp_count :
                QueryLog.countQ (spec := ChalZModSpec) (ph :: pt) (· = Sum.inr ()) =
                  QueryLog.countQ (spec := ChalZModSpec) pt (· = Sum.inr ()) := by
              simp [QueryLog.countQ, QueryLog.getQ_cons, hph_ne]
            rw [hp_count]
            exact ih u₁ st hpw₁ hpw₂ pt htail₁ htail₂
      · obtain rfl := support_step_progSign P pk bSim q st hus_w₁
        obtain rfl := support_step_progSign P pk bSim q st hus_w₂
        simp only [List.nil_append] at houter₁_eq houter₂_eq
        have hqlog_eq : (progSignStep P pk bSim q st).2.2.2 = st.2.2 := rfl
        rw [← hqlog_eq]
        exact ih (progSignStep P pk bSim q st).1 (progSignStep P pk bSim q st).2
          hpw₁ hpw₂ p houter₁_eq houter₂_eq
      · simp only [trackedInnerImpl, QueryImpl.add_apply_inr] at hus_w₁ hus_w₂
        rcases support_step_ro bs st hus_w₁ with
          ⟨w₁, hc₁, rfl⟩ | ⟨hnone₁, hh1_t₁, w₁, uLog₁, huLog₁, rfl⟩ |
            ⟨hnone₁, hh1_f₁, hchal₁, w₁, uLog₁, huLog₁, rfl⟩
        · rcases support_step_ro bs st hus_w₂ with
            ⟨w₂, hc₂, rfl⟩ | ⟨hnone₂, _, _⟩ | ⟨hnone₂, _, _⟩
          · obtain rfl := Option.some.inj (hc₁.symm.trans hc₂)
            simp only [List.nil_append] at houter₁_eq houter₂_eq
            exact ih w₁ st hpw₁ hpw₂ p houter₁_eq houter₂_eq
          · rw [hc₁] at hnone₂; cases hnone₂
          · rw [hc₁] at hnone₂; cases hnone₂
        · rcases support_step_ro bs st hus_w₂ with
            ⟨_, hc₂, _⟩ | ⟨_, _, w₂, uLog₂, huLog₂, rfl⟩ | ⟨_, hh1_f₂, _⟩
          · rw [hnone₁] at hc₂; cases hc₂
          · obtain ⟨_, hne₁⟩ := liftUnifChal_log_spec huLog₁
            obtain ⟨_, hne₂⟩ := liftUnifChal_log_spec huLog₂
            obtain ⟨p₁', hp₁', htail₁⟩ := all_inl_append_eq_append_inr hne₁ houter₁_eq
            obtain ⟨p₂', hp₂', htail₂⟩ := all_inl_append_eq_append_inr hne₂ houter₂_eq
            obtain ⟨rfl, rfl, rfl⟩ :=
              liftUnifChal_log_prefix_det huLog₁ huLog₂ (hp₁'.symm.trans hp₂')
            have hp_count : p.countQ (· = Sum.inr ()) = p₁'.countQ (· = Sum.inr ()) := by
              rw [hp₁', QueryLog.countQ_append, countQ_eq_zero_of_forall_ne hne₁, zero_add]
            rw [hp_count]
            exact ih w₁ (st.1, st.2.1.cacheQuery bs w₁, st.2.2) hpw₁ hpw₂ p₁' htail₁ htail₂
          · rw [hh1_t₁] at hh1_f₂; cases hh1_f₂
        · rcases support_step_ro bs st hus_w₂ with
            ⟨_, hc₂, _⟩ | ⟨_, hh1_t₂, _⟩ | ⟨_, _, hchal₂, w₂, uLog₂, huLog₂, rfl⟩
          · rw [hnone₁] at hc₂; cases hc₂
          · rw [hh1_f₁] at hh1_t₂; cases hh1_t₂
          · cases p with
            | nil =>
                simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                have h₁' := inner_queryLog_extends P pk bSim (oa w₁)
                  (st.1, st.2.1.cacheQuery bs w₁, st.2.2 ++ [bs]) hpw₁
                have h₂' := inner_queryLog_extends P pk bSim (oa w₂)
                  (st.1, st.2.1.cacheQuery bs w₂, st.2.2 ++ [bs]) hpw₂
                have hlen_app : (st.2.2 ++ [bs]).length = st.2.2.length + 1 := by simp
                dsimp only at h₁' h₂'
                rw [← hlen_app, h₁', h₂']
            | cons ph pt =>
                simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
                obtain ⟨hhead₁, htail₁_raw⟩ := houter₁_eq
                obtain ⟨hhead₂, htail₂_raw⟩ := houter₂_eq
                have hh_eq : hchal₁ = hchal₂ :=
                  eq_of_heq (Sigma.mk.inj (hhead₁.trans hhead₂.symm)).2
                subst hh_eq
                obtain ⟨_, hne₁⟩ := liftUnifChal_log_spec huLog₁
                obtain ⟨_, hne₂⟩ := liftUnifChal_log_spec huLog₂
                obtain ⟨p₁', hp₁', htail₁⟩ := all_inl_append_eq_append_inr hne₁ htail₁_raw
                obtain ⟨p₂', hp₂', htail₂⟩ := all_inl_append_eq_append_inr hne₂ htail₂_raw
                obtain ⟨rfl, rfl, rfl⟩ :=
                  liftUnifChal_log_prefix_det huLog₁ huLog₂ (hp₁'.symm.trans hp₂')
                have hph_fst : ph.1 = Sum.inr () := by
                  simpa using congrArg Sigma.fst hhead₁.symm
                have hp_count :
                    QueryLog.countQ (spec := ChalZModSpec) (ph :: pt) (· = Sum.inr ()) =
                      p₁'.countQ (· = Sum.inr ()) + 1 := by
                  have hcons :
                      QueryLog.countQ (spec := ChalZModSpec) (ph :: pt) (· = Sum.inr ()) =
                        QueryLog.countQ (spec := ChalZModSpec) pt (· = Sum.inr ()) + 1 := by
                    simp [QueryLog.countQ, QueryLog.getQ_cons, hph_fst]
                  rw [hcons, hp₁', QueryLog.countQ_append, countQ_eq_zero_of_forall_ne hne₁,
                    zero_add]
                have hlen_shift :
                    st.2.2.length + (p₁'.countQ (· = Sum.inr ()) + 1) + 1 =
                      (st.2.2 ++ [bs]).length + p₁'.countQ (· = Sum.inr ()) + 1 := by
                  simp [List.length_append]
                  omega
                rw [hp_count, hlen_shift]
                exact ih w₁ (st.1, st.2.1.cacheQuery bs w₁, st.2.2 ++ [bs])
                  hpw₁ hpw₂ p₁' htail₁ htail₂

private theorem wrappedTrace_queryLog_take_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv)
    {tr₁ tr₂ : Trace} {outerLog₁ outerLog₂ : QueryLog ChalZModSpec}
    (h₁ : (tr₁, outerLog₁) ∈ support
      (OracleComp.replayFirstRun (wrappedTrace P isValidDhTriple pk bSim A)))
    (h₂ : (tr₂, outerLog₂) ∈ support
      (OracleComp.replayFirstRun (wrappedTrace P isValidDhTriple pk bSim A)))
    (p : QueryLog ChalZModSpec)
    {v₁ v₂ : ZMod l25519} {rest₁ rest₂ : QueryLog ChalZModSpec}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    tr₁.queryLog.take (p.countQ (· = Sum.inr ()) + 1) =
      tr₂.queryLog.take (p.countQ (· = Sum.inr ()) + 1) := by
  unfold OracleComp.replayFirstRun OracleComp.withQueryLog wrappedTrace at h₁ h₂
  simp only [simulateQ_map, WriterT.run_map', support_map, Set.mem_image] at h₁ h₂
  obtain ⟨⟨⟨out₁, st₁⟩, log₁⟩, hmem₁, heq₁⟩ := h₁
  obtain ⟨⟨⟨out₂, st₂⟩, log₂⟩, hmem₂, heq₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₂
  have hq₁ : (buildTrace P pk (out₁, st₁)).queryLog = st₁.2.2 := by
    rcases out₁ with ⟨_, _, _ | _⟩ <;> rfl
  have hq₂ : (buildTrace P pk (out₂, st₂)).queryLog = st₂.2.2 := by
    rcases out₂ with ⟨_, _, _ | _⟩ <;> rfl
  rw [hq₁, hq₂]
  simpa using inner_prefix_det_one_more_inr P pk bSim
    (innerFull P isValidDhTriple pk A) ([], ∅, []) hmem₁ hmem₂ p hlog₁ hlog₂

/-- Any successful fork on `wrappedTrace` at `P.x25519Base sk` produces two accepting transcripts
    sharing the same challenge input under distinct `ZMod l25519` challenges `tr₁.hUsed ≠ tr₂.hUsed`. -/
theorem wrappedTrace_contextFork_sound {P : Primitives}
    (C : XeddsaCurveWitness P) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) {bSim : UInt8} (hbSim : bSim = 0 ∨ bSim = 1)
    (A : GapSigEufCmaRoAdv) (q_H : ℕ)
    {tr₁ tr₂ : Trace}
    (hsup : some (tr₁, tr₂) ∈ support
      (OracleComp.contextFork
        (wrappedTrace P isValidDhTriple (P.x25519Base sk) bSim A)
        (forkQbChal q_H) (Sum.inr ()) (forkPoint q_H))) :
    xeddsaVerifyWithDigest P (P.x25519Base sk) tr₁.mStar tr₁.sigStar tr₁.wStar = true ∧
      xeddsaVerifyWithDigest P (P.x25519Base sk) tr₂.mStar tr₂.sigStar tr₂.wStar = true ∧
      xeddsaVerifyChalInput? P (P.x25519Base sk) tr₁.mStar tr₁.sigStar =
        xeddsaVerifyChalInput? P (P.x25519Base sk) tr₂.mStar tr₂.sigStar ∧
      tr₁.hUsed ≠ tr₂.hUsed := by
  let pk := P.x25519Base sk
  let main := wrappedTrace P isValidDhTriple pk bSim A
  let qb := forkQbChal q_H
  let cf := forkPoint q_H
  let P_out : Trace → QueryLog ChalZModSpec → Prop := fun tr log =>
    tr.accepted = true →
      xeddsaVerifyChalInput? P pk tr.mStar tr.sigStar = some tr.targetKey ∧
        xeddsaVerifyWithDigest P pk tr.mStar tr.sigStar tr.wStar = true ∧
        (∀ s : Fin (q_H + 1), cf tr = some s →
          QueryLog.getQueryValue? log (Sum.inr ()) s.val = some tr.hUsed)
  have hP : ∀ {tr log}, (tr, log) ∈ support (OracleComp.replayFirstRun main) → P_out tr log := by
    intro tr log hmem hacc
    obtain ⟨_, _, hchal, hver, hqv⟩ :=
      wrappedTrace_replayFirstRun_props C isValidDhTriple sk hbSim A q_H hmem hacc
    exact ⟨hchal, hver, hqv⟩
  obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
    OracleComp.contextFork_propertyTransfer main qb (Sum.inr ()) cf P_out hP hsup
  obtain ⟨hchal₁, hver₁, hqv₁⟩ := hP₁ (accepted_of_forkPoint_eq_some hcf₁)
  obtain ⟨hchal₂, hver₂, hqv₂⟩ := hP₂ (accepted_of_forkPoint_eq_some hcf₂)
  have hh_ne : tr₁.hUsed ≠ tr₂.hUsed := by
    intro heq
    apply hneq
    rw [hqv₁ s hcf₁, hqv₂ s hcf₂, heq]
  obtain ⟨path, s', located, second, hpath, hcf_path, _, _, _, htr₁, htr₂⟩ :=
    OracleComp.contextFork_success main qb (Sum.inr ()) cf hsup
  have hs' : s' = s := by
    apply Option.some.inj
    calc some s' = cf (PFunctor.FreeM.output main path) := hcf_path.symm
      _ = cf tr₁ := by rw [htr₁]
      _ = some s := hcf₁
  subst s'
  let commonLog : QueryLog ChalZModSpec := located.occurrence.before
  have hfirst := OracleComp.replayPathResult_mem_support_replayFirstRun main path hpath
  have hsecond := OracleComp.replayPathResult_mem_support_replayFirstRun main second.path
    (OracleComp.mem_support_replayFirstPath main second.path)
  have htrlog₁ : (tr₁, (OracleComp.replayPathResult main path).2) ∈
      support (OracleComp.replayFirstRun main) := by
    simpa [OracleComp.replayPathResult, OracleComp.pathLogResult, htr₁] using hfirst
  have htrlog₂ : (tr₂, (OracleComp.replayPathResult main second.path).2) ∈
      support (OracleComp.replayFirstRun main) := by
    simpa [OracleComp.replayPathResult, OracleComp.pathLogResult, htr₂] using hsecond
  have hlog_eq₁ : (OracleComp.replayPathResult main path).2 =
      commonLog ++
        (⟨Sum.inr (), located.completion.answer⟩ ::
          (OracleComp.replayPathResult (located.occurrence.resume
            located.completion.answer) located.completion.suffix).2) := by
    have htrace := congrArg
      (fun p : PFunctor.FreeM.Path main =>
        (show QueryLog ChalZModSpec from PFunctor.FreeM.Path.trace main p))
      located.path_eq
    calc (OracleComp.replayPathResult main path).2
        = (OracleComp.replayPathResult main located.completion.path).2 := htrace.symm
      _ = _ := by
          change PFunctor.FreeM.Path.trace main located.completion.path =
            List.append (show PFunctor.TraceList ChalZModSpec.toPFunctor from commonLog)
              (⟨Sum.inr (), located.completion.answer⟩ ::
                PFunctor.FreeM.Path.trace
                  (located.occurrence.resume located.completion.answer)
                  located.completion.suffix)
          exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
            located.occurrence located.completion.answer located.completion.suffix
  have hlog_eq₂ : (OracleComp.replayPathResult main second.path).2 =
      commonLog ++
        (⟨Sum.inr (), second.answer⟩ ::
          (OracleComp.replayPathResult (located.occurrence.resume second.answer)
            second.suffix).2) := by
    change PFunctor.FreeM.Path.trace main second.path =
      List.append (show PFunctor.TraceList ChalZModSpec.toPFunctor from commonLog)
        (⟨Sum.inr (), second.answer⟩ ::
          PFunctor.FreeM.Path.trace
            (located.occurrence.resume second.answer) second.suffix)
    exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
      located.occurrence second.answer second.suffix
  have htakeEq := wrappedTrace_queryLog_take_eq P isValidDhTriple pk bSim A
    htrlog₁ htrlog₂ commonLog hlog_eq₁ hlog_eq₂
  have hprefixCount : commonLog.countQ (· = Sum.inr ()) = (s : ℕ) := by
    calc commonLog.countQ (· = Sum.inr ())
        = PFunctor.TraceList.occurrences (P := ChalZModSpec.toPFunctor) (Sum.inr ())
            (show PFunctor.TraceList ChalZModSpec.toPFunctor from commonLog) :=
          QueryLog.countQ_eq_occurrences commonLog (Sum.inr ())
      _ = (s : ℕ) := by simp [commonLog]
  rw [hprefixCount] at htakeEq
  have htgt₁ : tr₁.queryLog[(s : ℕ)]? = some tr₁.targetKey :=
    forkPoint_getElem?_eq_some_target hcf₁
  have htgt₂ : tr₂.queryLog[(s : ℕ)]? = some tr₂.targetKey :=
    forkPoint_getElem?_eq_some_target hcf₂
  have hgetTake (l : List Bytes) :
      (l.take ((s : ℕ) + 1))[(s : ℕ)]? = l[(s : ℕ)]? :=
    List.getElem?_take_of_lt (Nat.lt_succ_self _)
  have htgt_eq : tr₁.targetKey = tr₂.targetKey := by
    apply Option.some.inj
    rw [← htgt₁, ← htgt₂, ← hgetTake tr₁.queryLog, ← hgetTake tr₂.queryLog, htakeEq]
  refine ⟨hver₁, hver₂, ?_, hh_ne⟩
  rw [hchal₁, hchal₂, htgt_eq]

end Coupling

/-! ## Replay-forking `GapDH` adversary and main EUF-CMA bounds -/

section MainReduction

noncomputable local instance : DecidableEq ForkSpec.Domain :=
  Classical.decEq _

noncomputable local instance (t : ForkSpec.Domain) : DecidableEq (ForkSpec.Range t) :=
  Classical.decEq _

noncomputable def liftUnifBase {α : Type} (oa : ProbComp α) :
    OracleComp (PrimBaseSpec + gapDhOracleSpec) α :=
  simulateQ (QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec))) oa

noncomputable def forkRunAt (P : Primitives) (A : GapSigEufCmaRoAdv)
    (bSim : UInt8) (U V : Bytes) :
    OracleComp (PrimBaseSpec + gapDhOracleSpec) Bytes := do
  let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
  let res? ← simulateQ answerChalOnBase
    (OracleComp.contextFork (rawTrace P U bSim A) (forkQbFork q_H) (Sum.inr ()) (forkPoint q_H))
  match res? with
  | none => pure (List.replicate 32 0)
  | some (tr₁, tr₂) =>
      let skExt := extractClampedKey tr₁.sigStar tr₂.sigStar tr₁.hUsed tr₂.hUsed
      liftM ((PrimBaseSpec + gapDhOracleSpec).query (Sum.inl (Sum.inr (.x25519 skExt V))))

/-- Replay-forking `GapDH` adversary guessing the Edwards public-key sign bit before
    `OracleComp.contextFork` and issuing a single `.x25519` query on the recovered clamped scalar. -/
noncomputable def forkGapDhAdv (P : Primitives) (A : GapSigEufCmaRoAdv) : GapDhAdv where
  run U V := do
    let bBool ← liftUnifBase ($ᵗ Bool)
    let bSim : UInt8 := if bBool then 1 else 0
    forkRunAt P A bSim U V
  q_ddh := 2 * A.q_ddh
  q_prim := 2 * A.q_prim + 1

private theorem isQueryBoundP_liftUnifBase {α : Type} (oa : ProbComp α)
    (pred : (PrimBaseSpec + gapDhOracleSpec).Domain → Prop) [DecidablePred pred]
    (hpred : ∀ n, ¬ pred (Sum.inl (Sum.inl n))) :
    OracleComp.IsQueryBoundP (liftUnifBase oa) pred 0 := by
  unfold liftUnifBase
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind n mx ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.ofLift]
      change OracleComp.IsQueryBoundP
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query (Sum.inl (Sum.inl n))) >>= fun u =>
          simulateQ (QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec)))
            (mx u))
        pred 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (hpred n), fun u => by simpa using ih u⟩

private theorem isQueryBoundP_answerChalOnBase_ddh {α : Type}
    {oa : OracleComp ForkSpec α} {N : ℕ}
    (h : OracleComp.IsQueryBoundP oa (fun q => isForkDdhQuery q = true) N) :
    OracleComp.IsQueryBoundP (simulateQ answerChalOnBase oa)
      (fun q : (PrimBaseSpec + gapDhOracleSpec).Domain => q.isRight = true) N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure _ => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rcases t with (q | u_unit)
      · have h1 : ¬ (q.isRight = true) ∨ 0 < N := by
          rcases q with (_ | _) <;> exact h.1
        have h2 :
            (if isForkDdhQuery (Sum.inl q) = true then N - 1 else N) =
              (if q.isRight = true then N - 1 else N) := by
          rcases q with (_ | _) <;> rfl
        simp only [simulateQ_bind, simulateQ_spec_query, answerChalOnBase]
        change OracleComp.IsQueryBoundP
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query q) >>= fun u =>
            simulateQ answerChalOnBase (mx u))
          (fun q : (PrimBaseSpec + gapDhOracleSpec).Domain => q.isRight = true) N
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨h1, fun u => ih u (h2 ▸ h.2 u)⟩
      · cases u_unit
        simp only [simulateQ_bind, simulateQ_spec_query, answerChalOnBase]
        change OracleComp.IsQueryBoundP
          (liftUnifBase ($ᵗ (ZMod l25519)) >>= fun u => simulateQ answerChalOnBase (mx u))
          (fun q : (PrimBaseSpec + gapDhOracleSpec).Domain => q.isRight = true) N
        refine (OracleComp.isQueryBoundP_bind (n := 0) (m := N)
          (isQueryBoundP_liftUnifBase ($ᵗ (ZMod l25519)) _ (by simp)) ?_).mono (by omega)
        intro u _
        have h2 : (if isForkDdhQuery (Sum.inr ()) = true then N - 1 else N) = N := rfl
        exact ih u (h2 ▸ h.2 u)

private theorem isQueryBoundP_answerChalOnBase_prim {α : Type}
    {oa : OracleComp ForkSpec α} {N : ℕ}
    (h : OracleComp.IsQueryBoundP oa (fun q => isForkPrimQuery q = true) N) :
    OracleComp.IsQueryBoundP (simulateQ answerChalOnBase oa) (fun q => isPrimQuery q = true) N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure _ => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      rcases t with (q | u_unit)
      · have h1 : ¬ (isPrimQuery q = true) ∨ 0 < N := by
          rcases q with ((_ | _) | _) <;> exact h.1
        have h2 :
            (if isForkPrimQuery (Sum.inl q) = true then N - 1 else N) =
              (if isPrimQuery q = true then N - 1 else N) := by
          rcases q with ((_ | _) | _) <;> rfl
        simp only [simulateQ_bind, simulateQ_spec_query, answerChalOnBase]
        change OracleComp.IsQueryBoundP
          (liftM ((PrimBaseSpec + gapDhOracleSpec).query q) >>= fun u =>
            simulateQ answerChalOnBase (mx u))
          (fun q => isPrimQuery q = true) N
        rw [OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨h1, fun u => ih u (h2 ▸ h.2 u)⟩
      · cases u_unit
        simp only [simulateQ_bind, simulateQ_spec_query, answerChalOnBase]
        change OracleComp.IsQueryBoundP
          (liftUnifBase ($ᵗ (ZMod l25519)) >>= fun u => simulateQ answerChalOnBase (mx u))
          (fun q => isPrimQuery q = true) N
        refine (OracleComp.isQueryBoundP_bind (n := 0) (m := N)
          (isQueryBoundP_liftUnifBase ($ᵗ (ZMod l25519)) _ (by simp [isPrimQuery])) ?_).mono
          (by omega)
        intro u _
        have h2 : (if isForkPrimQuery (Sum.inr ()) = true then N - 1 else N) = N := rfl
        exact ih u (h2 ▸ h.2 u)

theorem forkGapDhAdv_bounded (P : Primitives) {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    (forkGapDhAdv P A).Bounded := by
  refine ⟨fun U V => ?_, fun U V => ?_⟩
  · dsimp only [forkGapDhAdv, forkRunAt]
    refine (OracleComp.isQueryBoundP_bind (n := 0) (m := A.q_ddh + A.q_ddh)
      (isQueryBoundP_liftUnifBase ($ᵗ Bool) _ (by simp)) ?_).mono (by omega)
    intro bBool _
    refine (OracleComp.isQueryBoundP_bind (n := A.q_ddh + A.q_ddh) (m := 0)
      (isQueryBoundP_answerChalOnBase_ddh
        (OracleComp.isQueryBoundP_contextFork _ _ _ _ _ A.q_ddh
          (rawTrace_isQueryBoundP_ddh P U (if bBool then 1 else 0) hA))) ?_).mono (by omega)
    rintro (_ | ⟨tr₁, tr₂⟩) _
    · simp
    · dsimp only
      change OracleComp.IsQueryBoundP
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query
          (Sum.inl (Sum.inr (.x25519
            (extractClampedKey tr₁.sigStar tr₂.sigStar tr₁.hUsed tr₂.hUsed) V)))) >>= pure)
        (fun q : (PrimBaseSpec + gapDhOracleSpec).Domain => q.isRight = true) 0
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun _ => trivial⟩
  · dsimp only [forkGapDhAdv, forkRunAt]
    refine (OracleComp.isQueryBoundP_bind (n := 0) (m := (A.q_prim + A.q_prim) + 1)
      (isQueryBoundP_liftUnifBase ($ᵗ Bool) _ (by simp [isPrimQuery])) ?_).mono (by omega)
    intro bBool _
    refine (OracleComp.isQueryBoundP_bind (n := A.q_prim + A.q_prim) (m := 1)
      (isQueryBoundP_answerChalOnBase_prim
        (OracleComp.isQueryBoundP_contextFork _ _ _ _ _ A.q_prim
          (rawTrace_isQueryBoundP_prim P U (if bBool then 1 else 0) hA))) ?_).mono (by omega)
    rintro (_ | ⟨tr₁, tr₂⟩) _
    · simp
    · dsimp only
      change OracleComp.IsQueryBoundP
        (liftM ((PrimBaseSpec + gapDhOracleSpec).query
          (Sum.inl (Sum.inr (.x25519
            (extractClampedKey tr₁.sigStar tr₂.sigStar tr₁.hUsed tr₂.hUsed) V)))) >>= pure)
        (fun q => isPrimQuery q = true) 1
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr (by omega), fun _ => trivial⟩

private theorem simulateQ_base_liftUnifBase (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp) {α : Type} (oa : ProbComp α) :
    simulateQ (primBaseImpl P + ddhImpl) (liftUnifBase oa) = oa := by
  unfold liftUnifBase
  rw [← QueryImpl.simulateQ_compose]
  have hid : (primBaseImpl P + ddhImpl) ∘ₛ
      QueryImpl.ofLift unifSpec (OracleComp (PrimBaseSpec + gapDhOracleSpec)) =
      QueryImpl.id' unifSpec := by
    funext n
    rw [QueryImpl.apply_compose, QueryImpl.ofLift_apply]
    change simulateQ (primBaseImpl P + ddhImpl)
      (liftM ((PrimBaseSpec + gapDhOracleSpec).query (Sum.inl (Sum.inl n)))) = _
    rw [simulateQ_spec_query]
    rfl
  rw [hid, simulateQ_id']

private noncomputable def forkFinish (P : Primitives) (V : Bytes) : Option (Trace × Trace) → Bytes
  | none => List.replicate 32 0
  | some (tr₁, tr₂) =>
      P.x25519 (extractClampedKey tr₁.sigStar tr₂.sigStar tr₁.hUsed tr₂.hUsed) V

private theorem simulateQ_base_forkRunAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (A : GapSigEufCmaRoAdv) (bSim : UInt8) (U V : Bytes) :
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
    simulateQ (primBaseImpl P + ddhImpl) (forkRunAt P A bSim U V) =
      forkFinish P V <$>
        simulateQ evalChalZMod
          (OracleComp.contextFork (wrappedTrace P isValidDhTriple U bSim A)
            (forkQbChal q_H) (Sum.inr ()) (forkPoint q_H)) := by
  intro ddhImpl q_H
  unfold forkRunAt
  rw [simulateQ_bind, ← QueryImpl.simulateQ_compose,
    evalSide_comp_answerChalOnBase P isValidDhTriple,
    QueryImpl.simulateQ_compose, elimSide_contextFork_eq, elimSide_rawTrace_eq,
    map_eq_bind_pure_comp]
  refine bind_congr fun res? => ?_
  rcases res? with _ | ⟨tr₁, tr₂⟩
  · simp [forkFinish, simulateQ_pure]
  · simp only [Function.comp_apply, forkFinish]
    rw [simulateQ_spec_query]
    rfl

private theorem prEvent_coin_forkGapDhAdv (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp)
    (A : GapSigEufCmaRoAdv) {bTrue : UInt8} (hbTrue : bTrue = 0 ∨ bTrue = 1)
    (U V : Bytes) (pred : Bytes → Prop) :
    (2 : ℝ≥0∞)⁻¹ *
      Pr{let Z ← simulateQ (primBaseImpl P + ddhImpl) (forkRunAt P A bTrue U V)}[pred Z] ≤
      Pr{let Z ← simulateQ (primBaseImpl P + ddhImpl) ((forkGapDhAdv P A).run U V)}[pred Z] := by
  have hrun :
      simulateQ (primBaseImpl P + ddhImpl) ((forkGapDhAdv P A).run U V) =
        (($ᵗ Bool) >>= fun bBool =>
          simulateQ (primBaseImpl P + ddhImpl)
            (forkRunAt P A (if bBool then 1 else 0) U V)) := by
    dsimp only [forkGapDhAdv]
    rw [simulateQ_bind, simulateQ_base_liftUnifBase]
  rw [hrun, prEvent_bind_eq_sum_fintype]
  let bGoal : Bool := (bTrue == 1)
  have hbSim_eq : (if bGoal then (1 : UInt8) else 0) = bTrue := by
    rcases hbTrue with rfl | rfl <;> rfl
  have hsingle := Finset.single_le_sum
    (f := fun bBool : Bool =>
      Pr{let z ← $ᵗ Bool}[z = bBool] *
        Pr{
          let Z ← simulateQ (primBaseImpl P + ddhImpl)
            (forkRunAt P A (if bBool then 1 else 0) U V)}[pred Z])
    (fun _ _ => zero_le) (Finset.mem_univ bGoal)
  have hpr_bool : Pr{let z ← $ᵗ Bool}[z = bGoal] = (2 : ℝ≥0∞)⁻¹ := by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool]
    rfl
  rw [hpr_bool, hbSim_eq] at hsingle
  exact hsingle

private theorem forkGapDhAdv_pointwise_ennreal {P : Primitives}
    (hWF : WellFormedPrimitivesδ P) (C : XeddsaCurveWitness P)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded)
    {u : Bytes} (hu_len : u.length = 32) (v : Bytes) :
    let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
    let ddhImpl : QueryImpl gapDhOracleSpec ProbComp :=
      fun (X, Y, Z) => pure (P.isValidDhTriple X Y Z)
    let liftComp := simulateQ implLifted
      (simWithChalDigest P P.isValidDhTriple (P.x25519Base u)
        (C.edSign (clampedScalarZMod u)) A)
    let accU := Pr{let ok ← liftComp}[ok = true]
    let runComp := simulateQ (primBaseImpl P + ddhImpl)
      ((forkGapDhAdv P A).run (P.x25519Base u) (P.x25519Base v))
    (2 : ℝ≥0∞)⁻¹ * (accU * (accU / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹)) ≤
      Pr{let Z ← runComp}[(P.pow8 Z == P.pow8 (P.x25519 u (P.x25519Base v))) = true] := by
  intro q_H ddhImpl liftComp accU runComp
  let _ : MeasurableSpace Bool := ⊤
  let _ : MeasurableSpace (Option (Trace × Trace)) := ⊤
  let U := P.x25519Base u
  let V := P.x25519Base v
  let bTrue := C.edSign (clampedScalarZMod u)
  have hbTrue_bool : bTrue = 0 ∨ bTrue = 1 := C.edSign_bool (clampedScalarZMod u)
  let cfComp :=
    OracleComp.contextFork (wrappedTrace P P.isValidDhTriple U bTrue A)
      (forkQbChal q_H) (Sum.inr ()) (forkPoint q_H)
  have haccE_eq :
      (∑ s : Fin (q_H + 1),
        Pr{let tr ← wrappedTrace P P.isValidDhTriple U bTrue A}[forkPoint q_H tr = some s]) =
      accU := by
    rw [← _root_.prEvent_isSome_eq_sum]
    have hcongr :
        Pr{let tr ← wrappedTrace P P.isValidDhTriple U bTrue A}[(forkPoint q_H tr).isSome = true] =
          Pr{let tr ← wrappedTrace P P.isValidDhTriple U bTrue A}[tr.accepted = true] :=
      prEvent_congr_of_support _ _ _ fun tr htr => by
        rw [wrappedTrace_forkPoint_isSome_eq_accepted C P.isValidDhTriple u hbTrue_bool hA htr]
    rw [hcongr, ← prEvent_map (wrappedTrace P P.isValidDhTriple U bTrue A) Trace.accepted (· = true),
      map_accepted_wrappedTrace_eq, prEvent_eq_evalDist_singleton,
      ← (evalChalZMod_evalDistEq _).evalDist_eq,
      ← QueryImpl.simulateQ_compose, evalChalZMod_comp_liftChalImpl,
      ← prEvent_eq_evalDist_singleton]
  have hcf_le :
      accU * (accU / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹) ≤
        Pr{let r ← cfComp}[r.isSome = true] := by
    have hraw := OracleComp.le_prEvent_isSome_contextFork
      (wrappedTrace P P.isValidDhTriple U bTrue A) (forkQbChal q_H) (Sum.inr ()) (forkPoint q_H)
      (OracleComp.CfReachable.toPathCfReachable
        (wrappedTrace_forkPoint_cfReachable P P.isValidDhTriple U bTrue A q_H))
    have hcard : Fintype.card (ChalZModSpec.Range (Sum.inr ())) = l25519 := ZMod.card l25519
    simpa only [haccE_eq, forkQbChal, hcard] using hraw
  have heval_cf :
      Pr{let r ← cfComp}[r.isSome = true] =
        Pr{let r ← simulateQ evalChalZMod cfComp}[r.isSome = true] := by
    rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
      (evalChalZMod_evalDistEq cfComp).evalDist_eq]
  have hwin_bTrue :
      Pr{let r ← simulateQ evalChalZMod cfComp}[r.isSome = true] ≤
        Pr{let Z ← simulateQ (primBaseImpl P + ddhImpl) (forkRunAt P A bTrue U V)}[
          (P.pow8 Z == P.pow8 (P.x25519 u V)) = true] := by
    rw [simulateQ_base_forkRunAt P P.isValidDhTriple A bTrue U V, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun r hr hisSome => ?_
    rcases r with _ | ⟨tr₁, tr₂⟩
    · simp at hisSome
    have hr_cf : some (tr₁, tr₂) ∈ support cfComp := by
      rw [OracleComp.mem_support_iff_evalDist_singleton_pos,
        (evalChalZMod_evalDistEq cfComp).evalDist_eq,
        ← OracleComp.mem_support_iff_evalDist_singleton_pos] at hr
      exact hr
    obtain ⟨hver₁, hver₂, hchal_eq, hh_ne⟩ :=
      wrappedTrace_contextFork_sound C P.isValidDhTriple u hbTrue_bool A q_H hr_cf
    have hdh :=
      x25519_extractClampedKey_eq hWF C (v := v) hu_len hver₁ hver₂ hchal_eq rfl rfl hh_ne
    dsimp only [forkFinish]
    rw [show V = P.x25519Base v from rfl,
      show tr₁.hUsed = decodeScalarBytes (fitBytesRef 64 tr₁.wStar) from rfl,
      show tr₂.hUsed = decodeScalarBytes (fitBytesRef 64 tr₂.wStar) from rfl,
      hdh]
    exact beq_self_eq_true _
  exact (mul_le_mul_of_nonneg_left (hcf_le.trans (heval_cf.trans_le hwin_bTrue)) zero_le).trans
    (prEvent_coin_forkGapDhAdv P ddhImpl A hbTrue_bool U V
      (fun Z => (P.pow8 Z == P.pow8 (P.x25519 u V)) = true))

private theorem length_of_mem_support_sampleScalar32 {u : Bytes}
    (hu : u ∈ support sampleScalar32) : u.length = 32 := by
  unfold sampleScalar32 sampleBytes32 at hu
  rw [support_map] at hu
  rcases hu with ⟨w, _, rfl⟩
  simp [word256ToBytes]

/-- Raw quadratic forking-lemma bound reducing `gapSigEufCmaSimExp` to `GapDH` via `forkGapDhAdv`
    after subtracting `xeddsaModLoss q_H`. -/
theorem gapSigEufCmaSim_forking_quad (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (C : XeddsaCurveWitness P)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded) :
    let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
    let epsSim := max 0
      ((𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal - xeddsaModLoss q_H)
    (forkGapDhAdv P A).Bounded ∧
    (forkGapDhAdv P A).q_ddh ≤ 2 * A.q_ddh ∧
    (forkGapDhAdv P A).q_prim ≤ 2 * A.q_prim + 1 ∧
    epsSim * (epsSim / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ)) ≤
      2 * GapDH P P.isValidDhTriple P.pow8 (forkGapDhAdv P A) := by
  refine ⟨forkGapDhAdv_bounded P hA, le_rfl, le_rfl, ?_⟩
  let _ : MeasurableSpace Bytes := ⊤
  let _ : MeasurableSpace Bool := ⊤
  let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
  let ddhImpl : QueryImpl gapDhOracleSpec ProbComp :=
    fun (X, Y, Z) => pure (P.isValidDhTriple X Y Z)
  let liftAt (u : Bytes) : ProbComp Bool :=
    simulateQ implLifted
      (simWithChalDigest P P.isValidDhTriple (P.x25519Base u)
        (C.edSign (clampedScalarZMod u)) A)
  let acc (u : Bytes) : ℝ≥0∞ := Pr{let ok ← liftAt u}[ok = true]
  let gapUV (u v : Bytes) : ProbComp Bool := do
    let Z ← simulateQ (primBaseImpl P + ddhImpl)
      ((forkGapDhAdv P A).run (P.x25519Base u) (P.x25519Base v))
    pure (P.pow8 Z == P.pow8 (P.x25519 u (P.x25519Base v)))
  let gapU (u : Bytes) : ProbComp Bool := sampleScalar32 >>= gapUV u
  let ELiftE : ℝ≥0∞ := ∫⁻ u, acc u ∂𝒟[sampleScalar32]
  have hELiftE_le_one : ELiftE ≤ 1 := by
    have hbind : ELiftE = Pr{let ok ← sampleScalar32 >>= liftAt}[ok = true] :=
      (prEvent_bind_eq_lintegral_of_discrete sampleScalar32 liftAt (· = true)).symm
    exact hbind.trans_le (prEvent_le_one _)
  have hELiftE_ne_top : ELiftE ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hELiftE_le_one
  have hSimE_le :
      𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true} ≤
        ELiftE + ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide := by
    rw [← prEvent_eq_evalDist_singleton]
    unfold gapSigEufCmaSimExp
    rw [prEvent_bind_eq_lintegral_of_discrete]
    let simAt (u : Bytes) : ProbComp Bool :=
      gapSigEufCmaSimExpAt P P.isValidDhTriple u (C.edSign (clampedScalarZMod u)) A
    have hpt (u : Bytes) :
        Pr{let ok ← simAt u}[ok = true] ≤
          acc u + ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide :=
      prEvent_gapSigEufCmaSimExpOnPk_le_lifted_add P P.isValidDhTriple
        (P.x25519Base u) (C.edSign (clampedScalarZMod u)) hA
    calc ∫⁻ u, Pr{let ok ← simAt u}[ok = true] ∂𝒟[sampleScalar32]
        ≤ ∫⁻ u, acc u + ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide ∂𝒟[sampleScalar32] :=
          lintegral_mono hpt
      _ = ELiftE + ∫⁻ _, ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide ∂𝒟[sampleScalar32] :=
          lintegral_add_right _ measurable_const
      _ = ELiftE + ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide := by
          rw [lintegral_const, ← prEvent_true_eq_evalDist_apply_univ,
            OracleComp.prEvent_true_eq_one, mul_one]
  have hSim_le :
      (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal ≤
        ELiftE.toReal + xeddsaModLoss q_H := by
    have hdelta_nn : 0 ≤ deltaWide := by
      unfold deltaWide
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_pos (Nat.cast_pos.mpr l25519_pos) (pow_pos zero_lt_two 512)).le
    have hfin2 : ((q_H + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal deltaWide ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have htoReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hELiftE_ne_top, hfin2⟩) hSimE_le
    rw [ENNReal.toReal_add hELiftE_ne_top hfin2, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hdelta_nn] at htoReal
    simpa [xeddsaModLoss, Nat.cast_add, Nat.cast_one] using htoReal
  have hper_u : ∀ᵐ u ∂𝒟[sampleScalar32],
      acc u * (acc u / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹) ≤
        2 * Pr{let ok ← gapU u}[ok = true] := by
    refine (OracleComp.evalDist_ae_mem_support sampleScalar32).mono fun u hu => ?_
    have hu_len : u.length = 32 := length_of_mem_support_sampleScalar32 hu
    have hv_le :
        (2 : ℝ≥0∞)⁻¹ * (acc u * (acc u / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹)) ≤
          Pr{let ok ← gapU u}[ok = true] :=
      le_prEvent_bind_of_forall_le sampleScalar32 (OracleComp.prEvent_true_eq_one _) (gapUV u)
        (· = true) fun v => by
          have hpt := forkGapDhAdv_pointwise_ennreal hWF C hA hu_len v
          dsimp only [gapUV]
          rw [bind_pure_comp, prEvent_map]
          exact hpt
    have hmul2 := mul_le_mul_of_nonneg_left hv_le (zero_le : (0 : ℝ≥0∞) ≤ 2)
    have hcancel : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (two_ne_zero : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top
    rwa [← mul_assoc, hcancel, one_mul] at hmul2
  have hENN_quad :
      ELiftE * (ELiftE / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹) ≤
        2 * 𝒟[gapDhExp P P.isValidDhTriple P.pow8 (forkGapDhAdv P A)] {true} := by
    have hlin := ENNReal.lintegral_mul_div_sub_le (μ := 𝒟[sampleScalar32])
      Measurable.of_discrete.aemeasurable ((q_H + 1 : ℕ) : ℝ≥0∞) (l25519 : ℝ≥0∞)⁻¹
      (Filter.Eventually.of_forall fun _ => prEvent_le_one _) hper_u
    have hrhs :
        (∫⁻ u, 2 * Pr{let ok ← gapU u}[ok = true] ∂𝒟[sampleScalar32]) =
          2 * 𝒟[gapDhExp P P.isValidDhTriple P.pow8 (forkGapDhAdv P A)] {true} := by
      rw [lintegral_const_mul (2 : ℝ≥0∞) Measurable.of_discrete,
        ← prEvent_bind_eq_lintegral_of_discrete sampleScalar32 gapU (· = true),
        prEvent_eq_evalDist_singleton]
      rfl
    exact hlin.trans_eq hrhs
  set ELift : ℝ := ELiftE.toReal
  have hELift_quad :
      ELift * (ELift / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ)) ≤
        2 * GapDH P P.isValidDhTriple P.pow8 (forkGapDhAdv P A) := by
    by_cases hneg : ELift / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ) ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hneg).trans
        (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    · push Not at hneg
      have hQ_pos : 0 < (q_H : ℝ) + 1 := by positivity
      have hL_pos : 0 < (l25519 : ℝ) := Nat.cast_pos.mpr l25519_pos
      have hofReal_acc : ENNReal.ofReal ELift = ELiftE := ENNReal.ofReal_toReal hELiftE_ne_top
      have hofReal_Q : ENNReal.ofReal ((q_H : ℝ) + 1) = ((q_H + 1 : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add, ENNReal.ofReal_natCast]
      have hofReal_invL : ENNReal.ofReal (1 / (l25519 : ℝ)) = (l25519 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos hL_pos, ENNReal.ofReal_natCast]
      have hofReal_lhs :
          ENNReal.ofReal (ELift * (ELift / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ))) =
            ELiftE * (ELiftE / ((q_H + 1 : ℕ) : ℝ≥0∞) - (l25519 : ℝ≥0∞)⁻¹) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, hofReal_acc,
          ENNReal.ofReal_sub _ (div_nonneg zero_le_one hL_pos.le),
          ENNReal.ofReal_div_of_pos hQ_pos, hofReal_acc, hofReal_Q, hofReal_invL]
      have hfin_rhs :
          (2 : ℝ≥0∞) * 𝒟[gapDhExp P P.isValidDhTriple P.pow8 (forkGapDhAdv P A)] {true} ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)
      rw [← hofReal_lhs] at hENN_quad
      have htoReal := ENNReal.toReal_mono hfin_rhs hENN_quad
      rw [ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg hneg.le),
        ENNReal.toReal_mul, ENNReal.toReal_ofNat] at htoReal
      exact htoReal
  have hQ_pos : 0 < (q_H : ℝ) + 1 := by positivity
  set epsSim := max 0
    ((𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal - xeddsaModLoss q_H)
  have heps_le : epsSim ≤ ELift := max_le ENNReal.toReal_nonneg (by linarith)
  have hG_nn : 0 ≤ 2 * GapDH P P.isValidDhTriple P.pow8 (forkGapDhAdv P A) :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  exact quad_le_of_le_of_nonneg_rhs (le_max_left _ _) heps_le hQ_pos hG_nn hELift_quad

theorem gapSigEufCmaRo_forking_quad_of_sim (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (C : XeddsaCurveWitness P)
    {A : GapSigEufCmaRoAdv} (hA : A.Bounded)
    (hSim : GapSigEufCmaRo P P.isValidDhTriple A ≤
      (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal +
        xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) :
    ∃ B₂ : GapDhAdv,
      let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
      let eps' := max 0
        (GapSigEufCmaRo P P.isValidDhTriple A -
          xeddsaSimLoss A.q_sig q_H - xeddsaModLoss q_H)
      B₂.Bounded ∧
      B₂.q_ddh ≤ 2 * A.q_ddh ∧
      B₂.q_prim ≤ 2 * A.q_prim + 1 ∧
      eps' * (eps' / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ)) ≤
        2 * GapDH P P.isValidDhTriple P.pow8 B₂ := by
  obtain ⟨hB_bound, hB_ddh, hB_prim, hSimQuad⟩ := gapSigEufCmaSim_forking_quad P hWF C hA
  refine ⟨forkGapDhAdv P A, hB_bound, hB_ddh, hB_prim, ?_⟩
  set q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
  set eps' := max 0
    (GapSigEufCmaRo P P.isValidDhTriple A - xeddsaSimLoss A.q_sig q_H - xeddsaModLoss q_H)
  set epsSim := max 0
    ((𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal - xeddsaModLoss q_H)
  have heps_le : eps' ≤ epsSim :=
    max_le (le_max_left _ _) ((by linarith : _ ≤
      (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal - xeddsaModLoss q_H).trans
      (le_max_right _ _))
  have hQ_pos : 0 < (q_H : ℝ) + 1 := by positivity
  have hG_nn : 0 ≤ 2 * GapDH P P.isValidDhTriple P.pow8 (forkGapDhAdv P A) :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  exact quad_le_of_le_of_nonneg_rhs (le_max_left _ _) heps_le hQ_pos hG_nn hSimQuad

theorem gapSigEufCmaRoBoundQuad_of_sim
    (hSim : ∀ (P : Primitives), WellFormedPrimitivesδ P →
      ∀ (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv), A.Bounded →
        GapSigEufCmaRo P P.isValidDhTriple A ≤
          (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal +
            xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) :
    GapSigEufCmaRoBoundQuad := by
  intro P hWF ⟨C⟩ A hA
  exact gapSigEufCmaRo_forking_quad_of_sim P hWF C hA (hSim P hWF C A hA)

theorem gapSigEufCmaRoBound_of_sim
    (hSim : ∀ (P : Primitives), WellFormedPrimitivesδ P →
      ∀ (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv), A.Bounded →
        GapSigEufCmaRo P P.isValidDhTriple A ≤
          (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal +
            xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) :
    GapSigEufCmaRoBound :=
  gapSigEufCmaRoBound_of_quad (gapSigEufCmaRoBoundQuad_of_sim hSim)

/-- Quadratic forking-lemma bound reducing `GapSigEufCmaRo` to standalone `GapDH`. -/
theorem gapSigEufCmaRoBoundQuad_holds : GapSigEufCmaRoBoundQuad :=
  gapSigEufCmaRoBoundQuad_of_sim gapSigEufCmaRo_le_sim

/-- Closed-form square-root forking-lemma bound reducing `GapSigEufCmaRo` to standalone `GapDH`. -/
theorem gapSigEufCmaRoBound_holds : GapSigEufCmaRoBound :=
  gapSigEufCmaRoBound_of_sim gapSigEufCmaRo_le_sim

end MainReduction

end Computational.Proofs.SignalPqxdh.XeddsaRom.ForkingReduction
