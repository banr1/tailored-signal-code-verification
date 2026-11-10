/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
import Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.MeasureTVDist.Basic
import VCVio.EvalDist.MeasureTVDist.Bind
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
import VCVio.ProgramLogic.Relational.SimulateQ.StateDependent

/-!
# HVZK simulation and SHA-512 random-oracle programming for XEdDSA

**Checked by Lean.** Proves the three-hop HVZK signing simulation bound (`xeddsaSimLoss`) in the
SHA-512 random-oracle model for `GapDhWithSignRo` and `GapSigEufCmaRo`: hedged-nonce `H_1`
decoupling, wide modular reduction (`deltaWide`), and Schnorr HVZK random-oracle programming.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim

open scoped MeasureTheory ENNReal
open MeasureTheory (
  Measure IsProbabilityMeasure measure_univ
  lintegral_add_right lintegral_congr lintegral_const lintegral_indicator_one lintegral_mono
)
open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery
open _root_.SignalPqxdh (
  Bytes Primitives PrimQuery primSpec PrimBaseSpec
  DdhQuery gapDhOracleSpec SigQuery sigOracleSpec sigAndDdhSpec
  WellFormedPrimitivesδ
  clampScalar25519 fitBytesRef fitBytesRef_length
  word256ToBytes sampleBytes32 sampleScalar32 sampleRandom64
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 l25519_pos natOfBytesLE bytesOfNatLE
  bytesOfNatLE_length natOfBytesLE_append natOfBytesLE_bytesOfNatLE bytesOfNatLE_natOfBytesLE
  encodeScalarBytes decodeScalarBytes encodeScalarBytes_length decodeScalarBytes_encodeScalarBytes
  encodeScalarBytes_byte31_lt_32
  xeddsaHashPrefix xeddsaHashPrefix_length clearSignBit32
  scalarIsInRange_clearSignBit32_xeddsaHashPrefix append_ne_xeddsaHashPrefix_append
  clampScalar25519_length clampedScalarZMod
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  edDummy edBaseMul
  sha512RoSpec sha512RoBaseImpl Sha512RoComp sha512RoImpl
  xeddsaSignRo xeddsaVerifyRo primRoStep primRoImpl primBaseRoImpl
  XeddsaRomOracleSpec
  isRomPrimQuery isRomPrimVerifyQuery isRomPrimSigSignQuery
  isRomDirectRoQuery isRomSigChalQuery isRomDdhChalQuery
  GapDhWithSignRoAdv GapDhWithSignRo gapDhWithSignRoExp
  GapSigEufCmaRoAdv GapSigEufCmaRo gapSigEufCmaRoExp
  XeddsaCurveWitness
  wideRem deltaWide xeddsaChalBudget xeddsaSimLoss
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip (
  compress_edBaseMul xeddsaSignFromDigests
)

/-! ## Simulated-signing oracle and ROM game variants -/

/-- Simulated XEdDSA signing in `Sha512RoComp` given public key `pk` and candidate Edwards sign bit
    `bSim` without the secret scalar, programming uncached challenge entries into the random-oracle
    cache. -/
noncomputable def xeddsaSimSign (P : Primitives) (pk : Bytes) (bSim : UInt8) (m : Bytes) :
    Sha512RoComp Bytes := do
  let edPk := (P.montToEd pk bSim).getD (edDummy P)
  let capA := P.compress edPk
  let minusCapA := P.edNeg edPk
  let sVal ← liftM (m := ProbComp) ($ᵗ (ZMod l25519))
  let hDigest ← liftM (m := ProbComp) sampleRandom64
  let h := P.scalarFromWide hDigest
  let s := encodeScalarBytes sVal
  let capR := P.compress (P.doubleScalarMulBasepoint h minusCapA s)
  let signBitByte : UInt8 := (bSim &&& 1) <<< 7
  modify fun cache =>
    match cache (capR ++ capA ++ m) with
    | some _ => cache
    | none   => cache.cacheQuery (capR ++ capA ++ m) hDigest
  return (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte])

noncomputable def gapDhWithSignRoExpAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (u v : Bytes) (A : GapDhWithSignRoAdv) : ProbComp Bool := do
  let U := P.x25519Base u
  let V := P.x25519Base v
  let sigImpl : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) => do
    let r ← liftM (m := ProbComp) sampleRandom64
    simulateQ sha512RoImpl (xeddsaSignRo P u m r)
  let ddhImpl : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let Z ← (simulateQ (primBaseRoImpl P + (sigImpl + ddhImpl)) (A.run U V)).run' ∅
  return (pow8 Z == pow8 (P.x25519 u V))

/-- Simulated candidate-output computation of `A` on public keys `(U, V)` and candidate sign bit
    `bSim` without `u` or `v`. -/
noncomputable def gapDhWithSignSimRun (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (U V : Bytes) (bSim : UInt8) (A : GapDhWithSignRoAdv) : ProbComp Bytes :=
  let sigImpl : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) =>
    xeddsaSimSign P U bSim m
  let ddhImpl : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  (simulateQ (primBaseRoImpl P + (sigImpl + ddhImpl)) (A.run U V)).run' ∅

noncomputable def gapDhWithSignSimExpAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (u v : Bytes) (bSim : UInt8) (A : GapDhWithSignRoAdv) : ProbComp Bool := do
  let Z ← gapDhWithSignSimRun P isValidDhTriple (P.x25519Base u) (P.x25519Base v) bSim A
  return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))

/-- Simulated `GapDhWithSignRo` experiment using the Edwards sign bit `C.edSign (clampedScalarZMod u)`. -/
noncomputable def gapDhWithSignSimExp (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignRoAdv) : ProbComp Bool := do
  let u ← sampleScalar32
  let v ← sampleScalar32
  gapDhWithSignSimExpAt P isValidDhTriple pow8 u v (C.edSign (clampedScalarZMod u)) A

noncomputable def gapSigEufCmaRoExpAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (A : GapSigEufCmaRoAdv) : ProbComp Bool := do
  let pk := P.sigPkGen sk
  let sigImpl : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp) :=
    fun (.sign m) => do
      let r ← liftM (m := ProbComp) sampleRandom64
      let sig ← liftM (m := Sha512RoComp) (simulateQ sha512RoImpl (xeddsaSignRo P sk m r))
      modify (m :: ·)
      return sig
  let ddhImpl : QueryImpl gapDhOracleSpec (StateT (List Bytes) Sha512RoComp) :=
    fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
  let fullImpl :=
    (primBaseRoImpl P).liftTarget (StateT (List Bytes) Sha512RoComp) + (sigImpl + ddhImpl)
  let checkInRo : Sha512RoComp Bool := do
    let ((mStar, sigStar), signedMsgs) ← (simulateQ fullImpl (A.run pk)).run []
    let ok ← simulateQ sha512RoImpl (xeddsaVerifyRo P pk mStar sigStar)
    return (ok && decide (mStar ∉ signedMsgs))
  checkInRo.run' ∅

/-- Simulated EUF-CMA ROM experiment parameterized by public key `pk` and candidate sign bit `bSim`
    without `sk`. -/
noncomputable def gapSigEufCmaSimExpOnPk (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) : ProbComp Bool := do
  let sigImpl : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp) :=
    fun (.sign m) => do
      let sig ← liftM (m := Sha512RoComp) (xeddsaSimSign P pk bSim m)
      modify (m :: ·)
      return sig
  let ddhImpl : QueryImpl gapDhOracleSpec (StateT (List Bytes) Sha512RoComp) :=
    fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
  let fullImpl :=
    (primBaseRoImpl P).liftTarget (StateT (List Bytes) Sha512RoComp) + (sigImpl + ddhImpl)
  let checkInRo : Sha512RoComp Bool := do
    let ((mStar, sigStar), signedMsgs) ← (simulateQ fullImpl (A.run pk)).run []
    let ok ← simulateQ sha512RoImpl (xeddsaVerifyRo P pk mStar sigStar)
    return (ok && decide (mStar ∉ signedMsgs))
  checkInRo.run' ∅

noncomputable abbrev gapSigEufCmaSimExpAt (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (bSim : UInt8) (A : GapSigEufCmaRoAdv) : ProbComp Bool :=
  gapSigEufCmaSimExpOnPk P isValidDhTriple (P.x25519Base sk) bSim A

/-- Simulated EUF-CMA ROM experiment using the Edwards sign bit `C.edSign (clampedScalarZMod sk)`. -/
noncomputable def gapSigEufCmaSimExp (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (A : GapSigEufCmaRoAdv) : ProbComp Bool := do
  let sk ← sampleScalar32
  gapSigEufCmaSimExpAt P isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A

/-! ## Uniform characterization of `sampleRandom64` and `deltaWide` TV bound -/

private theorem two_pow_256_mul_self : 2 ^ 256 * 2 ^ 256 = 2 ^ 512 := by
  rw [← pow_add]

private theorem word256ToBytes_length (w : BitVec 256) : (word256ToBytes w).length = 32 := by
  simp [word256ToBytes]

private theorem word256ToBytes_eq_bytesOfNatLE (w : BitVec 256) :
    word256ToBytes w = bytesOfNatLE 32 w.toNat := by
  apply List.ext_getElem
  · rw [word256ToBytes_length, bytesOfNatLE_length]
  · intro i hi1 hi2
    apply UInt8.toNat_inj.mp
    have hL : (word256ToBytes w)[i].toNat = (w.toNat / 256 ^ i) % 256 := by
      simp only [word256ToBytes, List.getElem_ofFn, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (8 * i) = 256 ^ i := by rw [Nat.pow_mul]
      rw [hpow, UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide))]
    have hR : (bytesOfNatLE 32 w.toNat)[i].toNat = (w.toNat / 256 ^ i) % 256 := by
      have hgetD : (bytesOfNatLE 32 w.toNat)[i] = (bytesOfNatLE 32 w.toNat).getD i 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
        rfl
      rw [hgetD, Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519.getD_toNat_eq_div_mod,
        natOfBytesLE_bytesOfNatLE]
      have hw : w.toNat < 256 ^ 32 := by
        have hlt := w.isLt
        have h256 : (2 : ℕ) ^ 256 = 256 ^ 32 := by
          show 2 ^ (8 * 32) = (2 ^ 8) ^ 32
          rw [pow_mul]
        omega
      rw [Nat.mod_eq_of_lt hw]
    exact hL.trans hR.symm

private theorem append_word256ToBytes_eq_bytesOfNatLE (w1 w2 : BitVec 256) :
    word256ToBytes w1 ++ word256ToBytes w2 = bytesOfNatLE 64 (w1.toNat + 2 ^ 256 * w2.toNat) := by
  have hlen : (word256ToBytes w1 ++ word256ToBytes w2).length = 64 := by
    simp [word256ToBytes_length]
  conv_lhs => rw [← bytesOfNatLE_natOfBytesLE (word256ToBytes w1 ++ word256ToBytes w2), hlen]
  rw [natOfBytesLE_append, word256ToBytes_length, word256ToBytes_eq_bytesOfNatLE w1,
    word256ToBytes_eq_bytesOfNatLE w2, natOfBytesLE_bytesOfNatLE, natOfBytesLE_bytesOfNatLE]
  have h256 : (256 : ℕ) ^ 32 = 2 ^ 256 := by
    show (2 ^ 8) ^ 32 = 2 ^ (8 * 32)
    rw [← pow_mul]
  rw [h256, Nat.mod_eq_of_lt w1.isLt, Nat.mod_eq_of_lt w2.isLt]

private def bitVecPairEquivFinMul (n : ℕ) : (BitVec n × BitVec n) ≃ Fin (2 ^ n * 2 ^ n) where
  toFun p := ⟨p.1.toNat + 2 ^ n * p.2.toNat, by
    have h1 : p.1.toNat < 2 ^ n := p.1.isLt
    have h2 : p.2.toNat + 1 ≤ 2 ^ n := p.2.isLt
    calc p.1.toNat + 2 ^ n * p.2.toNat
        < 2 ^ n + 2 ^ n * p.2.toNat := by omega
      _ = 2 ^ n * (p.2.toNat + 1) := by ring
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left (2 ^ n) h2⟩
  invFun k := (BitVec.ofNat n (k.val % 2 ^ n), BitVec.ofNat n (k.val / 2 ^ n))
  left_inv := fun ⟨w1, w2⟩ => by
    have h1 := w1.isLt
    have hpos : 0 < (2 : ℕ) ^ n := by positivity
    have hmod : (w1.toNat + 2 ^ n * w2.toNat) % 2 ^ n = w1.toNat := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    have hdiv : (w1.toNat + 2 ^ n * w2.toNat) / 2 ^ n = w2.toNat := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt h1, Nat.zero_add]
    refine Prod.ext (BitVec.eq_of_toNat_eq ?_) (BitVec.eq_of_toNat_eq ?_)
    · simp only [BitVec.toNat_ofNat, hmod, Nat.mod_eq_of_lt w1.isLt]
    · simp only [BitVec.toNat_ofNat, hdiv, Nat.mod_eq_of_lt w2.isLt]
  right_inv k := by
    ext
    simp only [BitVec.toNat_ofNat]
    have hmod2 : k.val % 2 ^ n % 2 ^ n = k.val % 2 ^ n :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))
    have hdiv_lt : k.val / 2 ^ n < 2 ^ n := Nat.div_lt_of_lt_mul k.isLt
    rw [hmod2, Nat.mod_eq_of_lt hdiv_lt, Nat.mod_add_div]

private theorem sampleRandom64_length {bs : Bytes} (h : bs ∈ support sampleRandom64) :
    bs.length = 64 := by
  unfold sampleRandom64 sampleBytes32 at h
  simp only [support_bind, support_map, support_pure, Set.mem_iUnion, Set.mem_image,
    Set.mem_singleton_iff] at h
  rcases h with ⟨b1, ⟨w1, _, rfl⟩, b2, ⟨w2, _, rfl⟩, rfl⟩
  simp [word256ToBytes_length]

private theorem sampleRandom64_eq_bind_bitVec :
    sampleRandom64 =
      (do
        let w1 ← $ᵗ BitVec 256
        let w2 ← $ᵗ BitVec 256
        pure (bytesOfNatLE 64 ((bitVecPairEquivFinMul 256 (w1, w2)).val))) := by
  unfold sampleRandom64 sampleBytes32
  rw [bind_map_left]
  congr 1
  funext w1
  rw [bind_map_left]
  congr 1
  funext w2
  rw [append_word256ToBytes_eq_bytesOfNatLE]
  rfl

private theorem sampleRandom64_evalDistEq_fin :
    sampleRandom64 =ᵈ
      ((fun k : Fin (2 ^ 256 * 2 ^ 256) => bytesOfNatLE 64 k.val) <$>
        ($ᵗ Fin (2 ^ 256 * 2 ^ 256))) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace Bytes := ⊤
  refine Measure.ext fun A _ => ?_
  change 𝒟[sampleRandom64] {x | x ∈ A} =
    𝒟[(fun k : Fin (2 ^ 256 * 2 ^ 256) => bytesOfNatLE 64 k.val) <$>
      ($ᵗ Fin (2 ^ 256 * 2 ^ 256))] {x | x ∈ A}
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  have hbij : Function.Bijective
      (Function.uncurry fun (w1 w2 : BitVec 256) => bitVecPairEquivFinMul 256 (w1, w2)) :=
    (bitVecPairEquivFinMul 256).bijective
  rw [← SampleableType.prEvent_uniformSample_pair_of_bijective hbij
    (fun k : Fin (2 ^ 256 * 2 ^ 256) => bytesOfNatLE 64 k.val ∈ A)]
  rw [sampleRandom64_eq_bind_bitVec]
  simp only [prEvent_norm]

private theorem two56_pow_64_eq : (256 : ℕ) ^ 64 = 2 ^ 256 * 2 ^ 256 := by
  calc (256 : ℕ) ^ 64 = (2 ^ 8) ^ (32 + 32) := rfl
    _ = (2 ^ 8) ^ 32 * (2 ^ 8) ^ 32 := pow_add _ 32 32
    _ = 2 ^ 256 * 2 ^ 256 := by rw [← pow_mul]

private theorem bytesOfNatLE_64_fin_injective :
    Function.Injective (fun k : Fin (2 ^ 256 * 2 ^ 256) => bytesOfNatLE 64 k.val) := by
  intro k1 k2 h
  have hnat := congrArg natOfBytesLE h
  rw [natOfBytesLE_bytesOfNatLE, natOfBytesLE_bytesOfNatLE, two56_pow_64_eq,
    Nat.mod_eq_of_lt k1.isLt, Nat.mod_eq_of_lt k2.isLt] at hnat
  exact Fin.ext hnat

private theorem prEvent_sampleRandom64_inj_eq_le {α : Type} {f : Bytes → α}
    (hf : ∀ r1 r2 : Bytes, r1.length = 64 → r2.length = 64 → f r1 = f r2 → r1 = r2)
    (y : α) :
    Pr{let r ← sampleRandom64}[f r = y] ≤ ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [sampleRandom64_evalDistEq_fin.prEvent_eq, prEvent_map,
    SampleableType.prEvent_uniformSample, Fintype.card_fin]
  have hcard : (Finset.univ.filter
      (fun k : Fin (2 ^ 256 * 2 ^ 256) => f (bytesOfNatLE 64 k.val) = y)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact bytesOfNatLE_64_fin_injective
      (hf _ _ (bytesOfNatLE_length 64 a.val) (bytesOfNatLE_length 64 b.val) (ha.trans hb.symm))
  calc ((Finset.univ.filter
        (fun k : Fin (2 ^ 256 * 2 ^ 256) => f (bytesOfNatLE 64 k.val) = y)).card : ℝ≥0∞) /
          ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)
      ≤ 1 / ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞) := by gcongr; exact_mod_cast hcard
    _ = ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := one_div _

private theorem card_fin_mod_fiber_lt {M L : ℕ} [NeZero L]
    (z : ZMod L) (hz : z.val < M % L) :
    (Finset.univ.filter (fun k : Fin M => (k.val : ZMod L) = z)).card = M / L + 1 := by
  classical
  have hL_pos : 0 < L := NeZero.pos L
  set Q := M / L
  have hdiv : L * Q + M % L = M := Nat.div_add_mod M L
  symm
  rw [← Finset.card_fin (Q + 1)]
  refine Finset.card_bij (fun (q : Fin (Q + 1)) _ =>
    ⟨L * q.val + z.val, by
      have hq : q.val ≤ Q := Nat.lt_succ_iff.mp q.isLt
      have hmul : L * q.val ≤ L * Q := Nat.mul_le_mul_left L hq
      omega⟩) ?_ ?_ ?_
  · intro q _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]
  · intro q1 _ q2 _ heq
    have hval := congrArg Fin.val heq
    dsimp only at hval
    have hmul : L * q1.val = L * q2.val := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hL_pos hmul)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hmod : k.val % L = z.val := by
      have hv := congrArg ZMod.val hk
      rwa [ZMod.val_natCast] at hv
    have hdecomp : L * (k.val / L) + z.val = k.val := by
      rw [← hmod]; exact Nat.div_add_mod k.val L
    have hq_lt : k.val / L < Q + 1 := by
      by_contra hge
      have hge' : Q + 1 ≤ k.val / L := by omega
      have hmul : L * (Q + 1) ≤ L * (k.val / L) := Nat.mul_le_mul_left L hge'
      have hrem : M % L < L := Nat.mod_lt M hL_pos
      have hk_lt := k.isLt
      nlinarith
    exact ⟨⟨k.val / L, hq_lt⟩, Finset.mem_univ _, Fin.ext hdecomp⟩

private theorem card_fin_mod_fiber_ge {M L : ℕ} [NeZero L]
    (z : ZMod L) (hz : ¬ z.val < M % L) :
    (Finset.univ.filter (fun k : Fin M => (k.val : ZMod L) = z)).card = M / L := by
  classical
  have hL_pos : 0 < L := NeZero.pos L
  set Q := M / L
  have hdiv : L * Q + M % L = M := Nat.div_add_mod M L
  symm
  rw [← Finset.card_fin Q]
  refine Finset.card_bij (fun (q : Fin Q) _ =>
    ⟨L * q.val + z.val, by
      have hq : q.val + 1 ≤ Q := q.isLt
      have hmul : L * q.val + L ≤ L * Q := by
        simpa [mul_add] using Nat.mul_le_mul_left L hq
      have hz_lt : z.val < L := z.val_lt
      omega⟩) ?_ ?_ ?_
  · intro q _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]
  · intro q1 _ q2 _ heq
    have hval := congrArg Fin.val heq
    dsimp only at hval
    have hmul : L * q1.val = L * q2.val := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hL_pos hmul)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hmod : k.val % L = z.val := by
      have hv := congrArg ZMod.val hk
      rwa [ZMod.val_natCast] at hv
    have hdecomp : L * (k.val / L) + z.val = k.val := by
      rw [← hmod]; exact Nat.div_add_mod k.val L
    have hq_lt : k.val / L < Q := by
      by_contra hge
      have hge' : Q ≤ k.val / L := by omega
      have hmul : L * Q ≤ L * (k.val / L) := Nat.mul_le_mul_left L hge'
      have hk_lt := k.isLt
      omega
    exact ⟨⟨k.val / L, hq_lt⟩, Finset.mem_univ _, Fin.ext hdecomp⟩

private theorem measureETVDist_fin_mod_zmod (M L : ℕ) [NeZero M] [NeZero L] :
    letI : MeasurableSpace (ZMod L) := ⊤
    measureETVDist (((fun k : Fin M => (k.val : ZMod L)) <$> ($ᵗ Fin M))) ($ᵗ (ZMod L)) ≤
      ENNReal.ofReal (((M % L : ℕ) : ℝ) * ((L - M % L : ℕ) : ℝ) / ((L : ℝ) * (M : ℝ))) := by
  classical
  let : MeasurableSpace (ZMod L) := ⊤
  have hM_pos_nat : 0 < M := NeZero.pos M
  have hL_pos_nat : 0 < L := NeZero.pos L
  refine iSup_le fun (Sm : {S : Set (ZMod L) // MeasurableSet S}) => ?_
  set S : Set (ZMod L) := Sm.1
  let pM : Fin M → Prop := fun k => (k.val : ZMod L) ∈ S
  let pL : ZMod L → Prop := fun z => z ∈ S
  have hmap_eq : 𝒟[(fun k : Fin M => (k.val : ZMod L)) <$> ($ᵗ Fin M)] S =
      ENNReal.ofReal ((Finset.univ.filter pM).card / (M : ℝ)) := by
    change 𝒟[(fun k : Fin M => (k.val : ZMod L)) <$> ($ᵗ Fin M)] {z | z ∈ S} = _
    rw [← prEvent_eq_evalDist_of_discrete, prEvent_map]
    simpa only [pM, Fintype.card_fin, Nat.cast_id] using
      SampleableType.prEvent_uniformSample_eq_ofReal pM
  have hunif_eq : 𝒟[$ᵗ (ZMod L)] S =
      ENNReal.ofReal ((Finset.univ.filter pL).card / (L : ℝ)) := by
    change 𝒟[$ᵗ (ZMod L)] {z | z ∈ S} = _
    rw [← prEvent_eq_evalDist_of_discrete]
    simpa only [pL, ZMod.card] using
      SampleableType.prEvent_uniformSample_eq_ofReal pL
  rw [hmap_eq, hunif_eq]
  set F : Finset (ZMod L) := Finset.univ.filter pL
  set R : ℕ := M % L
  set F_lo : Finset (ZMod L) := F.filter (fun z => z.val < R)
  set F_hi : Finset (ZMod L) := F.filter (fun z => ¬ z.val < R)
  set a : ℕ := F_lo.card
  set b : ℕ := F_hi.card
  have hsplit : F = F_lo ∪ F_hi := by
    ext z
    simp only [F_lo, F_hi, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj : Disjoint F_lo F_hi := by
    refine Finset.disjoint_left.mpr fun z h1 h2 => ?_
    simp only [F_lo, F_hi, Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hF_card : F.card = a + b := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have ha_le : a ≤ R := by
    calc F_lo.card
        ≤ (Finset.range R).card := by
          refine Finset.card_le_card_of_injOn ZMod.val
            (fun z hz => by
              simp only [F_lo, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hz ⊢
              exact hz.2)
            (fun _ _ _ _ heq => ZMod.val_injective L heq)
      _ = R := Finset.card_range R
  have hrem_lt : R < L := Nat.mod_lt M hL_pos_nat
  have hb_le : b ≤ L - R := by
    calc F_hi.card
        ≤ (Finset.range (L - R)).card := by
          refine Finset.card_le_card_of_injOn (fun z => z.val - R)
            (fun z hz => by
              simp only [F_hi, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hz ⊢
              have := z.val_lt
              omega)
            (fun z1 hz1 z2 hz2 heq => by
              dsimp only at heq
              simp only [F_hi, Finset.mem_coe, Finset.mem_filter] at hz1 hz2
              exact ZMod.val_injective L (by omega))
      _ = L - R := Finset.card_range _
  set Q := M / L
  have hM_card : (Finset.univ.filter pM).card = (a + b) * Q + a := by
    have hbiUnion : Finset.univ.filter pM =
        F.biUnion (fun z => Finset.univ.filter (fun k : Fin M => (k.val : ZMod L) = z)) := by
      ext k
      simp [F, pM, pL]
    rw [hbiUnion, Finset.card_biUnion (fun z1 _ z2 _ hne => Finset.disjoint_left.mpr fun k hk1 hk2 => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
      exact hne (hk1.symm.trans hk2))]
    rw [hsplit, Finset.sum_union hdisj]
    have hsum_lo : ∑ z ∈ F_lo,
        (Finset.univ.filter (fun k : Fin M => (k.val : ZMod L) = z)).card =
          a * (Q + 1) := by
      calc ∑ z ∈ F_lo, _ = ∑ _z ∈ F_lo, (Q + 1) := by
            refine Finset.sum_congr rfl fun z hz => ?_
            simp only [F_lo, Finset.mem_filter] at hz
            exact card_fin_mod_fiber_lt z hz.2
        _ = a * (Q + 1) := by simp [a]
    have hsum_hi : ∑ z ∈ F_hi,
        (Finset.univ.filter (fun k : Fin M => (k.val : ZMod L) = z)).card =
          b * Q := by
      calc ∑ z ∈ F_hi, _ = ∑ _z ∈ F_hi, Q := by
            refine Finset.sum_congr rfl fun z hz => ?_
            simp only [F_hi, Finset.mem_filter] at hz
            exact card_fin_mod_fiber_ge z hz.2
        _ = b * Q := by simp [b]
    rw [hsum_lo, hsum_hi]
    ring
  rw [hM_card, hF_card]
  set x : ℝ := (((a + b) * Q + a : ℕ) : ℝ) / (M : ℝ)
  set y : ℝ := ((a + b : ℕ) : ℝ) / (L : ℝ)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos_nat
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos_nat
  have hx_nonneg : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hM_pos.le
  have hy_nonneg : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) hL_pos.le
  have habs_le : |x - y| ≤ ((R : ℝ) * ((L - R : ℕ) : ℝ)) / ((L : ℝ) * (M : ℝ)) := by
    have hdiv_nat : L * Q + R = M := Nat.div_add_mod M L
    have hdiv_real : (L : ℝ) * (Q : ℝ) + (R : ℝ) = (M : ℝ) := by exact_mod_cast hdiv_nat
    have hsub_real : ((L - R : ℕ) : ℝ) = (L : ℝ) - (R : ℝ) := Nat.cast_sub (le_of_lt hrem_lt)
    have ha_real : (a : ℝ) ≤ (R : ℝ) := by exact_mod_cast ha_le
    have hb_real : (b : ℝ) ≤ ((L - R : ℕ) : ℝ) := by exact_mod_cast hb_le
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hr0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have hlr0 : (0 : ℝ) ≤ ((L - R : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnum_cast : (((a + b) * Q + a : ℕ) : ℝ) = ((a : ℝ) + (b : ℝ)) * (Q : ℝ) + (a : ℝ) := by
      push_cast; ring
    have hab_cast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; rfl
    have hdiff : x - y =
        ((a : ℝ) * ((L - R : ℕ) : ℝ) - (b : ℝ) * (R : ℝ)) / ((L : ℝ) * (M : ℝ)) := by
      dsimp only [x, y]
      rw [hnum_cast, hab_cast, hsub_real]
      field_simp [hL_pos.ne', hM_pos.ne']
      nlinarith [hdiv_real]
    rw [hdiff, abs_div, abs_of_pos (mul_pos hL_pos hM_pos)]
    gcongr
    rw [abs_le]
    constructor <;> nlinarith
  rcases le_total x y with hxy | hyx
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hxy), zero_add,
      ← ENNReal.ofReal_sub y hx_nonneg]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by rwa [abs_sub_comm]))
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hyx), add_zero,
      ← ENNReal.ofReal_sub x hy_nonneg]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans habs_le)

private theorem measureETVDist_decode_sampleRandom64_zmod :
    letI : MeasurableSpace (ZMod l25519) := ⊤
    measureETVDist (decodeScalarBytes <$> sampleRandom64) ($ᵗ (ZMod l25519)) ≤
      ENNReal.ofReal deltaWide := by
  let : MeasurableSpace (ZMod l25519) := ⊤
  have heq : 𝒟[decodeScalarBytes <$> sampleRandom64] =
      𝒟[(fun k : Fin (2 ^ 256 * 2 ^ 256) => (k.val : ZMod l25519)) <$>
        ($ᵗ Fin (2 ^ 256 * 2 ^ 256))] := by
    let : MeasurableSpace Bytes := ⊤
    let : MeasurableSpace (Fin (2 ^ 256 * 2 ^ 256)) := ⊤
    rw [evalDist_map_of_discrete, sampleRandom64_evalDistEq_fin.evalDist_eq,
      evalDist_map_of_discrete, Measure.map_map Measurable.of_discrete Measurable.of_discrete,
      evalDist_map_of_discrete, SampleableType.evalDist_uniformSample]
    have hfun : (decodeScalarBytes ∘ fun k : Fin (2 ^ 256 * 2 ^ 256) => bytesOfNatLE 64 k.val) =
        (fun k : Fin (2 ^ 256 * 2 ^ 256) => (k.val : ZMod l25519)) := by
      funext k
      simp only [Function.comp_apply, decodeScalarBytes, natOfBytesLE_bytesOfNatLE,
        two56_pow_64_eq, Nat.mod_eq_of_lt k.isLt]
    rw [hfun]
  calc measureETVDist (decodeScalarBytes <$> sampleRandom64) ($ᵗ (ZMod l25519))
      = Measure.etvDist 𝒟[decodeScalarBytes <$> sampleRandom64] 𝒟[$ᵗ (ZMod l25519)] := rfl
    _ = Measure.etvDist
          𝒟[(fun k : Fin (2 ^ 256 * 2 ^ 256) => (k.val : ZMod l25519)) <$>
            ($ᵗ Fin (2 ^ 256 * 2 ^ 256))]
          𝒟[$ᵗ (ZMod l25519)] := by rw [heq]
    _ = measureETVDist
          ((fun k : Fin (2 ^ 256 * 2 ^ 256) => (k.val : ZMod l25519)) <$>
            ($ᵗ Fin (2 ^ 256 * 2 ^ 256)))
          ($ᵗ (ZMod l25519)) := rfl
    _ ≤ ENNReal.ofReal
          ((((2 ^ 256 * 2 ^ 256) % l25519 : ℕ) : ℝ) *
            ((l25519 - (2 ^ 256 * 2 ^ 256) % l25519 : ℕ) : ℝ) /
            ((l25519 : ℝ) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ))) :=
        measureETVDist_fin_mod_zmod (2 ^ 256 * 2 ^ 256) l25519
    _ = ENNReal.ofReal deltaWide := by
        congr 1
        unfold deltaWide wideRem
        rw [two_pow_256_mul_self, Nat.cast_pow, Nat.cast_ofNat]

/-! ## Query-budget combinators and non-`H_1` cache projection -/

private theorem fitBytesRef_of_length_eq {n : ℕ} {bs : Bytes} (h : bs.length = n) :
    fitBytesRef n bs = bs := by
  simp [fitBytesRef, h]

private theorem isQueryBoundP_or_of_disjoint {ι α : Type} {spec : OracleSpec ι}
    {oa : OracleComp spec α} {p₁ p₂ : ι → Prop} [DecidablePred p₁] [DecidablePred p₂]
    (hdisj : ∀ t, ¬ (p₁ t ∧ p₂ t)) {n₁ n₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBoundP (fun t => p₁ t ∨ p₂ t) (n₁ + n₂) := by
  refine OracleComp.IsQueryBoundP.proj (fun b : ℕ × ℕ => b.1 + b.2) ?_ ?_
    (h₁.and_isQueryBound_pair h₂)
  · intro t b hcan hp
    rcases hp with hp1 | hp2
    · have := hcan.1.resolve_left (not_not.mpr hp1); omega
    · have := hcan.2.resolve_left (not_not.mpr hp2); omega
  · intro t b hcan
    by_cases hp1 : p₁ t
    · have hp2 : ¬ p₂ t := fun h => hdisj t ⟨hp1, h⟩
      have hb1 : 0 < b.1 := hcan.1.resolve_left (not_not.mpr hp1)
      simp only [hp1, hp2, true_or, ↓reduceIte]
      omega
    · by_cases hp2 : p₂ t
      · have hb2 : 0 < b.2 := hcan.2.resolve_left (not_not.mpr hp2)
        simp only [hp1, hp2, or_true, ↓reduceIte]
        omega
      · simp [hp1, hp2]

private def isRomGrowthQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool :=
  fun q => isRomDirectRoQuery q || isRomPrimVerifyQuery q || isRomPrimSigSignQuery q

private theorem isQueryBoundP_growth_of_bounds {α : Type}
    {oa : OracleComp XeddsaRomOracleSpec α} {q_ro q_verify q_prim_sigSign : ℕ}
    (h_ro : oa.IsQueryBoundP (fun q => isRomDirectRoQuery q = true) q_ro)
    (h_ver : oa.IsQueryBoundP (fun q => isRomPrimVerifyQuery q = true) q_verify)
    (h_psig : oa.IsQueryBoundP (fun q => isRomPrimSigSignQuery q = true) q_prim_sigSign) :
    oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true)
      (xeddsaChalBudget q_ro q_verify q_prim_sigSign) := by
  have h12 : oa.IsQueryBoundP
      (fun q => isRomDirectRoQuery q = true ∨ isRomPrimVerifyQuery q = true)
      (q_ro + q_verify) := by
    refine isQueryBoundP_or_of_disjoint ?_ h_ro h_ver
    rintro (((n | pq) | bs) | (sq | dq)) ⟨h1, h2⟩ <;>
      simp [isRomDirectRoQuery, isRomPrimVerifyQuery] at h1 h2
  have h123 : oa.IsQueryBoundP
      (fun q => (isRomDirectRoQuery q = true ∨ isRomPrimVerifyQuery q = true) ∨
        isRomPrimSigSignQuery q = true)
      (q_ro + q_verify + q_prim_sigSign) := by
    refine isQueryBoundP_or_of_disjoint ?_ h12 h_psig
    rintro (((n | pq) | bs) | (sq | dq)) ⟨h1, h2⟩ <;>
      try { simp [isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery] at h1 h2 }
    cases pq <;> simp [isRomDirectRoQuery, isRomPrimVerifyQuery, isRomPrimSigSignQuery] at h1 h2
  exact (OracleComp.isQueryBoundP_congr_pred fun q => by
    simp [isRomGrowthQuery, Bool.or_eq_true]).mpr h123

private def isH1 (t : Bytes) : Bool :=
  t.take 32 == xeddsaHashPrefix

private theorem isH1_xeddsaHashPrefix_append (rest : Bytes) :
    isH1 (xeddsaHashPrefix ++ rest) = true := by
  unfold isH1
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  exact beq_self_eq_true _

private theorem isH1_eq_false_of_inRange {capR rest : Bytes}
    (hlen : capR.length = 32) (hrange : _root_.SignalPqxdh.scalarIsInRange (clearSignBit32 capR) = true) :
    isH1 (capR ++ rest) = false := by
  unfold isH1
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  cases hbeq : (capR == xeddsaHashPrefix)
  · rfl
  · have heq : capR = xeddsaHashPrefix := eq_of_beq hbeq
    subst heq
    rw [scalarIsInRange_clearSignBit32_xeddsaHashPrefix] at hrange
    exact absurd hrange Bool.false_ne_true

private def projNonH1 (c : sha512RoSpec.QueryCache) : sha512RoSpec.QueryCache :=
  QueryCache.ofFn fun t => if isH1 t then none else c t

@[simp]
private theorem projNonH1_apply (c : sha512RoSpec.QueryCache) (t : Bytes) :
    projNonH1 c t = if isH1 t then none else c t := rfl

@[simp]
private theorem projNonH1_empty : projNonH1 ∅ = ∅ := by
  ext t
  simp [projNonH1_apply]

private theorem projNonH1_cacheQuery (c : sha512RoSpec.QueryCache) (t u : Bytes) :
    projNonH1 (c.cacheQuery t u) =
      if isH1 t then projNonH1 c else (projNonH1 c).cacheQuery t u := by
  ext s
  by_cases hst : s = t
  · subst hst
    by_cases ht : isH1 s = true
    · simp [projNonH1_apply, ht]
    · simp [projNonH1_apply, ht]
  · by_cases ht : isH1 t = true
    · simp [projNonH1_apply, ht, QueryCache.cacheQuery_of_ne _ _ hst]
    · simp [projNonH1_apply, ht, QueryCache.cacheQuery_of_ne _ _ hst]

private theorem projNonH1_enncard_cacheQuery_of_isH1 (c : sha512RoSpec.QueryCache)
    {t : Bytes} (ht : isH1 t = true) (u : Bytes) :
    (projNonH1 (c.cacheQuery t u)).enncard = (projNonH1 c).enncard := by
  rw [projNonH1_cacheQuery, ht]
  rfl

private theorem projNonH1_enncard_cacheQuery_le (c : sha512RoSpec.QueryCache) (t u : Bytes) :
    (projNonH1 (c.cacheQuery t u)).enncard ≤ (projNonH1 c).enncard + 1 := by
  rw [projNonH1_cacheQuery]
  split_ifs
  · exact le_self_add
  · exact QueryCache.enncard_cacheQuery_le _ _ _

private def logSigQuery :
    QueryImpl XeddsaRomOracleSpec (StateT (List Bytes) (OracleComp XeddsaRomOracleSpec))
  | .inr (.inl (.sign m)) => StateT.mk fun s =>
      (fun sig => (sig, m :: s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inr (.inl (.sign m)))) :
          OracleComp XeddsaRomOracleSpec Bytes)
  | q => StateT.mk fun s =>
      (fun u => (u, s)) <$>
        (liftM (XeddsaRomOracleSpec.query q) :
          OracleComp XeddsaRomOracleSpec (XeddsaRomOracleSpec.Range q))

@[simp]
private theorem logSigQuery_run_unif (k : ℕ) (s : List Bytes) :
    (logSigQuery (.inl (.inl (.inl k)))).run s =
      (fun u => (u, s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inl (.inl (.inl k)))) :
          OracleComp XeddsaRomOracleSpec (Fin (k + 1))) := rfl

@[simp]
private theorem logSigQuery_run_prim (pq : PrimQuery) (s : List Bytes) :
    (logSigQuery (.inl (.inl (.inr pq)))).run s =
      (fun u => (u, s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inl (.inl (.inr pq)))) :
          OracleComp XeddsaRomOracleSpec (primSpec.Range pq)) := rfl

@[simp]
private theorem logSigQuery_run_ro (bs : Bytes) (s : List Bytes) :
    (logSigQuery (.inl (.inr bs))).run s =
      (fun u => (u, s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inl (.inr bs))) :
          OracleComp XeddsaRomOracleSpec Bytes) := rfl

@[simp]
private theorem logSigQuery_run_sig (m : Bytes) (s : List Bytes) :
    (logSigQuery (.inr (.inl (.sign m)))).run s =
      (fun sig => (sig, m :: s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inr (.inl (.sign m)))) :
          OracleComp XeddsaRomOracleSpec Bytes) := rfl

@[simp]
private theorem logSigQuery_run_ddh (dq : DdhQuery) (s : List Bytes) :
    (logSigQuery (.inr (.inr dq))).run s =
      (fun u => (u, s)) <$>
        (liftM (XeddsaRomOracleSpec.query (.inr (.inr dq))) :
          OracleComp XeddsaRomOracleSpec Bool) := rfl

private theorem isQueryBoundP_logSigQuery {α : Type}
    {p : XeddsaRomOracleSpec.Domain → Prop} [DecidablePred p]
    {oa : OracleComp XeddsaRomOracleSpec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) (msgs : List Bytes) :
    ((simulateQ logSigQuery oa).run msgs).IsQueryBoundP p n := by
  refine h.simulateQ_run_StateT_of_step (fun q s => ?_) msgs
  rcases q with (((k | pq) | bs) | (sq | dq))
  · rw [logSigQuery_run_unif, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [hp]
  · rw [logSigQuery_run_prim, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [hp]
  · rw [logSigQuery_run_ro, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [hp]
  · rcases sq with ⟨m⟩
    rw [logSigQuery_run_sig, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [hp]
  · rw [logSigQuery_run_ddh, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro hp; simp [hp]

private theorem simulateQ_stateSig_eq_logSigQuery {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sigHandler : QueryImpl sigOracleSpec Sha512RoComp)
    (oa : OracleComp XeddsaRomOracleSpec α) (msgs : List Bytes) :
    let sigImplState : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp) :=
      fun (.sign m) => do
        let sig ← liftM (m := Sha512RoComp) (sigHandler (.sign m))
        modify (m :: ·)
        return sig
    let ddhImplState : QueryImpl gapDhOracleSpec (StateT (List Bytes) Sha512RoComp) :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    let ddhImplBase : QueryImpl gapDhOracleSpec Sha512RoComp :=
      fun (X, Y, Z) => pure (isValidDhTriple X Y Z)
    (simulateQ ((primBaseRoImpl P).liftTarget (StateT (List Bytes) Sha512RoComp) +
        (sigImplState + ddhImplState)) oa).run msgs =
      simulateQ (primBaseRoImpl P + (sigHandler + ddhImplBase))
        ((simulateQ logSigQuery oa).run msgs) := by
  dsimp only
  induction oa using OracleComp.inductionOn generalizing msgs with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind q cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rcases q with (((k | pq) | bs) | (sq | ⟨X, Y, Z⟩))
      · simp only [logSigQuery_run_unif, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          simulateQ_map, bind_map_left, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        congr 1; funext u; exact ih u msgs
      · simp only [logSigQuery_run_prim, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          simulateQ_map, bind_map_left, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        congr 1; funext u; exact ih u msgs
      · simp only [logSigQuery_run_ro, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          simulateQ_map, bind_map_left, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map]
        congr 1; funext u; exact ih u msgs
      · rcases sq with ⟨m⟩
        simp only [logSigQuery_run_sig, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
          StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_modify,
          StateT.run_pure, bind_assoc, pure_bind, simulateQ_map, bind_map_left,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
        congr 1; funext sig; exact ih sig (m :: msgs)
      · simp only [logSigQuery_run_ddh, QueryImpl.add_apply_inr,
          StateT.run_pure, pure_bind, simulateQ_map, bind_map_left,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
        exact ih (isValidDhTriple X Y Z) msgs

/-! ## Hedged-nonce `H_1` decoupling -/

private def h1Input (sk m r : Bytes) : Bytes :=
  xeddsaHashPrefix ++ clampScalar25519 sk ++ m ++ fitBytesRef 64 r

private theorem h1Input_isH1 (sk m r : Bytes) : isH1 (h1Input sk m r) = true := by
  unfold h1Input
  rw [List.append_assoc, List.append_assoc]
  exact isH1_xeddsaHashPrefix_append _

private theorem h1Input_inj_on_64 (sk m : Bytes) :
    ∀ r1 r2 : Bytes, r1.length = 64 → r2.length = 64 → h1Input sk m r1 = h1Input sk m r2 → r1 = r2 := by
  intro r1 r2 hr1 hr2 heq
  unfold h1Input at heq
  have hfit := List.append_cancel_left heq
  rwa [fitBytesRef_of_length_eq hr1, fitBytesRef_of_length_eq hr2] at hfit

private def ddhRoImpl (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl gapDhOracleSpec Sha512RoComp :=
  fun (X, Y, Z) => pure (isValidDhTriple X Y Z)

private def ddhStateImpl (σ : Type) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl gapDhOracleSpec (StateT σ ProbComp) :=
  fun (X, Y, Z) => pure (isValidDhTriple X Y Z)

private theorem sha512RoImpl_run_some {t : Bytes} {c : sha512RoSpec.QueryCache} {v : Bytes}
    (h : c t = some v) :
    (sha512RoImpl t).run c = pure (v, c) :=
  QueryImpl.withCaching_run_some sha512RoBaseImpl h

private theorem sha512RoImpl_run_none {t : Bytes} {c : sha512RoSpec.QueryCache}
    (h : c t = none) :
    (sha512RoImpl t).run c =
      (fun v => (v, c.cacheQuery t v)) <$> sampleRandom64 :=
  QueryImpl.withCaching_run_none sha512RoBaseImpl h

private noncomputable def sigRoImpl₀ (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec Sha512RoComp :=
  fun (.sign m) => do
    let r ← liftM (m := ProbComp) sampleRandom64
    simulateQ sha512RoImpl (xeddsaSignRo P sk m r)

private noncomputable def impl₀ (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl XeddsaRomOracleSpec Sha512RoComp :=
  primBaseRoImpl P + (sigRoImpl₀ P sk + ddhRoImpl isValidDhTriple)

@[simp]
private theorem impl₀_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (n : ℕ) (c : sha512RoSpec.QueryCache) :
    (impl₀ P isValidDhTriple sk (.inl (.inl (.inl n)))).run c =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, c)) := rfl

@[simp]
private theorem impl₀_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (pq : PrimQuery) :
    impl₀ P isValidDhTriple sk (.inl (.inl (.inr pq))) =
      simulateQ sha512RoImpl (primRoStep P pq) := rfl

@[simp]
private theorem impl₀_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk bs : Bytes) :
    impl₀ P isValidDhTriple sk (.inl (.inr bs)) = sha512RoImpl bs := rfl

@[simp]
private theorem impl₀_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk m : Bytes) :
    impl₀ P isValidDhTriple sk (.inr (.inl (.sign m))) = sigRoImpl₀ P sk (.sign m) := rfl

@[simp]
private theorem impl₀_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk X Y Z : Bytes) :
    impl₀ P isValidDhTriple sk (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

private noncomputable def sigRoImpl₁ (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec Sha512RoComp :=
  fun (.sign m) => StateT.mk fun advC =>
    sampleRandom64 >>= fun h1Digest =>
      let keyData := clampScalar25519 sk
      let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
      let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
      (sha512RoImpl (capR ++ capA ++ m)).run advC >>= fun p2 =>
        pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)

private theorem sigRoImpl₁_run (P : Primitives) (sk m : Bytes) (advC : sha512RoSpec.QueryCache) :
    (sigRoImpl₁ P sk (.sign m)).run advC =
      (sampleRandom64 >>= fun h1Digest =>
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
        (sha512RoImpl (capR ++ capA ++ m)).run advC >>= fun p2 =>
          pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)) := rfl

private noncomputable def impl₁ (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl XeddsaRomOracleSpec Sha512RoComp :=
  primBaseRoImpl P + (sigRoImpl₁ P sk + ddhRoImpl isValidDhTriple)

@[simp]
private theorem impl₁_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (n : ℕ) (c : sha512RoSpec.QueryCache) :
    (impl₁ P isValidDhTriple sk (.inl (.inl (.inl n)))).run c =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, c)) := rfl

@[simp]
private theorem impl₁_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (pq : PrimQuery) :
    impl₁ P isValidDhTriple sk (.inl (.inl (.inr pq))) =
      simulateQ sha512RoImpl (primRoStep P pq) := rfl

@[simp]
private theorem impl₁_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk bs : Bytes) :
    impl₁ P isValidDhTriple sk (.inl (.inr bs)) = sha512RoImpl bs := rfl

@[simp]
private theorem impl₁_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk m : Bytes) :
    impl₁ P isValidDhTriple sk (.inr (.inl (.sign m))) = sigRoImpl₁ P sk (.sign m) := rfl

@[simp]
private theorem impl₁_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk X Y Z : Bytes) :
    impl₁ P isValidDhTriple sk (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

private abbrev Hop1State : Type :=
  (sha512RoSpec.QueryCache × sha512RoSpec.QueryCache) × Bool

private def unionCache (advC sigC : sha512RoSpec.QueryCache) : sha512RoSpec.QueryCache :=
  QueryCache.ofFn fun k =>
    match sigC k with
    | some v => some v
    | none   => advC k

@[simp]
private theorem unionCache_empty : unionCache ∅ ∅ = ∅ := by
  ext k
  rfl

private theorem unionCache_cacheQuery_adv {advC sigC : sha512RoSpec.QueryCache}
    {t : Bytes} (hsig : sigC t = none) (v : Bytes) :
    unionCache (advC.cacheQuery t v) sigC = (unionCache advC sigC).cacheQuery t v := by
  ext k
  by_cases hkt : k = t
  · subst hkt
    simp [unionCache, hsig]
  · simp [unionCache, QueryCache.cacheQuery_of_ne _ _ hkt]

private theorem unionCache_cacheQuery_sig (advC sigC : sha512RoSpec.QueryCache) (t v : Bytes) :
    unionCache advC (sigC.cacheQuery t v) = (unionCache advC sigC).cacheQuery t v := by
  ext k
  by_cases hkt : k = t
  · subst hkt
    simp [unionCache]
  · simp [unionCache, QueryCache.cacheQuery_of_ne _ _ hkt]

private theorem projNonH1_unionCache {advC sigC : sha512RoSpec.QueryCache}
    (hinv : ∀ k, (sigC k).isSome = true → isH1 k = true) :
    projNonH1 (unionCache advC sigC) = projNonH1 advC := by
  ext k
  by_cases hk : isH1 k = true
  · simp [projNonH1_apply, hk]
  · simp only [projNonH1_apply, hk, unionCache, QueryCache.ofFn_apply]
    cases hs : sigC k with
    | none => rfl
    | some v =>
        exfalso
        exact hk (hinv k (by simp [hs]))

private def roStep₀ : QueryImpl sha512RoSpec (StateT Hop1State ProbComp) :=
  fun t => StateT.mk fun ((advC, sigC), bad) =>
    match sigC t with
    | some v => pure (v, ((advC, sigC), true))
    | none =>
        match advC t with
        | some v => pure (v, ((advC, sigC), bad))
        | none =>
            (fun v => (v, ((advC.cacheQuery t v, sigC), bad))) <$> sampleRandom64

private theorem roStep₀_run (t : Bytes) (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) :
    (roStep₀ t).run ((advC, sigC), bad) =
      match sigC t with
      | some v => pure (v, ((advC, sigC), true))
      | none =>
          match advC t with
          | some v => pure (v, ((advC, sigC), bad))
          | none =>
              (fun v => (v, ((advC.cacheQuery t v, sigC), bad))) <$> sampleRandom64 := rfl

private def roStep₁ : QueryImpl sha512RoSpec (StateT Hop1State ProbComp) :=
  fun t => StateT.mk fun ((advC, sigC), bad) =>
    (fun p : Bytes × sha512RoSpec.QueryCache =>
      (p.1, ((p.2, sigC), bad || (sigC t).isSome))) <$> (sha512RoImpl t).run advC

private theorem roStep₁_run (t : Bytes) (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) :
    (roStep₁ t).run ((advC, sigC), bad) =
      (fun p : Bytes × sha512RoSpec.QueryCache =>
        (p.1, ((p.2, sigC), bad || (sigC t).isSome))) <$> (sha512RoImpl t).run advC := rfl

private def sigH1Step₀ (t₁ : Bytes) : StateT Hop1State ProbComp Bytes :=
  StateT.mk fun ((advC, sigC), bad) =>
    match unionCache advC sigC t₁ with
    | some v => pure (v, ((advC, sigC), true))
    | none =>
        (fun v => (v, ((advC, sigC.cacheQuery t₁ v), bad))) <$> sampleRandom64

private theorem sigH1Step₀_run (t₁ : Bytes) (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) :
    (sigH1Step₀ t₁).run ((advC, sigC), bad) =
      match unionCache advC sigC t₁ with
      | some v => pure (v, ((advC, sigC), true))
      | none =>
          (fun v => (v, ((advC, sigC.cacheQuery t₁ v), bad))) <$> sampleRandom64 := rfl

private noncomputable def sigTrk₀ (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec (StateT Hop1State ProbComp) :=
  fun (.sign m) => StateT.mk fun s =>
    sampleRandom64 >>= fun r =>
      (sigH1Step₀ (h1Input sk m r)).run s >>= fun p1 =>
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        let capR := P.compress (edBaseMul P (P.scalarFromWide p1.1))
        (roStep₀ (capR ++ capA ++ m)).run p1.2 >>= fun p2 =>
          pure (xeddsaSignFromDigests P sk p1.1 p2.1, p2.2)

private theorem sigTrk₀_run (P : Primitives) (sk m : Bytes) (s : Hop1State) :
    (sigTrk₀ P sk (.sign m)).run s =
      (sampleRandom64 >>= fun r =>
        (sigH1Step₀ (h1Input sk m r)).run s >>= fun p1 =>
          let keyData := clampScalar25519 sk
          let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
          let capR := P.compress (edBaseMul P (P.scalarFromWide p1.1))
          (roStep₀ (capR ++ capA ++ m)).run p1.2 >>= fun p2 =>
            pure (xeddsaSignFromDigests P sk p1.1 p2.1, p2.2)) := rfl

private theorem simulateQ_sha512RoImpl_xeddsaSignRo_run
    (P : Primitives) (sk m r : Bytes) (c : sha512RoSpec.QueryCache) :
    (simulateQ sha512RoImpl (xeddsaSignRo P sk m r)).run c =
      ((sha512RoImpl (h1Input sk m r)).run c >>= fun p1 =>
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        let capR := P.compress (edBaseMul P (P.scalarFromWide p1.1))
        (sha512RoImpl (capR ++ capA ++ m)).run p1.2 >>= fun p2 =>
          pure (xeddsaSignFromDigests P sk p1.1 p2.1, p2.2)) := by
  unfold xeddsaSignRo h1Input xeddsaSignFromDigests
  simp [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, StateT.run_bind]

private noncomputable def sigTrk₁ (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec (StateT Hop1State ProbComp) :=
  fun (.sign m) => StateT.mk fun ((advC, sigC), bad) =>
    sampleRandom64 >>= fun r =>
      sampleRandom64 >>= fun h1Digest =>
        let s₁ : Hop1State :=
          match unionCache advC sigC (h1Input sk m r) with
          | some _ => ((advC, sigC), true)
          | none   => ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), bad)
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
        (roStep₁ (capR ++ capA ++ m)).run s₁ >>= fun p2 =>
          pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)

private theorem sigTrk₁_run (P : Primitives) (sk m : Bytes)
    (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) :
    (sigTrk₁ P sk (.sign m)).run ((advC, sigC), bad) =
      (sampleRandom64 >>= fun r =>
        sampleRandom64 >>= fun h1Digest =>
          let s₁ : Hop1State :=
            match unionCache advC sigC (h1Input sk m r) with
            | some _ => ((advC, sigC), true)
            | none   => ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), bad)
          let keyData := clampScalar25519 sk
          let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
          let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
          (roStep₁ (capR ++ capA ++ m)).run s₁ >>= fun p2 =>
            pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)) := rfl

private def primBaseTrk (P : Primitives)
    (ro : QueryImpl sha512RoSpec (StateT Hop1State ProbComp)) :
    QueryImpl (PrimBaseSpec + sha512RoSpec) (StateT Hop1State ProbComp) :=
  (QueryImpl.ofLift unifSpec (StateT Hop1State ProbComp) +
    (fun q => simulateQ ro (primRoStep P q))) + ro

private noncomputable def impl₀_trk (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl XeddsaRomOracleSpec (StateT Hop1State ProbComp) :=
  primBaseTrk P roStep₀ +
    (sigTrk₀ P sk + ddhStateImpl Hop1State isValidDhTriple)

private noncomputable def impl₁_trk (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl XeddsaRomOracleSpec (StateT Hop1State ProbComp) :=
  primBaseTrk P roStep₁ +
    (sigTrk₁ P sk + ddhStateImpl Hop1State isValidDhTriple)

@[simp]
private theorem impl₀_trk_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (n : ℕ) (s : Hop1State) :
    (impl₀_trk P isValidDhTriple sk (.inl (.inl (.inl n)))).run s =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)) := rfl

@[simp]
private theorem impl₀_trk_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (pq : PrimQuery) :
    impl₀_trk P isValidDhTriple sk (.inl (.inl (.inr pq))) =
      simulateQ roStep₀ (primRoStep P pq) := rfl

@[simp]
private theorem impl₀_trk_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk bs : Bytes) :
    impl₀_trk P isValidDhTriple sk (.inl (.inr bs)) = roStep₀ bs := rfl

@[simp]
private theorem impl₀_trk_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk m : Bytes) :
    impl₀_trk P isValidDhTriple sk (.inr (.inl (.sign m))) = sigTrk₀ P sk (.sign m) := rfl

@[simp]
private theorem impl₀_trk_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk X Y Z : Bytes) :
    impl₀_trk P isValidDhTriple sk (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

@[simp]
private theorem impl₁_trk_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (n : ℕ) (s : Hop1State) :
    (impl₁_trk P isValidDhTriple sk (.inl (.inl (.inl n)))).run s =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)) := rfl

@[simp]
private theorem impl₁_trk_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (pq : PrimQuery) :
    impl₁_trk P isValidDhTriple sk (.inl (.inl (.inr pq))) =
      simulateQ roStep₁ (primRoStep P pq) := rfl

@[simp]
private theorem impl₁_trk_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk bs : Bytes) :
    impl₁_trk P isValidDhTriple sk (.inl (.inr bs)) = roStep₁ bs := rfl

@[simp]
private theorem impl₁_trk_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk m : Bytes) :
    impl₁_trk P isValidDhTriple sk (.inr (.inl (.sign m))) = sigTrk₁ P sk (.sign m) := rfl

@[simp]
private theorem impl₁_trk_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk X Y Z : Bytes) :
    impl₁_trk P isValidDhTriple sk (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

private theorem roStep₀_proj_union (t : Bytes) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$> (roStep₀ t).run s =
      (sha512RoImpl t).run (unionCache s.1.1 s.1.2) := by
  rcases s with ⟨⟨advC, sigC⟩, bad⟩
  change Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$>
      (roStep₀ t).run ((advC, sigC), bad) =
    (sha512RoBaseImpl.withCaching t).run (unionCache advC sigC)
  rw [roStep₀_run]
  cases hs : sigC t with
  | some v =>
      have hu : unionCache advC sigC t = some v := by simp [unionCache, hs]
      rw [QueryImpl.withCaching_run_some _ hu]
      rfl
  | none =>
      cases ha : advC t with
      | some v =>
          have hu : unionCache advC sigC t = some v := by simp [unionCache, hs, ha]
          rw [QueryImpl.withCaching_run_some _ hu]
          rfl
      | none =>
          have hu : unionCache advC sigC t = none := by simp [unionCache, hs, ha]
          rw [QueryImpl.withCaching_run_none _ hu, Functor.map_map]
          congr 1
          funext v
          exact Prod.ext rfl (unionCache_cacheQuery_adv hs v)

private theorem sigH1Step₀_proj_union (t₁ : Bytes) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$> (sigH1Step₀ t₁).run s =
      (sha512RoImpl t₁).run (unionCache s.1.1 s.1.2) := by
  rcases s with ⟨⟨advC, sigC⟩, bad⟩
  change Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$>
      (sigH1Step₀ t₁).run ((advC, sigC), bad) =
    (sha512RoBaseImpl.withCaching t₁).run (unionCache advC sigC)
  rw [sigH1Step₀_run]
  cases hu : unionCache advC sigC t₁ with
  | some v =>
      rw [QueryImpl.withCaching_run_some _ hu]
      rfl
  | none =>
      rw [QueryImpl.withCaching_run_none _ hu, Functor.map_map]
      congr 1
      funext v
      exact Prod.ext rfl (unionCache_cacheQuery_sig advC sigC t₁ v)

private theorem simulateQ_roStep₀_proj_union {β : Type}
    (sub : OracleComp sha512RoSpec β) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$>
        (simulateQ roStep₀ sub).run s =
      (simulateQ sha512RoImpl sub).run (unionCache s.1.1 s.1.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq roStep₀ sha512RoImpl
    (fun s' : Hop1State => unionCache s'.1.1 s'.1.2)
    roStep₀_proj_union sub s

private theorem impl₀_trk_proj_union {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) <$>
        (simulateQ (impl₀_trk P isValidDhTriple sk) oa).run s =
      (simulateQ (impl₀ P isValidDhTriple sk) oa).run (unionCache s.1.1 s.1.2) := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (impl₀_trk P isValidDhTriple sk) (impl₀ P isValidDhTriple sk)
    (fun s' : Hop1State => unionCache s'.1.1 s'.1.2) ?_ oa s
  intro q s'
  rcases q with (((k | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp only [impl₀_trk_unif, impl₀_unif, map_bind, map_pure]
    rfl
  · simp only [impl₀_trk_prim, impl₀_prim]
    exact simulateQ_roStep₀_proj_union (primRoStep P pq) s'
  · simp only [impl₀_trk_ro, impl₀_ro]
    exact roStep₀_proj_union bs s'
  · rcases sq with ⟨m⟩
    rw [impl₀_trk_sig, impl₀_sig, sigTrk₀_run]
    simp only [sigRoImpl₀, StateT.run_bind, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind]
    rw [map_bind]
    congr 1
    funext r
    rw [simulateQ_sha512RoImpl_xeddsaSignRo_run, map_bind,
      ← sigH1Step₀_proj_union (h1Input sk m r) s', bind_map_left]
    congr 1
    funext p1
    dsimp only [Prod.map, id_eq]
    rw [map_bind, ← roStep₀_proj_union _ p1.2, bind_map_left]
    congr 1
  · simp only [impl₀_trk_ddh, impl₀_ddh, StateT.run_pure, map_pure]
    rfl

private theorem impl₀_trk_preserves_sigH1 {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) :
    ∀ s : Hop1State, (∀ k, (s.1.2 k).isSome = true → isH1 k = true) →
      ∀ z ∈ support ((simulateQ (impl₀_trk P isValidDhTriple sk) oa).run s),
        ∀ k, (z.2.1.2 k).isSome = true → isH1 k = true := by
  have hro : ∀ (sub : OracleComp sha512RoSpec Bytes) (s : Hop1State),
      (∀ k, (s.1.2 k).isSome = true → isH1 k = true) →
      ∀ z ∈ support ((simulateQ roStep₀ sub).run s),
        ∀ k, (z.2.1.2 k).isSome = true → isH1 k = true := by
    intro sub
    induction sub using OracleComp.inductionOn with
    | pure _ =>
        intro s hs z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hs
    | query_bind t cont ih =>
        intro s hs z hz
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨us, hus, hz⟩ := hz
        have hus_inv : ∀ k, (us.2.1.2 k).isSome = true → isH1 k = true := by
          rcases s with ⟨⟨advC, sigC⟩, bad⟩
          rw [roStep₀_run] at hus
          cases h1 : sigC t
          · rw [h1] at hus
            cases h2 : advC t
            · rw [h2, support_map] at hus
              obtain ⟨v, _, rfl⟩ := hus; exact hs
            · rw [h2, support_pure, Set.mem_singleton_iff] at hus
              subst hus; exact hs
          · rw [h1, support_pure, Set.mem_singleton_iff] at hus
            subst hus; exact hs
        exact ih us.1 us.2 hus_inv z hz
  have hro_any : ∀ {β : Type} (sub : OracleComp sha512RoSpec β) (s : Hop1State),
      (∀ k, (s.1.2 k).isSome = true → isH1 k = true) →
      ∀ z ∈ support ((simulateQ roStep₀ sub).run s),
        ∀ k, (z.2.1.2 k).isSome = true → isH1 k = true := by
    intro β sub
    induction sub using OracleComp.inductionOn with
    | pure _ =>
        intro s hs z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hs
    | query_bind t cont ih =>
        intro s hs z hz
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨us, hus, hz⟩ := hz
        have hus_inv : ∀ k, (us.2.1.2 k).isSome = true → isH1 k = true :=
          hro (liftM (sha512RoSpec.query t)) s hs us (by simpa [simulateQ_query] using hus)
        exact ih us.1 us.2 hus_inv z hz
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
  | query_bind q cont ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have hus_inv : ∀ k, (us.2.1.2 k).isSome = true → isH1 k = true := by
        rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
        · simp only [impl₀_trk_unif, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hus
          obtain ⟨_, _, rfl⟩ := hus; exact hs
        · rw [impl₀_trk_prim] at hus
          exact hro_any (primRoStep P pq) s hs us hus
        · rw [impl₀_trk_ro] at hus
          exact hro_any (liftM (sha512RoSpec.query bs)) s hs us
            (by simpa [simulateQ_query] using hus)
        · rcases sq with ⟨m⟩
          rw [impl₀_trk_sig, sigTrk₀_run] at hus
          rw [mem_support_bind_iff] at hus; obtain ⟨r, _, hus⟩ := hus
          rw [mem_support_bind_iff] at hus; obtain ⟨p1, hp1, hus⟩ := hus
          rw [mem_support_bind_iff] at hus; obtain ⟨p2, hp2, hus⟩ := hus
          simp only [support_pure, Set.mem_singleton_iff] at hus; subst hus
          have hp1_inv : ∀ k, (p1.2.1.2 k).isSome = true → isH1 k = true := by
            rcases s with ⟨⟨advC, sigC⟩, bad⟩
            rw [sigH1Step₀_run] at hp1
            cases hu : unionCache advC sigC (h1Input sk m r)
            · rw [hu, support_map] at hp1
              obtain ⟨v, _, rfl⟩ := hp1
              intro k hk
              by_cases hkt : k = h1Input sk m r
              · subst hkt; exact h1Input_isH1 sk m r
              · rw [QueryCache.cacheQuery_of_ne _ _ hkt] at hk; exact hs k hk
            · rw [hu, support_pure, Set.mem_singleton_iff] at hp1
              subst hp1; exact hs
          exact hro_any (liftM (sha512RoSpec.query _)) p1.2 hp1_inv p2
            (by simpa [simulateQ_query] using hp2)
        · simp only [impl₀_trk_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
          subst hus; exact hs
      exact ih us.1 us.2 hus_inv z hz

private theorem evalDistEq_proj_impl₀_trk {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) :
    (fun z : α × Hop1State => (z.1, projNonH1 z.2.1.1)) <$>
        (simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false) =ᵈ
      Prod.map id projNonH1 <$>
        (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅ := by
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  have hproj := impl₀_trk_proj_union P isValidDhTriple sk oa ((∅, ∅), false)
  dsimp only at hproj
  rw [unionCache_empty] at hproj
  rw [← hproj, Functor.map_map, prEvent_map, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun z hz => ?_
  have hinv := impl₀_trk_preserves_sigH1 P isValidDhTriple sk oa ((∅, ∅), false)
    (fun k hk => by simp at hk) z hz
  exact iff_of_eq (congrArg p (Prod.ext rfl (projNonH1_unionCache hinv).symm))

private theorem roStep₁_proj_adv (t : Bytes) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => s'.1.1) <$> (roStep₁ t).run s =
      (sha512RoImpl t).run s.1.1 := by
  rcases s with ⟨⟨advC, sigC⟩, bad⟩
  rw [roStep₁_run, Functor.map_map]
  exact id_map _

private theorem simulateQ_roStep₁_proj_adv {β : Type}
    (sub : OracleComp sha512RoSpec β) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => s'.1.1) <$> (simulateQ roStep₁ sub).run s =
      (simulateQ sha512RoImpl sub).run s.1.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq roStep₁ sha512RoImpl
    (fun s' : Hop1State => s'.1.1)
    roStep₁_proj_adv sub s

private theorem evalDistEq_step_impl₁_trk (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (q : XeddsaRomOracleSpec.Domain) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => s'.1.1) <$>
        (impl₁_trk P isValidDhTriple sk q).run s =ᵈ
      (impl₁ P isValidDhTriple sk q).run s.1.1 := by
  rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · rfl
  · rw [impl₁_trk_prim, impl₁_prim, simulateQ_roStep₁_proj_adv]
  · rw [impl₁_trk_ro, impl₁_ro, roStep₁_proj_adv]
  · rcases sq with ⟨m⟩
    rcases s with ⟨⟨advC, sigC⟩, bad⟩
    rw [impl₁_trk_sig, impl₁_sig, sigTrk₁_run, sigRoImpl₁_run, map_bind]
    have hconst : ∀ r : Bytes,
        Prod.map id (fun s' : Hop1State => s'.1.1) <$>
          (sampleRandom64 >>= fun h1Digest =>
            let s₁ : Hop1State :=
              match unionCache advC sigC (h1Input sk m r) with
              | some _ => ((advC, sigC), true)
              | none   => ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), bad)
            let keyData := clampScalar25519 sk
            let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
            let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
            (roStep₁ (capR ++ capA ++ m)).run s₁ >>= fun p2 =>
              pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)) =
        (sampleRandom64 >>= fun h1Digest =>
          let keyData := clampScalar25519 sk
          let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
          let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
          (sha512RoImpl (capR ++ capA ++ m)).run advC >>= fun p2 =>
            pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)) := by
      intro r
      rw [map_bind]
      congr 1; funext h1Digest
      dsimp only
      set s₁ : Hop1State :=
        match unionCache advC sigC (h1Input sk m r) with
        | some _ => ((advC, sigC), true)
        | none   => ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), bad)
      have hs1 : s₁.1.1 = advC := by
        dsimp only [s₁]; cases unionCache advC sigC (h1Input sk m r) <;> rfl
      conv_rhs => rw [← hs1, ← roStep₁_proj_adv _ s₁]
      rw [bind_map_left, map_bind]
      congr 1
    simp_rw [hconst]
    let : MeasurableSpace (Bytes × sha512RoSpec.QueryCache) := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const sampleRandom64 _)
  · rfl

private theorem evalDistEq_proj_impl₁_trk {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) (s : Hop1State) :
    Prod.map id (fun s' : Hop1State => s'.1.1) <$>
        (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run s =ᵈ
      (simulateQ (impl₁ P isValidDhTriple sk) oa).run s.1.1 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
  | query_bind q cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      have h1 :
          ((impl₁_trk P isValidDhTriple sk q).run s >>= fun us =>
            Prod.map id (fun s' : Hop1State => s'.1.1) <$>
              (simulateQ (impl₁_trk P isValidDhTriple sk) (cont us.1)).run us.2) =ᵈ
          ((impl₁_trk P isValidDhTriple sk q).run s >>= fun us =>
            (simulateQ (impl₁ P isValidDhTriple sk) (cont us.1)).run us.2.1.1) :=
        EvalDistEq.bind EvalDistEq.rfl fun us => ih us.1 us.2
      have h2 :
          ((impl₁_trk P isValidDhTriple sk q).run s >>= fun us =>
            (simulateQ (impl₁ P isValidDhTriple sk) (cont us.1)).run us.2.1.1) =
          ((Prod.map id (fun s' : Hop1State => s'.1.1) <$>
            (impl₁_trk P isValidDhTriple sk q).run s) >>= fun uc =>
            (simulateQ (impl₁ P isValidDhTriple sk) (cont uc.1)).run uc.2) := by
        rw [bind_map_left]; rfl
      refine h1.trans ?_
      rw [h2]
      exact EvalDistEq.bind (evalDistEq_step_impl₁_trk P isValidDhTriple sk q s)
        fun _ => EvalDistEq.rfl

private theorem roStep₀_mono :
    ∀ t (s : Hop1State), s.2 = true → ∀ z ∈ support ((roStep₀ t).run s), z.2.2 = true := by
  intro t ⟨⟨advC, sigC⟩, bad⟩ hbad z hz
  dsimp only at hbad; subst hbad
  rw [roStep₀_run] at hz
  cases h1 : sigC t
  · rw [h1] at hz
    cases h2 : advC t
    · rw [h2, support_map] at hz; obtain ⟨_, _, rfl⟩ := hz; rfl
    · rw [h2, support_pure, Set.mem_singleton_iff] at hz; subst hz; rfl
  · rw [h1, support_pure, Set.mem_singleton_iff] at hz; subst hz; rfl

private theorem roStep₁_mono :
    ∀ t (s : Hop1State), s.2 = true → ∀ z ∈ support ((roStep₁ t).run s), z.2.2 = true := by
  intro t ⟨⟨advC, sigC⟩, bad⟩ hbad z hz
  dsimp only at hbad; subst hbad
  rw [roStep₁_run, support_map] at hz
  obtain ⟨_, _, rfl⟩ := hz; rfl

private theorem roStep_agree :
    ∀ t (s : Hop1State), ¬ s.2 = true → ∀ q : Bytes × Hop1State → Prop,
      Pr{let z ← (roStep₀ t).run s}[q z ∧ ¬ z.2.2 = true] =
        Pr{let z ← (roStep₁ t).run s}[q z ∧ ¬ z.2.2 = true] := by
  intro t ⟨⟨advC, sigC⟩, bad⟩ hbad q
  have hb0 : bad = false := Bool.eq_false_iff.mpr hbad
  subst hb0
  rw [roStep₀_run, roStep₁_run]
  cases hs : sigC t with
  | some v =>
      rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz h => by
          simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact h.2 rfl),
        prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz h => by
          rw [support_map] at hz
          obtain ⟨_, _, rfl⟩ := hz; exact h.2 rfl)]
  | none =>
      simp only [Option.isSome_none, Bool.or_false]
      cases ha : advC t with
      | some v =>
          rw [sha512RoImpl_run_some ha]
          rfl
      | none =>
          rw [sha512RoImpl_run_none ha, Functor.map_map]
          rfl

private theorem impl₀_trk_mono (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ q (s : Hop1State), s.2 = true →
      ∀ z ∈ support ((impl₀_trk P isValidDhTriple sk q).run s), z.2.2 = true := by
  intro q s hbad z hz
  rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp only [impl₀_trk_unif, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, _, rfl⟩ := hz; exact hbad
  · rw [impl₀_trk_prim] at hz
    exact OracleComp.ProgramLogic.Relational.forall_mem_support_simulateQ_run_of_bad
      roStep₀ (fun st => st.2 = true) roStep₀_mono (primRoStep P pq) hbad z hz
  · rw [impl₀_trk_ro] at hz
    exact roStep₀_mono bs s hbad z hz
  · rcases sq with ⟨m⟩
    rw [impl₀_trk_sig, sigTrk₀_run] at hz
    rw [mem_support_bind_iff] at hz; obtain ⟨r, _, hz⟩ := hz
    rw [mem_support_bind_iff] at hz; obtain ⟨p1, hp1, hz⟩ := hz
    rw [mem_support_bind_iff] at hz; obtain ⟨p2, hp2, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    have hp1_bad : p1.2.2 = true := by
      rcases s with ⟨⟨advC, sigC⟩, bad⟩
      dsimp only at hbad; subst hbad
      rw [sigH1Step₀_run] at hp1
      cases hu : unionCache advC sigC (h1Input sk m r)
      · rw [hu, support_map] at hp1; obtain ⟨_, _, rfl⟩ := hp1; rfl
      · rw [hu, support_pure, Set.mem_singleton_iff] at hp1; subst hp1; rfl
    exact roStep₀_mono _ p1.2 hp1_bad p2 hp2
  · simp only [impl₀_trk_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hbad

private theorem impl₁_trk_mono (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ q (s : Hop1State), s.2 = true →
      ∀ z ∈ support ((impl₁_trk P isValidDhTriple sk q).run s), z.2.2 = true := by
  intro q s hbad z hz
  rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp only [impl₁_trk_unif, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨_, _, rfl⟩ := hz; exact hbad
  · rw [impl₁_trk_prim] at hz
    exact OracleComp.ProgramLogic.Relational.forall_mem_support_simulateQ_run_of_bad
      roStep₁ (fun st => st.2 = true) roStep₁_mono (primRoStep P pq) hbad z hz
  · rw [impl₁_trk_ro] at hz
    exact roStep₁_mono bs s hbad z hz
  · rcases sq with ⟨m⟩
    rcases s with ⟨⟨advC, sigC⟩, bad⟩
    dsimp only at hbad; subst hbad
    rw [impl₁_trk_sig, sigTrk₁_run] at hz
    rw [mem_support_bind_iff] at hz; obtain ⟨r, _, hz⟩ := hz
    rw [mem_support_bind_iff] at hz; obtain ⟨h1Digest, _, hz⟩ := hz
    rw [mem_support_bind_iff] at hz; obtain ⟨p2, hp2, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
    refine roStep₁_mono _ _ ?_ p2 hp2
    cases unionCache advC sigC (h1Input sk m r) <;> rfl
  · simp only [impl₁_trk_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hbad

private theorem impl_trk_agree (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ q (s : Hop1State), ¬ s.2 = true →
      ∀ ev : XeddsaRomOracleSpec.Range q × Hop1State → Prop,
        Pr{let z ← (impl₀_trk P isValidDhTriple sk q).run s}[ev z ∧ ¬ z.2.2 = true] =
          Pr{let z ← (impl₁_trk P isValidDhTriple sk q).run s}[ev z ∧ ¬ z.2.2 = true] := by
  intro q s hbad ev
  rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp only [impl₀_trk_unif, impl₁_trk_unif]
  · simp only [impl₀_trk_prim, impl₁_trk_prim]
    exact OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_and_not_bad_eq
      roStep₀ roStep₁ (fun st => st.2 = true) roStep_agree roStep₀_mono roStep₁_mono
      (primRoStep P pq) s ev
  · simp only [impl₀_trk_ro, impl₁_trk_ro]
    exact roStep_agree bs s hbad ev
  · rcases sq with ⟨m⟩
    rcases s with ⟨⟨advC, sigC⟩, bad⟩
    have hb0 : bad = false := Bool.eq_false_iff.mpr hbad
    subst hb0
    rw [impl₀_trk_sig, impl₁_trk_sig, sigTrk₀_run, sigTrk₁_run, map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support sampleRandom64 _ _ fun r _ => ?_
    rw [sigH1Step₀_run]
    cases hu : unionCache advC sigC (h1Input sk m r) with
    | some v =>
        dsimp only
        rw [pure_bind,
          prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz h => by
            rw [mem_support_bind_iff] at hz; obtain ⟨p2, hp2, hz⟩ := hz
            simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact h.2 (roStep₀_mono _ _ rfl p2 hp2)),
          prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz h => by
            rw [mem_support_bind_iff] at hz; obtain ⟨h1Digest, _, hz⟩ := hz
            rw [mem_support_bind_iff] at hz; obtain ⟨p2, hp2, hz⟩ := hz
            simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz
            exact h.2 (roStep₁_mono _ _ rfl p2 hp2))]
    | none =>
        dsimp only
        rw [bind_map_left, map_bind, map_bind]
        refine OracleComp.prEvent_bind_congr_of_support sampleRandom64 _ _ fun h1Digest _ => ?_
        dsimp only
        have hstep := roStep_agree
          (P.compress (edBaseMul P (P.scalarFromWide h1Digest)) ++
            P.compress (edBaseMul P (P.scalarFromBytesModOrder (clampScalar25519 sk))) ++ m)
          ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), false)
          Bool.false_ne_true
          (fun p2 => ev (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2))
        simpa only [prEvent_norm] using hstep
  · simp only [impl₀_trk_ddh, impl₁_trk_ddh]

private abbrev LogState : Type :=
  sha512RoSpec.QueryCache × Finset Bytes × List Bytes

private def roLog : QueryImpl sha512RoSpec (StateT LogState ProbComp) :=
  fun t => StateT.mk fun (advC, dom, msgs) =>
    (fun p : Bytes × sha512RoSpec.QueryCache =>
      (p.1, (p.2, Insert.insert t dom, msgs))) <$> (sha512RoImpl t).run advC

private theorem roLog_run (t : Bytes) (advC : sha512RoSpec.QueryCache)
    (dom : Finset Bytes) (msgs : List Bytes) :
    (roLog t).run (advC, dom, msgs) =
      (fun p : Bytes × sha512RoSpec.QueryCache =>
        (p.1, (p.2, Insert.insert t dom, msgs))) <$> (sha512RoImpl t).run advC := rfl

private noncomputable def sigLog (P : Primitives) (sk : Bytes) :
    QueryImpl sigOracleSpec (StateT LogState ProbComp) :=
  fun (.sign m) => StateT.mk fun (advC, dom, msgs) =>
    sampleRandom64 >>= fun h1Digest =>
      let keyData := clampScalar25519 sk
      let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
      let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
      let t₂ := capR ++ capA ++ m
      (sha512RoImpl t₂).run advC >>= fun p2 =>
        pure (xeddsaSignFromDigests P sk h1Digest p2.1,
          (p2.2, Insert.insert t₂ dom, msgs ++ [m]))

private theorem sigLog_run (P : Primitives) (sk m : Bytes)
    (advC : sha512RoSpec.QueryCache) (dom : Finset Bytes) (msgs : List Bytes) :
    (sigLog P sk (.sign m)).run (advC, dom, msgs) =
      (sampleRandom64 >>= fun h1Digest =>
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
        let t₂ := capR ++ capA ++ m
        (sha512RoImpl t₂).run advC >>= fun p2 =>
          pure (xeddsaSignFromDigests P sk h1Digest p2.1,
            (p2.2, Insert.insert t₂ dom, msgs ++ [m]))) := rfl

private noncomputable def impl₁_log (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    QueryImpl XeddsaRomOracleSpec (StateT LogState ProbComp) :=
  ((QueryImpl.ofLift unifSpec (StateT LogState ProbComp) +
      (fun q => simulateQ roLog (primRoStep P q))) + roLog) +
    (sigLog P sk + ddhStateImpl LogState isValidDhTriple)

@[simp]
private theorem impl₁_log_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (n : ℕ) (s : LogState) :
    (impl₁_log P isValidDhTriple sk (.inl (.inl (.inl n)))).run s =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)) := rfl

@[simp]
private theorem impl₁_log_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk : Bytes) (pq : PrimQuery) :
    impl₁_log P isValidDhTriple sk (.inl (.inl (.inr pq))) =
      simulateQ roLog (primRoStep P pq) := rfl

@[simp]
private theorem impl₁_log_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk bs : Bytes) :
    impl₁_log P isValidDhTriple sk (.inl (.inr bs)) = roLog bs := rfl

@[simp]
private theorem impl₁_log_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk m : Bytes) :
    impl₁_log P isValidDhTriple sk (.inr (.inl (.sign m))) = sigLog P sk (.sign m) := rfl

@[simp]
private theorem impl₁_log_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk X Y Z : Bytes) :
    impl₁_log P isValidDhTriple sk (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

private theorem roLog_msgs {β : Type} (sub : OracleComp sha512RoSpec β)
    (advC : sha512RoSpec.QueryCache) (dom : Finset Bytes) (msgs₀ : List Bytes) :
    (simulateQ roLog sub).run (advC, dom, msgs₀) =
      (fun p : β × LogState => (p.1, (p.2.1, p.2.2.1, msgs₀ ++ p.2.2.2))) <$>
        (simulateQ roLog sub).run (advC, dom, []) := by
  induction sub using OracleComp.inductionOn generalizing advC dom with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [roLog_run, roLog_run, bind_map_left, bind_map_left]
      congr 1; funext p
      exact ih p.1 p.2 (Insert.insert t dom)

private theorem run_impl₁_log_msgs {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α)
    (advC : sha512RoSpec.QueryCache) (dom : Finset Bytes) (msgs₀ : List Bytes) :
    (simulateQ (impl₁_log P isValidDhTriple sk) oa).run (advC, dom, msgs₀) =
      (fun p : α × LogState => (p.1, (p.2.1, p.2.2.1, msgs₀ ++ p.2.2.2))) <$>
        (simulateQ (impl₁_log P isValidDhTriple sk) oa).run (advC, dom, []) := by
  induction oa using OracleComp.inductionOn generalizing advC dom msgs₀ with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind q cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
      · simp only [impl₁_log_unif, bind_assoc, pure_bind]
        congr 1; funext u; exact ih u advC dom msgs₀
      · simp only [impl₁_log_prim]
        rw [roLog_msgs (primRoStep P pq) advC dom msgs₀, bind_map_left]
        congr 1; funext ⟨u, advC', dom', msgs'⟩
        dsimp only
        rw [ih u advC' dom' (msgs₀ ++ msgs'), ih u advC' dom' msgs', Functor.map_map]
        congr 1; funext z
        simp [List.append_assoc]
      · simp only [impl₁_log_ro]
        rw [roLog_run, roLog_run, bind_map_left, bind_map_left]
        congr 1; funext p
        exact ih p.1 p.2 (Insert.insert bs dom) msgs₀
      · rcases sq with ⟨m⟩
        rw [impl₁_log_sig, sigLog_run, sigLog_run]
        simp only [bind_assoc, pure_bind, List.nil_append]
        congr 1; funext h1Digest
        congr 1; funext p
        rw [ih _ p.2 _ (msgs₀ ++ [m]), ih _ p.2 _ [m], Functor.map_map]
        congr 1; funext z
        simp [List.append_assoc]
      · simp only [impl₁_log_ddh, StateT.run_pure, pure_bind]
        exact ih (isValidDhTriple X Y Z) advC dom msgs₀

private theorem impl₁_log_dom_subset {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) :
    ∀ (s : LogState),
      (∀ k, (s.1 k).isSome = true → k ∈ s.2.1) →
      ∀ z ∈ support ((simulateQ (impl₁_log P isValidDhTriple sk) oa).run s),
        s.2.1 ⊆ z.2.2.1 ∧ (∀ k, (z.2.1 k).isSome = true → k ∈ z.2.2.1) := by
  have hro_one : ∀ (t : Bytes) (s : LogState),
      (∀ k, (s.1 k).isSome = true → k ∈ s.2.1) →
      ∀ z ∈ support ((roLog t).run s),
        s.2.1 ⊆ z.2.2.1 ∧ (∀ k, (z.2.1 k).isSome = true → k ∈ z.2.2.1) := by
    intro t ⟨advC, dom, msgs⟩ hs z hz
    rw [roLog_run, support_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    refine ⟨Finset.subset_insert t dom, fun k hk => ?_⟩
    cases hc : advC t with
    | some v =>
        rw [sha512RoImpl_run_some hc, support_pure, Set.mem_singleton_iff] at hp
        subst hp; exact Finset.mem_insert_of_mem (hs k hk)
    | none =>
        rw [sha512RoImpl_run_none hc, support_map] at hp
        obtain ⟨v, _, rfl⟩ := hp
        by_cases hkt : k = t
        · rw [hkt]; exact Finset.mem_insert_self t dom
        · rw [QueryCache.cacheQuery_of_ne _ _ hkt] at hk
          exact Finset.mem_insert_of_mem (hs k hk)
  have hro : ∀ {β : Type} (sub : OracleComp sha512RoSpec β) (s : LogState),
      (∀ k, (s.1 k).isSome = true → k ∈ s.2.1) →
      ∀ z ∈ support ((simulateQ roLog sub).run s),
        s.2.1 ⊆ z.2.2.1 ∧ (∀ k, (z.2.1 k).isSome = true → k ∈ z.2.2.1) := by
    intro β sub
    induction sub using OracleComp.inductionOn with
    | pure _ =>
        intro s hs z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact ⟨Finset.Subset.refl _, hs⟩
    | query_bind t cont ih =>
        intro s hs z hz
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨us, hus, hz⟩ := hz
        obtain ⟨hsub1, hinv1⟩ := hro_one t s hs us hus
        obtain ⟨hsub2, hinv2⟩ := ih us.1 us.2 hinv1 z hz
        exact ⟨hsub1.trans hsub2, hinv2⟩
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro s hs z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact ⟨Finset.Subset.refl _, hs⟩
  | query_bind q cont ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have hstep : s.2.1 ⊆ us.2.2.1 ∧ (∀ k, (us.2.1 k).isSome = true → k ∈ us.2.2.1) := by
        rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
        · simp only [impl₁_log_unif, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hus
          obtain ⟨_, _, rfl⟩ := hus; exact ⟨Finset.Subset.refl _, hs⟩
        · rw [impl₁_log_prim] at hus
          exact hro (primRoStep P pq) s hs us hus
        · rw [impl₁_log_ro] at hus
          exact hro_one bs s hs us hus
        · rcases sq with ⟨m⟩
          rcases s with ⟨advC, dom, msgs⟩
          rw [impl₁_log_sig, sigLog_run] at hus
          rw [mem_support_bind_iff] at hus; obtain ⟨h1Digest, _, hus⟩ := hus
          rw [mem_support_bind_iff] at hus; obtain ⟨p, hp, hus⟩ := hus
          simp only [support_pure, Set.mem_singleton_iff] at hus; subst hus
          have h1 := hro_one _ (advC, dom, msgs) hs
            (p.1, (p.2, Insert.insert _ dom, msgs))
            (by rw [roLog_run, support_map]; exact ⟨p, hp, rfl⟩)
          exact h1
        · simp only [impl₁_log_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
          subst hus; exact ⟨Finset.Subset.refl _, hs⟩
      obtain ⟨hsub2, hinv2⟩ := ih us.1 us.2 hstep.2 z hz
      exact ⟨hstep.1.trans hsub2, hinv2⟩

private theorem impl₁_log_card_bounds {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) {qS qH : ℕ}
    (hqS : oa.IsQueryBoundP (fun q => isRomSigChalQuery q = true) qS)
    (hqH : oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true) qH)
    (s : LogState) :
    ∀ z ∈ support ((simulateQ (impl₁_log P isValidDhTriple sk) oa).run s),
      z.2.2.1.card ≤ s.2.1.card + 2 * qH + qS ∧
      z.2.2.2.length ≤ s.2.2.length + qS := by
  have hro_one : ∀ (t : Bytes) (st : LogState)
      (z : Bytes × LogState), z ∈ support ((roLog t).run st) →
      z.2.2.1.card ≤ st.2.1.card + 1 ∧ z.2.2.2.length = st.2.2.length := by
    intro t ⟨advC, dom, msgs⟩ z hz
    rw [roLog_run, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact ⟨Finset.card_insert_le t dom, rfl⟩
  induction oa using OracleComp.inductionOn generalizing qS qH s with
  | pure _ =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; dsimp only; omega
  | query_bind q cont ih =>
      rw [isQueryBoundP_query_bind_iff] at hqS hqH
      intro z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨us, hus, hz⟩ := hz
      have htail := ih us.1 (hqS.2 us.1) (hqH.2 us.1) us.2 z hz
      rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
      · simp only [impl₁_log_unif, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hus
        obtain ⟨_, _, rfl⟩ := hus
        simp only [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
          isRomPrimVerifyQuery, isRomPrimSigSignQuery, Bool.or_self, Bool.false_eq_true,
          ↓reduceIte] at htail
        exact htail
      · rw [impl₁_log_prim] at hus
        cases pq with
        | sigSign sk' m' r' =>
            have hposH : 0 < qH :=
              hqH.1.resolve_left (by simp [isRomGrowthQuery, isRomPrimSigSignQuery])
            simp only [isRomSigChalQuery, isRomGrowthQuery, isRomPrimSigSignQuery,
              Bool.or_true, ↓reduceIte, Bool.false_eq_true] at htail
            change us ∈ support ((simulateQ roLog (xeddsaSignRo P sk' m' r')).run s) at hus
            unfold xeddsaSignRo at hus
            simp only [simulateQ_bind, simulateQ_query,
              OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
              simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
              Set.mem_singleton_iff] at hus
            obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hus
            have hb1 := hro_one _ s p1 hp1
            have hb2 := hro_one _ p1.2 p2 hp2
            dsimp only at htail ⊢
            omega
        | sigVerify pk' m' sg' =>
            have hposH : 0 < qH :=
              hqH.1.resolve_left (by simp [isRomGrowthQuery, isRomPrimVerifyQuery])
            simp only [isRomSigChalQuery, isRomGrowthQuery, isRomPrimVerifyQuery,
              Bool.true_or, Bool.or_true, ↓reduceIte, Bool.false_eq_true] at htail
            change us ∈ support ((simulateQ roLog (xeddsaVerifyRo P pk' m' sg')).run s) at hus
            unfold xeddsaVerifyRo at hus
            split at hus
            · dsimp only at hus
              cases hmont : P.montToEd pk' ((sg'.getD 63 0 &&& 128) >>> 7)
              · rw [hmont] at hus
                simp only [simulateQ_pure, StateT.run_pure, support_pure,
                  Set.mem_singleton_iff] at hus
                subst hus; dsimp only at htail ⊢; omega
              · rw [hmont] at hus
                simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                  OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure,
                  StateT.run_pure, mem_support_bind_iff, support_pure,
                  Set.mem_singleton_iff] at hus
                obtain ⟨p1, hp1, rfl⟩ := hus
                have hb1 := hro_one _ s p1 hp1
                dsimp only at htail ⊢; omega
            · simp only [simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hus
              subst hus; dsimp only at htail ⊢; omega
        | _ =>
            simp only [primRoStep, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hus
            subst hus
            simp only [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
              isRomPrimVerifyQuery, isRomPrimSigSignQuery, Bool.or_self,
              Bool.false_eq_true, ↓reduceIte] at htail
            exact htail
      · rw [impl₁_log_ro] at hus
        have hposH : 0 < qH :=
          hqH.1.resolve_left (by simp [isRomGrowthQuery, isRomDirectRoQuery])
        simp only [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
          Bool.true_or, ↓reduceIte, Bool.false_eq_true] at htail
        have hb1 := hro_one bs s us hus
        omega
      · rcases sq with ⟨m⟩
        have hposS : 0 < qS := hqS.1.resolve_left (by simp [isRomSigChalQuery])
        simp only [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
          isRomPrimVerifyQuery, isRomPrimSigSignQuery, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte] at htail
        rcases s with ⟨advC, dom, msgs⟩
        rw [impl₁_log_sig, sigLog_run] at hus
        rw [mem_support_bind_iff] at hus; obtain ⟨h1Digest, _, hus⟩ := hus
        rw [mem_support_bind_iff] at hus; obtain ⟨p, _, hus⟩ := hus
        simp only [support_pure, Set.mem_singleton_iff] at hus; subst hus
        set t₂ := P.compress (edBaseMul P (P.scalarFromWide h1Digest)) ++
          P.compress (edBaseMul P (P.scalarFromBytesModOrder (clampScalar25519 sk))) ++ m
        have hins : (Insert.insert t₂ dom).card ≤ dom.card + 1 := Finset.card_insert_le t₂ dom
        have hlen : (msgs ++ [m]).length = msgs.length + 1 := by simp
        dsimp only at htail ⊢
        omega
      · simp only [impl₁_log_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hus
        subst hus
        simp only [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
          isRomPrimVerifyQuery, isRomPrimSigSignQuery, Bool.or_self,
          Bool.false_eq_true, ↓reduceIte] at htail
        exact htail

private noncomputable def evalNoncesDom (sk : Bytes) (dom : Finset Bytes) :
    List Bytes → List Bytes → ProbComp Bool
  | _, [] => pure false
  | seen, m :: ms => do
      let r ← sampleRandom64
      let t₁ := h1Input sk m r
      let restBad ← evalNoncesDom sk dom (t₁ :: seen) ms
      return (decide (t₁ ∈ dom) || decide (t₁ ∈ seen) || restBad)

private theorem prEvent_sampleRandom64_mem_finset_le (sk m : Bytes) (F : Finset Bytes) :
    Pr{let r ← sampleRandom64}[h1Input sk m r ∈ F] ≤
      (F.card : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp
  | @insert y F' hy ih =>
      have hunion : Pr{let r ← sampleRandom64}[h1Input sk m r ∈ Insert.insert y F'] ≤
          Pr{let r ← sampleRandom64}[h1Input sk m r = y] +
            Pr{let r ← sampleRandom64}[h1Input sk m r ∈ F'] := by
        calc Pr{let r ← sampleRandom64}[h1Input sk m r ∈ Insert.insert y F']
            = Pr{let r ← sampleRandom64}[h1Input sk m r = y ∨ h1Input sk m r ∈ F'] := by
                refine prEvent_congr_of_support _ _ _ fun r _ => ?_
                simp [Finset.mem_insert]
          _ ≤ _ := prEvent_or_le _ _ _
      calc Pr{let r ← sampleRandom64}[h1Input sk m r ∈ Insert.insert y F']
          ≤ Pr{let r ← sampleRandom64}[h1Input sk m r = y] +
              Pr{let r ← sampleRandom64}[h1Input sk m r ∈ F'] := hunion
        _ ≤ ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ +
              (F'.card : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ :=
            add_le_add (prEvent_sampleRandom64_inj_eq_le (h1Input_inj_on_64 sk m) y) ih
        _ = ((Insert.insert y F').card : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
            rw [Finset.card_insert_of_notMem hy]
            push_cast
            ring

private theorem prEvent_evalNoncesDom_le (sk : Bytes) (dom : Finset Bytes) :
    ∀ (seen ms : List Bytes),
      Pr{let e ← evalNoncesDom sk dom seen ms}[e = true] ≤
        (ms.length : ℝ≥0∞) *
          (((dom.card + seen.length + ms.length : ℕ) : ℝ≥0∞) *
            ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
  classical
  intro seen ms
  induction ms generalizing seen with
  | nil =>
      simp [evalNoncesDom]
  | cons m ms ih =>
      unfold evalNoncesDom
      set forb : Finset Bytes := dom ∪ seen.toFinset
      have hforb_card : forb.card ≤ dom.card + seen.length := by
        calc (dom ∪ seen.toFinset).card
            ≤ dom.card + seen.toFinset.card := Finset.card_union_le _ _
          _ ≤ dom.card + seen.length := Nat.add_le_add_left (List.toFinset_card_le seen) _
      have hstep : ∀ r : Bytes,
          Pr{let restBad ← evalNoncesDom sk dom (h1Input sk m r :: seen) ms}[
            (decide (h1Input sk m r ∈ dom) || decide (h1Input sk m r ∈ seen) || restBad) = true] ≤
            (if h1Input sk m r ∈ forb then (1 : ℝ≥0∞) else 0) +
              (ms.length : ℝ≥0∞) *
                (((dom.card + (seen.length + 1) + ms.length : ℕ) : ℝ≥0∞) *
                  ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
        intro r
        split_ifs with hmem
        · exact (prEvent_le_one _).trans le_self_add
        · rw [zero_add]
          have hndom : decide (h1Input sk m r ∈ dom) = false := by
            rw [decide_eq_false_iff_not]; intro h; exact hmem (Finset.mem_union_left _ h)
          have hnseen : decide (h1Input sk m r ∈ seen) = false := by
            rw [decide_eq_false_iff_not]; intro h
            exact hmem (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
          simpa only [hndom, hnseen, Bool.or_self, Bool.false_or,
            List.length_cons] using ih (h1Input sk m r :: seen)
      let : MeasurableSpace Bytes := ⊤
      rw [prEvent_bind_eq_lintegral_of_discrete]
      calc _
          ≤ ∫⁻ r, ((if h1Input sk m r ∈ forb then (1 : ℝ≥0∞) else 0) +
              (ms.length : ℝ≥0∞) *
                (((dom.card + (seen.length + 1) + ms.length : ℕ) : ℝ≥0∞) *
                  ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹)) ∂𝒟[sampleRandom64] :=
            lintegral_mono fun r => by simpa only [prEvent_norm] using hstep r
        _ = (∫⁻ r, (if h1Input sk m r ∈ forb then (1 : ℝ≥0∞) else 0) ∂𝒟[sampleRandom64]) +
              (ms.length : ℝ≥0∞) *
                (((dom.card + (seen.length + 1) + ms.length : ℕ) : ℝ≥0∞) *
                  ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
            have : IsProbabilityMeasure 𝒟[sampleRandom64] := ⟨evalDist_apply_univ_eq_one _⟩
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ = Pr{let r ← sampleRandom64}[h1Input sk m r ∈ forb] +
              (ms.length : ℝ≥0∞) *
                (((dom.card + (seen.length + 1) + ms.length : ℕ) : ℝ≥0∞) *
                  ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
            congr 1
            rw [prEvent_eq_evalDist_of_discrete, ← lintegral_indicator_one MeasurableSet.of_discrete]
            refine lintegral_congr fun r => ?_
            by_cases hr : h1Input sk m r ∈ forb <;> simp [hr]
        _ ≤ (forb.card : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ +
              (ms.length : ℝ≥0∞) *
                (((dom.card + (seen.length + 1) + ms.length : ℕ) : ℝ≥0∞) *
                  ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) :=
            add_le_add (prEvent_sampleRandom64_mem_finset_le sk m forb) le_rfl
        _ ≤ ((dom.card + seen.length + (ms.length + 1) : ℕ) : ℝ≥0∞) *
              ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ +
            (ms.length : ℝ≥0∞) *
              (((dom.card + seen.length + (ms.length + 1) : ℕ) : ℝ≥0∞) *
                ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
            have h1 : forb.card ≤ dom.card + seen.length + (ms.length + 1) := by omega
            have h2 : dom.card + (seen.length + 1) + ms.length =
                dom.card + seen.length + (ms.length + 1) := by omega
            rw [h2]
            gcongr
        _ = (((m :: ms).length : ℕ) : ℝ≥0∞) *
              (((dom.card + seen.length + (m :: ms).length : ℕ) : ℝ≥0∞) *
                ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
            simp only [List.length_cons]
            push_cast
            ring

private theorem roLog_dom {β : Type} (sub : OracleComp sha512RoSpec β)
    (advC : sha512RoSpec.QueryCache) (dom₀ : Finset Bytes) :
    (simulateQ roLog sub).run (advC, dom₀, []) =
      (fun p : β × LogState => (p.1, (p.2.1, dom₀ ∪ p.2.2.1, p.2.2.2))) <$>
        (simulateQ roLog sub).run (advC, ∅, []) := by
  induction sub using OracleComp.inductionOn generalizing advC dom₀ with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [roLog_run, roLog_run, bind_map_left, bind_map_left]
      congr 1; funext p
      rw [ih p.1 p.2 (Insert.insert t dom₀), ih p.1 p.2 (Insert.insert t ∅), Functor.map_map]
      congr 1; funext z
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
      ext x
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

private theorem roStep₁_eq_map_roLog {β : Type} (sub : OracleComp sha512RoSpec β)
    (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) :
    (simulateQ roStep₁ sub).run ((advC, sigC), bad) =
      (fun p : β × LogState =>
        (p.1, ((p.2.1, sigC), bad || decide (∃ k ∈ p.2.2.1, (sigC k).isSome = true)))) <$>
        (simulateQ roLog sub).run (advC, ∅, []) := by
  induction sub using OracleComp.inductionOn generalizing advC bad with
  | pure a =>
      simp [simulateQ_pure]
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [roStep₁_run, roLog_run, bind_map_left, bind_map_left]
      congr 1; funext p
      rw [ih p.1 p.2 (bad || (sigC t).isSome), roLog_dom (cont p.1) p.2 (Insert.insert t ∅),
        Functor.map_map]
      congr 1; funext z
      refine Prod.ext rfl (Prod.ext rfl ?_)
      dsimp only
      cases hb : bad <;> cases hst : (sigC t).isSome <;>
        by_cases hex : ∃ k ∈ z.2.2.1, (sigC k).isSome = true
      · simp_all [Finset.mem_insert]
      · simp_all [Finset.mem_insert]
      · simp_all
      · simp_all
      · simp_all
      · simp_all
      · simp_all
      · simp_all

private theorem prEvent_bad_le_evalNonces {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) :
    ∀ (advC sigC : sha512RoSpec.QueryCache) (bad : Bool) (dom : Finset Bytes) (seen : List Bytes),
      (∀ k, (advC k).isSome = true → k ∈ dom) →
      (∀ k, (sigC k).isSome = true → k ∈ seen) →
      Pr{let z ← (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((advC, sigC), bad)}[
          z.2.2 = true] ≤
        Pr{let p ← (simulateQ (impl₁_log P isValidDhTriple sk) oa).run (advC, dom, []);
           let e ← evalNoncesDom sk p.2.2.1 seen p.2.2.2}[
          bad = true ∨ (∃ k ∈ seen, k ∈ p.2.2.1) ∨ e = true] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro advC sigC bad dom seen _ _
      simp only [simulateQ_pure, StateT.run_pure, evalNoncesDom, prEvent_norm]
      cases bad <;> simp
  | query_bind q cont ih =>
      intro advC sigC bad dom seen hdom hseen
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rcases q with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
      · simp only [impl₁_trk_unif, impl₁_log_unif, prEvent_norm, bind_assoc]
        refine OracleComp.prEvent_bind_mono_of_support
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) _ _ fun u _ => ?_
        simpa only [prEvent_norm, bind_assoc, pure_bind] using
          ih u advC sigC bad dom seen hdom hseen
      · simp only [impl₁_trk_prim, impl₁_log_prim, prEvent_norm, bind_assoc]
        rw [roStep₁_eq_map_roLog (primRoStep P pq) advC sigC bad,
          roLog_dom (primRoStep P pq) advC dom, bind_map_left, bind_map_left]
        refine OracleComp.prEvent_bind_mono_of_support
          ((simulateQ roLog (primRoStep P pq)).run (advC, ∅, [])) _ _ fun w hw => ?_
        have hw_dom := impl₁_log_dom_subset P isValidDhTriple sk
          (liftM (XeddsaRomOracleSpec.query (.inl (.inl (.inr pq)))))
          (advC, dom, []) hdom
          (w.1, (w.2.1, dom ∪ w.2.2.1, w.2.2.2))
          (by
            simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
              id_map, impl₁_log_prim]
            rw [roLog_dom, support_map]
            exact ⟨w, hw, rfl⟩)
        have hmsgs0 : w.2.2.2 = [] := by
          have hb := impl₁_log_card_bounds P isValidDhTriple sk
            (liftM (XeddsaRomOracleSpec.query (.inl (.inl (.inr pq)))))
            (qS := 0) (qH := 1)
            (by rw [isQueryBoundP_query_iff]; simp [isRomSigChalQuery])
            (by rw [isQueryBoundP_query_iff]; intro _; omega)
            (advC, ∅, []) w
            (by simpa [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
                  id_map, impl₁_log_prim] using hw)
          exact List.eq_nil_of_length_eq_zero (by simpa using hb.2)
        rw [hmsgs0]
        have hih_w := ih w.1 w.2.1 sigC
          (bad || decide (∃ k ∈ w.2.2.1, (sigC k).isSome = true))
          (dom ∪ w.2.2.1) seen hw_dom.2 hseen
        refine le_trans (by simpa only [prEvent_norm, bind_assoc] using hih_w) ?_
        refine OracleComp.prEvent_bind_mono_of_support
          ((simulateQ (impl₁_log P isValidDhTriple sk) (cont w.1)).run
            (w.2.1, dom ∪ w.2.2.1, [])) _ _ fun p hp => ?_
        have hp_sub := (impl₁_log_dom_subset P isValidDhTriple sk (cont w.1)
          (w.2.1, dom ∪ w.2.2.1, []) hw_dom.2 p hp).1
        refine prEvent_mono _ _ _ fun e he => ?_
        rcases he with hbad' | hhit | he_true
        · rcases Bool.or_eq_true_iff.mp hbad' with hb | hany
          · exact Or.inl hb
          · obtain ⟨k, hk_mem, hk_sig⟩ := of_decide_eq_true hany
            exact Or.inr (Or.inl ⟨k, hseen k hk_sig, hp_sub (Finset.mem_union_right _ hk_mem)⟩)
        · exact Or.inr (Or.inl hhit)
        · exact Or.inr (Or.inr he_true)
      · simp only [impl₁_trk_ro, impl₁_log_ro, prEvent_norm, bind_assoc]
        rw [roStep₁_run, roLog_run, bind_map_left, bind_map_left]
        refine OracleComp.prEvent_bind_mono_of_support ((sha512RoImpl bs).run advC) _ _
          fun w hw => ?_
        have hw_dom : ∀ k, (w.2 k).isSome = true → k ∈ Insert.insert bs dom := by
          intro k hk
          cases hc : advC bs with
          | some v =>
              rw [sha512RoImpl_run_some hc, support_pure, Set.mem_singleton_iff] at hw
              subst hw; exact Finset.mem_insert_of_mem (hdom k hk)
          | none =>
              rw [sha512RoImpl_run_none hc, support_map] at hw
              obtain ⟨v, _, rfl⟩ := hw
              by_cases hkb : k = bs
              · rw [hkb]; exact Finset.mem_insert_self bs dom
              · rw [QueryCache.cacheQuery_of_ne _ _ hkb] at hk
                exact Finset.mem_insert_of_mem (hdom k hk)
        have hih_w := ih w.1 w.2 sigC (bad || (sigC bs).isSome) (Insert.insert bs dom)
          seen hw_dom hseen
        refine le_trans (by simpa only [prEvent_norm, bind_assoc] using hih_w) ?_
        refine OracleComp.prEvent_bind_mono_of_support
          ((simulateQ (impl₁_log P isValidDhTriple sk) (cont w.1)).run
            (w.2, Insert.insert bs dom, [])) _ _ fun p hp => ?_
        have hp_sub := (impl₁_log_dom_subset P isValidDhTriple sk (cont w.1)
          (w.2, Insert.insert bs dom, []) hw_dom p hp).1
        refine prEvent_mono _ _ _ fun e he => ?_
        rcases he with hbad' | hhit | he_true
        · rcases Bool.or_eq_true_iff.mp hbad' with hb | hsig
          · exact Or.inl hb
          · exact Or.inr (Or.inl ⟨bs, hseen bs hsig, hp_sub (Finset.mem_insert_self bs dom)⟩)
        · exact Or.inr (Or.inl hhit)
        · exact Or.inr (Or.inr he_true)
      · rcases sq with ⟨m⟩
        rw [impl₁_trk_sig, impl₁_log_sig, sigTrk₁_run, sigLog_run]
        simp only [prEvent_norm, List.nil_append]
        rw [OracleComp.prEvent_bind_bind_swap_of_uniform sampleRandom64 sampleRandom64]
        refine OracleComp.prEvent_bind_mono_of_support sampleRandom64 _ _ fun h1Digest _ => ?_
        let keyData := clampScalar25519 sk
        let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
        set t₂ := P.compress (edBaseMul P (P.scalarFromWide h1Digest)) ++ capA ++ m
        have hro1_unfold : ∀ r : Bytes,
            (let s₁ : Hop1State :=
               match unionCache advC sigC (h1Input sk m r) with
               | some _ => ((advC, sigC), true)
               | none   => ((advC, sigC.cacheQuery (h1Input sk m r) h1Digest), bad)
             (roStep₁ t₂).run s₁ >>= fun p2 =>
               (fun z : α × Hop1State => z.2.2 = true) <$>
                 (simulateQ (impl₁_trk P isValidDhTriple sk)
                   (cont (xeddsaSignFromDigests P sk h1Digest p2.1))).run p2.2) =
            ((sha512RoImpl t₂).run advC >>= fun p2 =>
              let sigC₁ : sha512RoSpec.QueryCache :=
                match unionCache advC sigC (h1Input sk m r) with
                | some _ => sigC
                | none   => sigC.cacheQuery (h1Input sk m r) h1Digest
              let bad₁ : Bool :=
                match unionCache advC sigC (h1Input sk m r) with
                | some _ => true
                | none   => bad
              (fun z : α × Hop1State => z.2.2 = true) <$>
                (simulateQ (impl₁_trk P isValidDhTriple sk)
                  (cont (xeddsaSignFromDigests P sk h1Digest p2.1))).run
                  ((p2.2, sigC₁), bad₁ || (sigC₁ t₂).isSome)) := by
          intro r
          dsimp only
          cases unionCache advC sigC (h1Input sk m r) <;>
            rw [roStep₁_run, bind_map_left]
        simp_rw [hro1_unfold]
        rw [OracleComp.prEvent_bind_bind_swap_of_uniform sampleRandom64
          ((sha512RoImpl t₂).run advC)]
        refine OracleComp.prEvent_bind_mono_of_support ((sha512RoImpl t₂).run advC) _ _
          fun p2 hp2 => ?_
        set u := xeddsaSignFromDigests P sk h1Digest p2.1
        set dom' := Insert.insert t₂ dom
        have hp2_dom : ∀ k, (p2.2 k).isSome = true → k ∈ dom' := by
          intro k hk
          cases hc : advC t₂ with
          | some v =>
              rw [sha512RoImpl_run_some hc, support_pure, Set.mem_singleton_iff] at hp2
              subst hp2; exact Finset.mem_insert_of_mem (hdom k hk)
          | none =>
              rw [sha512RoImpl_run_none hc, support_map] at hp2
              obtain ⟨v, _, rfl⟩ := hp2
              by_cases hkt : k = t₂
              · subst hkt; exact Finset.mem_insert_self t₂ dom
              · rw [QueryCache.cacheQuery_of_ne _ _ hkt] at hk
                exact Finset.mem_insert_of_mem (hdom k hk)
        rw [run_impl₁_log_msgs P isValidDhTriple sk (cont u) p2.2 dom' [m], bind_map_left]
        calc prEvent (sampleRandom64 >>= fun r =>
                let sigC₁ : sha512RoSpec.QueryCache :=
                  match unionCache advC sigC (h1Input sk m r) with
                  | some _ => sigC
                  | none   => sigC.cacheQuery (h1Input sk m r) h1Digest
                let bad₁ : Bool :=
                  match unionCache advC sigC (h1Input sk m r) with
                  | some _ => true
                  | none   => bad
                (fun z : α × Hop1State => z.2.2 = true) <$>
                  (simulateQ (impl₁_trk P isValidDhTriple sk) (cont u)).run
                    ((p2.2, sigC₁), bad₁ || (sigC₁ t₂).isSome))
            ≤ prEvent (sampleRandom64 >>= fun r =>
                (simulateQ (impl₁_log P isValidDhTriple sk) (cont u)).run (p2.2, dom', []) >>=
                  fun p =>
                    (fun e : Bool => bad = true ∨ (∃ k ∈ seen, k ∈ p.2.2.1) ∨
                      (decide (h1Input sk m r ∈ p.2.2.1) || decide (h1Input sk m r ∈ seen) || e) =
                        true) <$>
                      evalNoncesDom sk p.2.2.1 (h1Input sk m r :: seen) p.2.2.2) := by
              refine OracleComp.prEvent_bind_mono_of_support sampleRandom64 _ _ fun r _ => ?_
              set t₁ := h1Input sk m r
              cases hu : unionCache advC sigC t₁ with
              | some v =>
                  dsimp only
                  simp only [Bool.true_or]
                  have hseen₁ : ∀ k, (sigC k).isSome = true → k ∈ t₁ :: seen :=
                    fun k hk => List.mem_cons_of_mem t₁ (hseen k hk)
                  have hih_r := ih u p2.2 sigC true dom' (t₁ :: seen) hp2_dom hseen₁
                  refine le_trans (by simpa only [prEvent_norm] using hih_r) ?_
                  refine OracleComp.prEvent_bind_mono_of_support
                    ((simulateQ (impl₁_log P isValidDhTriple sk) (cont u)).run (p2.2, dom', [])) _ _
                    fun p hp => ?_
                  have hp_sub := (impl₁_log_dom_subset P isValidDhTriple sk (cont u)
                    (p2.2, dom', []) hp2_dom p hp).1
                  have ht1_or : t₁ ∈ p.2.2.1 ∨ t₁ ∈ seen := by
                    simp only [unionCache, QueryCache.ofFn_apply] at hu
                    cases hs : sigC t₁ with
                    | some _ => exact Or.inr (hseen t₁ (by simp [hs]))
                    | none =>
                        rw [hs] at hu
                        have ha : (advC t₁).isSome = true := by simp [hu]
                        exact Or.inl (hp_sub (Finset.mem_insert_of_mem (hdom t₁ ha)))
                  refine prEvent_mono _ _ _ fun e _ => ?_
                  rcases ht1_or with ht1_dom | ht1_seen
                  · exact Or.inr (Or.inr (by simp [ht1_dom]))
                  · exact Or.inr (Or.inr (by simp [ht1_seen]))
              | none =>
                  dsimp only
                  set sigC₁ : sha512RoSpec.QueryCache := sigC.cacheQuery t₁ h1Digest
                  have hseen₁ : ∀ k, (sigC₁ k).isSome = true → k ∈ t₁ :: seen := by
                    intro k hk
                    by_cases hkt : k = t₁
                    · rw [hkt]; exact List.mem_cons_self
                    · rw [QueryCache.cacheQuery_of_ne _ _ hkt] at hk
                      exact List.mem_cons_of_mem t₁ (hseen k hk)
                  have hih_r := ih u p2.2 sigC₁ (bad || (sigC₁ t₂).isSome) dom' (t₁ :: seen)
                    hp2_dom hseen₁
                  refine le_trans (by simpa only [prEvent_norm] using hih_r) ?_
                  refine OracleComp.prEvent_bind_mono_of_support
                    ((simulateQ (impl₁_log P isValidDhTriple sk) (cont u)).run (p2.2, dom', [])) _ _
                    fun p hp => ?_
                  have hp_sub := (impl₁_log_dom_subset P isValidDhTriple sk (cont u)
                    (p2.2, dom', []) hp2_dom p hp).1
                  have ht2_or : (sigC₁ t₂).isSome = true →
                      t₁ ∈ p.2.2.1 ∨ (∃ k ∈ seen, k ∈ p.2.2.1) := by
                    intro hs2
                    have ht2_mem : t₂ ∈ p.2.2.1 := hp_sub (Finset.mem_insert_self t₂ dom)
                    rcases List.mem_cons.mp (hseen₁ t₂ hs2) with heq | hmem_seen
                    · exact Or.inl (heq ▸ ht2_mem)
                    · exact Or.inr ⟨t₂, hmem_seen, ht2_mem⟩
                  refine prEvent_mono _ _ _ fun e he => ?_
                  rcases he with hbad2 | ⟨k, hk_cons, hk_dom⟩ | he_true
                  · rcases Bool.or_eq_true_iff.mp hbad2 with hb | hs2
                    · exact Or.inl hb
                    · rcases ht2_or hs2 with ht1_dom | hhit
                      · exact Or.inr (Or.inr (by simp [ht1_dom]))
                      · exact Or.inr (Or.inl hhit)
                  · rcases List.mem_cons.mp hk_cons with rfl | hk_seen
                    · exact Or.inr (Or.inr (by simp [hk_dom]))
                    · exact Or.inr (Or.inl ⟨k, hk_seen, hk_dom⟩)
                  · exact Or.inr (Or.inr (by simp [he_true]))
          _ = prEvent ((simulateQ (impl₁_log P isValidDhTriple sk) (cont u)).run (p2.2, dom', []) >>=
                fun p =>
                  (fun e : Bool => bad = true ∨ (∃ k ∈ seen, k ∈ p.2.2.1) ∨ e = true) <$>
                    evalNoncesDom sk p.2.2.1 seen ([m] ++ p.2.2.2)) := by
              rw [OracleComp.prEvent_bind_bind_swap_of_uniform sampleRandom64
                ((simulateQ (impl₁_log P isValidDhTriple sk) (cont u)).run (p2.2, dom', []))]
              refine OracleComp.prEvent_bind_congr_of_support _ _ _ fun p _ => ?_
              simp only [List.singleton_append, evalNoncesDom, prEvent_norm]
      · simp only [impl₁_trk_ddh, impl₁_log_ddh, StateT.run_pure, pure_bind]
        exact ih (isValidDhTriple X Y Z) advC sigC bad dom seen hdom hseen

private theorem measureETVDist_hop1_le {α : Type}
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) {qS qH : ℕ}
    (hqS : oa.IsQueryBoundP (fun q => isRomSigChalQuery q = true) qS)
    (hqH : oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true) qH) :
    letI : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
    measureETVDist
      (Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅)
      (Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅) ≤
      ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512) := by
  let : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
  let : MeasurableSpace (α × Hop1State) := ⊤
  let fProj : α × Hop1State → α × sha512RoSpec.QueryCache :=
    fun z => (z.1, projNonH1 z.2.1.1)
  have hL : 𝒟[Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅] =
      𝒟[fProj <$> (simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)] :=
    (evalDistEq_proj_impl₀_trk P isValidDhTriple sk oa).symm.evalDist_eq
  have hR : 𝒟[Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅] =
      𝒟[fProj <$> (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)] := by
    have h1 := (evalDistEq_proj_impl₁_trk P isValidDhTriple sk oa ((∅, ∅), false)).symm.map
      (Prod.map id projNonH1)
    rw [Functor.map_map] at h1
    exact h1.evalDist_eq
  have htv_trk : measureETVDist
      ((simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false))
      ((simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)) ≤
      Pr{let z ← (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)}[
        z.2.2 = true] := by
    rw [← OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq
      (impl₀_trk P isValidDhTriple sk) (impl₁_trk P isValidDhTriple sk)
      (fun s => s.2 = true)
      (impl_trk_agree P isValidDhTriple sk)
      (impl₀_trk_mono P isValidDhTriple sk)
      (impl₁_trk_mono P isValidDhTriple sk) oa ((∅, ∅), false)]
    exact OracleComp.ProgramLogic.Relational.measureETVDist_simulateQ_run_le_prEvent_bad
      (impl₀_trk P isValidDhTriple sk) (impl₁_trk P isValidDhTriple sk)
      (fun s => s.2 = true)
      (impl_trk_agree P isValidDhTriple sk)
      (impl₀_trk_mono P isValidDhTriple sk)
      (impl₁_trk_mono P isValidDhTriple sk) oa ((∅, ∅), false)
  have hbad_bound :
      Pr{let z ← (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)}[
        z.2.2 = true] ≤
        ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512) := by
    refine (prEvent_bad_le_evalNonces P isValidDhTriple sk oa ∅ ∅ false ∅ []
      (fun k hk => by simp at hk) (fun k hk => by simp at hk)).trans ?_
    have hbind := prEvent_bind_le_of_forall_le_of_support
      ((simulateQ (impl₁_log P isValidDhTriple sk) oa).run (∅, ∅, []))
      (fun p => (fun e : Bool => false = true ∨ (∃ k ∈ ([] : List Bytes), k ∈ p.2.2.1) ∨ e = true) <$>
        evalNoncesDom sk p.2.2.1 [] p.2.2.2)
      id
      (ε := ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512))
      (fun p hp => by
        obtain ⟨hdom_le, hlen_le⟩ :=
          impl₁_log_card_bounds P isValidDhTriple sk oa hqS hqH (∅, ∅, []) p hp
        simp only [Finset.card_empty, Nat.zero_add, List.length_nil] at hdom_le hlen_le
        have hsimp_ev :
            Pr{let y ← (fun e : Bool => false = true ∨ (∃ k ∈ ([] : List Bytes), k ∈ p.2.2.1) ∨
                e = true) <$> evalNoncesDom sk p.2.2.1 [] p.2.2.2}[id y] =
            Pr{let e ← evalNoncesDom sk p.2.2.1 [] p.2.2.2}[e = true] := by
          simp only [prEvent_norm, id_eq]
          refine prEvent_congr_of_support _ _ _ fun e _ => ?_
          simp
        rw [hsimp_ev]
        refine (prEvent_evalNoncesDom_le sk p.2.2.1 [] p.2.2.2).trans ?_
        simp only [List.length_nil, Nat.add_zero]
        have hsum_le : p.2.2.1.card + p.2.2.2.length ≤ 2 * qH + 3 * qS := by omega
        calc (p.2.2.2.length : ℝ≥0∞) *
              (((p.2.2.1.card + p.2.2.2.length : ℕ) : ℝ≥0∞) *
                ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹)
            ≤ (qS : ℝ≥0∞) * (((2 * qH + 3 * qS : ℕ) : ℝ≥0∞) *
                ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹) := by
              gcongr
          _ = ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512) := by
              have hden_pos : (0 : ℝ) < (2 : ℝ) ^ 512 := by positivity
              rw [ENNReal.ofReal_div_of_pos hden_pos, div_eq_mul_inv,
                ENNReal.ofReal_mul (Nat.cast_nonneg qS), mul_assoc, ENNReal.ofReal_natCast]
              congr 2
              · have hcast : ((2 * qH + 3 * qS : ℕ) : ℝ) = 2 * (qH : ℝ) + 3 * (qS : ℝ) := by
                  push_cast; ring
                rw [← hcast, ENNReal.ofReal_natCast]
              · congr 1
                have hpow : ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ) = (2 : ℝ) ^ 512 := by
                  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
                rw [← hpow, ENNReal.ofReal_natCast])
    simpa only [prEvent_norm, id_eq] using hbind
  calc measureETVDist
        (Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅)
        (Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅)
      = Measure.etvDist
          𝒟[Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅]
          𝒟[Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅] := rfl
    _ = Measure.etvDist
          𝒟[fProj <$> (simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)]
          𝒟[fProj <$> (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)] := by
          rw [hL, hR]
    _ = measureETVDist
          (fProj <$> (simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false))
          (fProj <$> (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)) := rfl
    _ ≤ measureETVDist
          ((simulateQ (impl₀_trk P isValidDhTriple sk) oa).run ((∅, ∅), false))
          ((simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)) :=
          measureETVDist_map_le _ _ fProj Measurable.of_discrete
    _ ≤ Pr{let z ← (simulateQ (impl₁_trk P isValidDhTriple sk) oa).run ((∅, ∅), false)}[
          z.2.2 = true] := htv_trk
    _ ≤ ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512) := hbad_bound

/-! ## Wide modular reduction and Schnorr HVZK random-oracle programming -/

private theorem uint8_ofNat_toNat_eq (b : UInt8) : UInt8.ofNat b.toNat = b :=
  UInt8.toNat_inj.mp (UInt8.toNat_ofNat_of_lt' b.toBitVec.isLt)

private theorem uint8_shift_signBit_roundtrip (b : UInt8) :
    (((b &&& 0x80) >>> 7) &&& 1) <<< 7 = (b &&& 0x80) := by
  have hcheck : ∀ i : Fin 256,
      (((UInt8.ofNat i.val &&& 0x80) >>> 7) &&& 1) <<< 7 = (UInt8.ofNat i.val &&& 0x80) := by
    decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

private theorem uint8_shift_signBit_bool (b : UInt8) :
    ((b &&& 0x80) >>> 7) = 0 ∨ ((b &&& 0x80) >>> 7) = 1 := by
  have hcheck : ∀ i : Fin 256,
      ((UInt8.ofNat i.val &&& 0x80) >>> 7) = 0 ∨ ((UInt8.ofNat i.val &&& 0x80) >>> 7) = 1 := by
    decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

private noncomputable def sigRoImpl₃ (P : Primitives) (pk : Bytes) (bSim : UInt8) :
    QueryImpl sigOracleSpec Sha512RoComp :=
  fun (.sign m) => xeddsaSimSign P pk bSim m

private noncomputable def impl₃ (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pk : Bytes) (bSim : UInt8) :
    QueryImpl XeddsaRomOracleSpec Sha512RoComp :=
  primBaseRoImpl P + (sigRoImpl₃ P pk bSim + ddhRoImpl isValidDhTriple)

@[simp]
private theorem impl₃_unif (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (n : ℕ) (c : sha512RoSpec.QueryCache) :
    (impl₃ P isValidDhTriple pk bSim (.inl (.inl (.inl n)))).run c =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, c)) := rfl

@[simp]
private theorem impl₃_prim (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (pq : PrimQuery) :
    impl₃ P isValidDhTriple pk bSim (.inl (.inl (.inr pq))) =
      simulateQ sha512RoImpl (primRoStep P pq) := rfl

@[simp]
private theorem impl₃_ro (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (bs : Bytes) :
    impl₃ P isValidDhTriple pk bSim (.inl (.inr bs)) = sha512RoImpl bs := rfl

@[simp]
private theorem impl₃_sig (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (m : Bytes) :
    impl₃ P isValidDhTriple pk bSim (.inr (.inl (.sign m))) = xeddsaSimSign P pk bSim m := rfl

@[simp]
private theorem impl₃_ddh (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pk : Bytes) (bSim : UInt8) (X Y Z : Bytes) :
    impl₃ P isValidDhTriple pk bSim (.inr (.inr (X, Y, Z))) =
      pure (isValidDhTriple X Y Z) := rfl

private theorem xeddsaSimSign_run (P : Primitives) (pk : Bytes) (bSim : UInt8) (m : Bytes)
    (c : sha512RoSpec.QueryCache) :
    (xeddsaSimSign P pk bSim m).run c =
      (let edPk := (P.montToEd pk bSim).getD (edDummy P)
       let capA := P.compress edPk
       let minusCapA := P.edNeg edPk
       ($ᵗ (ZMod l25519)) >>= fun sVal =>
         sampleRandom64 >>= fun hDigest =>
           let h := P.scalarFromWide hDigest
           let s := encodeScalarBytes sVal
           let capR := P.compress (P.doubleScalarMulBasepoint h minusCapA s)
           let signBitByte : UInt8 := (bSim &&& 1) <<< 7
           let c' := match c (capR ++ capA ++ m) with
             | some _ => c
             | none   => c.cacheQuery (capR ++ capA ++ m) hDigest
           pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], c')) := by
  unfold xeddsaSimSign
  simp [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_modify,
    bind_pure_comp, map_pure]

private theorem evalDistEq_bind_bind_swap_probComp {α β γ : Type}
    (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    (mx >>= fun a => my >>= fun b => f a b) =ᵈ
      (my >>= fun b => mx >>= fun a => f a b) :=
  let : MeasurableSpace γ := ⊤
  EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_bind_swap_of_uniform mx my f)

private theorem prEvent_uniform_zmod_hit_cache_le
    (c : sha512RoSpec.QueryCache) {g : ZMod l25519 → Bytes} (hg : Function.Injective g) :
    letI : MeasurableSpace (ZMod l25519) := ⊤
    𝒟[$ᵗ (ZMod l25519)] {rVal : ZMod l25519 | (c (g rVal)).isSome = true} ≤
      c.enncard * (l25519 : ℝ≥0∞)⁻¹ := by
  classical
  let : MeasurableSpace (ZMod l25519) := ⊤
  rw [← prEvent_eq_evalDist_of_discrete, SampleableType.prEvent_uniformSample, ZMod.card,
    div_eq_mul_inv]
  set F : Finset (ZMod l25519) := Finset.univ.filter (fun rVal => (c (g rVal)).isSome = true)
  have hencard : (F.card : ℕ∞) ≤ c.toSet.encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard F]
    refine Set.encard_le_encard_of_injOn (f := fun rVal => ⟨g rVal, (c (g rVal)).getD []⟩)
      (fun rVal hr => ?_) (fun r1 _ r2 _ heq => ?_)
    · simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hr
      simp [QueryCache.mem_toSet, hv]
    · exact hg (congrArg Sigma.fst heq)
  have henncard : (F.card : ℝ≥0∞) ≤ c.enncard := by
    unfold QueryCache.enncard
    exact_mod_cast hencard
  exact mul_le_mul_of_nonneg_right henncard zero_le

private theorem measureETVDist_sig_hop23_step
    (P : Primitives) (C : XeddsaCurveWitness P) (sk m : Bytes)
    (c : sha512RoSpec.QueryCache) :
    letI : MeasurableSpace (Bytes × sha512RoSpec.QueryCache) := ⊤
    measureETVDist
      ((sigRoImpl₁ P sk (.sign m)).run c)
      ((xeddsaSimSign P (P.x25519Base sk) (C.edSign (clampedScalarZMod sk)) m).run c) ≤
      ENNReal.ofReal deltaWide + (projNonH1 c).enncard * (l25519 : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (Bytes × sha512RoSpec.QueryCache) := ⊤
  let : MeasurableSpace (ZMod l25519) := ⊤
  set aScalar : ZMod l25519 := clampedScalarZMod sk
  set bSim : UInt8 := C.edSign aScalar
  set capA : Bytes := C.compressEd aScalar
  set signBitByte : UInt8 := (bSim &&& 1) <<< 7
  have ha_eq : P.scalarFromBytesModOrder (clampScalar25519 sk) = encodeScalarBytes aScalar := by
    rw [C.scalarMod_eq, fitBytesRef_of_length_eq (clampScalar25519_length sk)]
    rfl
  have hcapA_honest :
      P.compress (edBaseMul P (P.scalarFromBytesModOrder (clampScalar25519 sk))) = capA := by
    rw [ha_eq, compress_edBaseMul C]
  have hsignBitByte_honest : (capA.getD 31 0 &&& 0x80) = signBitByte := by
    dsimp only [signBitByte, bSim, capA]
    rw [← C.compressEd_signBit aScalar, uint8_shift_signBit_roundtrip]
  let rStep : ZMod l25519 → ProbComp (Bytes × sha512RoSpec.QueryCache) := fun rVal =>
    let capR := C.compressEd rVal
    (sha512RoImpl (capR ++ capA ++ m)).run c >>= fun p2 =>
      let h := P.scalarFromWide p2.1
      let s := P.scalarAdd (P.scalarMul h (encodeScalarBytes aScalar)) (encodeScalarBytes rVal)
      pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], p2.2)
  let rStepSim : ZMod l25519 → ProbComp (Bytes × sha512RoSpec.QueryCache) := fun rVal =>
    let capR := C.compressEd rVal
    sampleRandom64 >>= fun hDigest =>
      let c' := match c (capR ++ capA ++ m) with
        | some _ => c
        | none   => c.cacheQuery (capR ++ capA ++ m) hDigest
      let h := P.scalarFromWide hDigest
      let s := P.scalarAdd (P.scalarMul h (encodeScalarBytes aScalar)) (encodeScalarBytes rVal)
      pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], c')
  have hL_eq : (sigRoImpl₁ P sk (.sign m)).run c =ᵈ
      ((decodeScalarBytes <$> sampleRandom64) >>= rStep) := by
    rw [sigRoImpl₁_run, bind_map_left]
    refine EvalDistEq.of_forall_prEvent_eq fun ev => ?_
    rw [map_bind, map_bind]
    refine OracleComp.prEvent_bind_congr_of_support sampleRandom64 _ _ fun h1Digest hh1 => ?_
    have hh1_len := sampleRandom64_length hh1
    have hr_eq : P.scalarFromWide h1Digest = encodeScalarBytes (decodeScalarBytes h1Digest) := by
      rw [C.scalarWide_eq, fitBytesRef_of_length_eq hh1_len]
    have hcapR_eq : P.compress (edBaseMul P (P.scalarFromWide h1Digest)) =
        C.compressEd (decodeScalarBytes h1Digest) := by
      rw [hr_eq, compress_edBaseMul C]
    have hbody_eq :
        ((sha512RoImpl
            (P.compress (edBaseMul P (P.scalarFromWide h1Digest)) ++
              P.compress (edBaseMul P (P.scalarFromBytesModOrder (clampScalar25519 sk))) ++ m)).run c
          >>= fun p2 => pure (xeddsaSignFromDigests P sk h1Digest p2.1, p2.2)) =
        rStep (decodeScalarBytes h1Digest) := by
      dsimp only [rStep, xeddsaSignFromDigests]
      rw [hcapA_honest, hcapR_eq]
      congr 1; funext p2
      rw [ha_eq, hr_eq, hsignBitByte_honest]
    rw [hbody_eq]
  obtain ⟨edPk, hmont, hrep_raw⟩ := C.montToEd_base sk bSim (C.edSign_bool aScalar)
  have hrep_edPk : C.RepresentsEd aScalar edPk := by
    simpa only [bSim, aScalar, beq_self_eq_true, ↓reduceIte] using hrep_raw
  have hgetD_edPk : (P.montToEd (P.x25519Base sk) bSim).getD (edDummy P) = edPk := by
    rw [hmont]; rfl
  have hcomp_edPk : P.compress edPk = capA := C.compress_of_represents hrep_edPk
  have hrep_neg : C.RepresentsEd (-aScalar) (P.edNeg edPk) := C.edNeg_represents hrep_edPk
  have hR_eq :
      (xeddsaSimSign P (P.x25519Base sk) bSim m).run c =ᵈ (($ᵗ (ZMod l25519)) >>= rStepSim) := by
    rw [xeddsaSimSign_run]
    dsimp only
    rw [hgetD_edPk, hcomp_edPk]
    refine (evalDistEq_bind_bind_swap_probComp ($ᵗ (ZMod l25519)) sampleRandom64 _).trans ?_
    have hinner :
        (sampleRandom64 >>= fun hDigest =>
          ($ᵗ (ZMod l25519)) >>= fun sVal =>
            let h := P.scalarFromWide hDigest
            let s := encodeScalarBytes sVal
            let capR := P.compress (P.doubleScalarMulBasepoint h (P.edNeg edPk) s)
            let c' := match c (capR ++ capA ++ m) with
              | some _ => c
              | none   => c.cacheQuery (capR ++ capA ++ m) hDigest
            pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], c')) =ᵈ
        (sampleRandom64 >>= fun hDigest =>
          ($ᵗ (ZMod l25519)) >>= fun rVal =>
            let capR := C.compressEd rVal
            let c' := match c (capR ++ capA ++ m) with
              | some _ => c
              | none   => c.cacheQuery (capR ++ capA ++ m) hDigest
            let h := P.scalarFromWide hDigest
            let s := P.scalarAdd (P.scalarMul h (encodeScalarBytes aScalar)) (encodeScalarBytes rVal)
            pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], c')) := by
      refine EvalDistEq.of_forall_prEvent_eq fun ev => ?_
      rw [map_bind, map_bind]
      refine OracleComp.prEvent_bind_congr_of_support sampleRandom64 _ _ fun hDigest hh => ?_
      have hh_len := sampleRandom64_length hh
      set hScalar : ZMod l25519 := decodeScalarBytes hDigest
      have hh_eq : P.scalarFromWide hDigest = encodeScalarBytes hScalar := by
        rw [C.scalarWide_eq, fitBytesRef_of_length_eq hh_len]
      have hbij :
          ((fun rVal : ZMod l25519 => hScalar * aScalar + rVal) <$> ($ᵗ (ZMod l25519))) =ᵈ
            ($ᵗ (ZMod l25519)) :=
        SampleableType.map_uniformSample_evalDistEq_of_bijective
          (Equiv.addLeft (hScalar * aScalar)).bijective
      have hsub := (hbij.symm.bind fun sVal => EvalDistEq.refl
        (let h := P.scalarFromWide hDigest
         let s := encodeScalarBytes sVal
         let capR := P.compress (P.doubleScalarMulBasepoint h (P.edNeg edPk) s)
         let c' := match c (capR ++ capA ++ m) with
           | some _ => c
           | none   => c.cacheQuery (capR ++ capA ++ m) hDigest
         pure (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte], c'))).prEvent_eq ev
      rw [bind_map_left] at hsub
      refine hsub.trans ?_
      rw [map_bind, map_bind]
      refine OracleComp.prEvent_bind_congr_of_support ($ᵗ (ZMod l25519)) _ _ fun rVal _ => ?_
      dsimp only
      have hdsmb :
          P.compress (P.doubleScalarMulBasepoint (P.scalarFromWide hDigest) (P.edNeg edPk)
              (encodeScalarBytes (hScalar * aScalar + rVal))) =
            C.compressEd rVal := by
        rw [hh_eq, C.compress_of_represents (C.dsmb_represents hScalar _ hrep_neg)]
        congr 1; ring
      have hs_eq :
          encodeScalarBytes (hScalar * aScalar + rVal) =
            P.scalarAdd (P.scalarMul (P.scalarFromWide hDigest) (encodeScalarBytes aScalar))
              (encodeScalarBytes rVal) := by
        rw [hh_eq, C.scalarMul_eq, C.scalarAdd_eq]
      rw [hdsmb, hs_eq]
    exact hinner.trans (evalDistEq_bind_bind_swap_probComp sampleRandom64 ($ᵗ (ZMod l25519)) _)
  have hhop2 :
      measureETVDist ((decodeScalarBytes <$> sampleRandom64) >>= rStep)
        (($ᵗ (ZMod l25519)) >>= rStep) ≤ ENNReal.ofReal deltaWide :=
    (measureETVDist_bind_le (decodeScalarBytes <$> sampleRandom64) ($ᵗ (ZMod l25519)) rStep
      Measurable.of_discrete).trans measureETVDist_decode_sampleRandom64_zmod
  set badSet : Set (ZMod l25519) :=
    {rVal | (projNonH1 c (C.compressEd rVal ++ capA ++ m)).isSome = true}
  have hhop3 :
      measureETVDist (($ᵗ (ZMod l25519)) >>= rStep) (($ᵗ (ZMod l25519)) >>= rStepSim) ≤
        (projNonH1 c).enncard * (l25519 : ℝ≥0∞)⁻¹ := by
    have hbad_le := measureETVDist_bind_bind_le_of_bad ($ᵗ (ZMod l25519)) rStep rStepSim
      Measurable.of_discrete Measurable.of_discrete (bad := badSet) MeasurableSet.of_discrete 0
      (Filter.Eventually.of_forall fun rVal hnotbad => by
        have hisH1 : isH1 (C.compressEd rVal ++ capA ++ m) = false := by
          rw [List.append_assoc]
          exact isH1_eq_false_of_inRange (C.compressEd_len rVal) (C.compressEd_inRange rVal)
        have hc_none : c (C.compressEd rVal ++ capA ++ m) = none := by
          change ¬ (projNonH1 c (C.compressEd rVal ++ capA ++ m)).isSome = true at hnotbad
          rw [projNonH1_apply] at hnotbad
          simp only [hisH1, Bool.false_eq_true, ↓reduceIte] at hnotbad
          cases hct : c (C.compressEd rVal ++ capA ++ m)
          · rfl
          · exfalso; exact hnotbad (by simp [hct])
        have hstep_eq : rStep rVal = rStepSim rVal := by
          dsimp only [rStep, rStepSim]
          rw [sha512RoImpl_run_none hc_none, bind_map_left, hc_none]
        rw [hstep_eq, measureETVDist_self])
    rw [zero_mul, add_zero] at hbad_le
    refine hbad_le.trans (prEvent_uniform_zmod_hit_cache_le (projNonH1 c) ?_)
    intro r1 r2 heq
    have h1 := List.append_cancel_right heq
    have h2 := List.append_cancel_right h1
    exact C.compressEd_inj h2
  calc measureETVDist ((sigRoImpl₁ P sk (.sign m)).run c)
        ((xeddsaSimSign P (P.x25519Base sk) bSim m).run c)
      = Measure.etvDist 𝒟[(sigRoImpl₁ P sk (.sign m)).run c]
          𝒟[(xeddsaSimSign P (P.x25519Base sk) bSim m).run c] := rfl
    _ = Measure.etvDist 𝒟[(decodeScalarBytes <$> sampleRandom64) >>= rStep]
          𝒟[($ᵗ (ZMod l25519)) >>= rStepSim] := by
          rw [hL_eq.evalDist_eq, hR_eq.evalDist_eq]
    _ = measureETVDist ((decodeScalarBytes <$> sampleRandom64) >>= rStep)
          (($ᵗ (ZMod l25519)) >>= rStepSim) := rfl
    _ ≤ measureETVDist ((decodeScalarBytes <$> sampleRandom64) >>= rStep)
          (($ᵗ (ZMod l25519)) >>= rStep) +
        measureETVDist (($ᵗ (ZMod l25519)) >>= rStep)
          (($ᵗ (ZMod l25519)) >>= rStepSim) := measureETVDist_triangle _ _ _
    _ ≤ ENNReal.ofReal deltaWide + (projNonH1 c).enncard * (l25519 : ℝ≥0∞)⁻¹ :=
          add_le_add hhop2 hhop3

private def liftNoBad (impl : QueryImpl XeddsaRomOracleSpec Sha512RoComp) :
    QueryImpl XeddsaRomOracleSpec (StateT (sha512RoSpec.QueryCache × Bool) ProbComp) :=
  fun q => StateT.mk fun (c, b) =>
    (fun z : XeddsaRomOracleSpec.Range q × sha512RoSpec.QueryCache => (z.1, (z.2, b))) <$>
      (impl q).run c

private theorem liftNoBad_run (impl : QueryImpl XeddsaRomOracleSpec Sha512RoComp)
    (q : XeddsaRomOracleSpec.Domain) (c : sha512RoSpec.QueryCache) (b : Bool) :
    (liftNoBad impl q).run (c, b) =
      (fun z : XeddsaRomOracleSpec.Range q × sha512RoSpec.QueryCache => (z.1, (z.2, b))) <$>
        (impl q).run c := rfl

private theorem simulateQ_liftNoBad_proj {α : Type}
    (impl : QueryImpl XeddsaRomOracleSpec Sha512RoComp)
    (oa : OracleComp XeddsaRomOracleSpec α) (c : sha512RoSpec.QueryCache) (b : Bool) :
    Prod.map id Prod.fst <$> (simulateQ (liftNoBad impl) oa).run (c, b) =
      (simulateQ impl oa).run c := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (liftNoBad impl) impl Prod.fst ?_ oa (c, b)
  intro q ⟨c', b'⟩
  rw [liftNoBad_run, Functor.map_map]
  exact id_map _

private theorem liftNoBad_mono (impl : QueryImpl XeddsaRomOracleSpec Sha512RoComp) :
    ∀ (t : XeddsaRomOracleSpec.Domain) (p : sha512RoSpec.QueryCache × Bool), p.2 = true →
      ∀ z ∈ support ((liftNoBad impl t).run p), z.2.2 = true := by
  intro t ⟨c, b⟩ hb z hz
  dsimp only at hb; subst hb
  rw [liftNoBad_run, support_map] at hz
  obtain ⟨_, _, rfl⟩ := hz; rfl

private theorem prEvent_liftNoBad_bad_eq_zero {α : Type}
    (impl : QueryImpl XeddsaRomOracleSpec Sha512RoComp)
    (oa : OracleComp XeddsaRomOracleSpec α) (c : sha512RoSpec.QueryCache) :
    Pr{let z ← (simulateQ (liftNoBad impl) oa).run (c, false)}[z.2.2 = true] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz htrue => ?_
  have hfalse : z.2.2 = false :=
    OracleComp.ProgramLogic.Relational.forall_mem_support_simulateQ_run_of_bad
      (liftNoBad impl) (fun p => p.2 = false)
      (fun t ⟨c', b'⟩ hb' w hw => by
        dsimp only at hb'; subst hb'
        rw [liftNoBad_run, support_map] at hw
        obtain ⟨_, _, rfl⟩ := hw; rfl)
      oa rfl z hz
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

private theorem sha512RoImpl_projNonH1_enncard_le
    (t : Bytes) (c : sha512RoSpec.QueryCache)
    {w : Bytes × sha512RoSpec.QueryCache} (hw : w ∈ support ((sha512RoImpl t).run c)) :
    (projNonH1 w.2).enncard ≤ (projNonH1 c).enncard + 1 := by
  cases hct : c t with
  | some v =>
      rw [sha512RoImpl_run_some hct, support_pure, Set.mem_singleton_iff] at hw
      subst hw; exact le_self_add
  | none =>
      rw [sha512RoImpl_run_none hct, support_map] at hw
      obtain ⟨v, _, rfl⟩ := hw
      exact projNonH1_enncard_cacheQuery_le c t v

private theorem sha512RoImpl_projNonH1_enncard_eq_of_isH1
    {t : Bytes} (ht : isH1 t = true) (c : sha512RoSpec.QueryCache)
    {w : Bytes × sha512RoSpec.QueryCache} (hw : w ∈ support ((sha512RoImpl t).run c)) :
    (projNonH1 w.2).enncard = (projNonH1 c).enncard := by
  cases hct : c t with
  | some v =>
      rw [sha512RoImpl_run_some hct, support_pure, Set.mem_singleton_iff] at hw
      subst hw; rfl
  | none =>
      rw [sha512RoImpl_run_none hct, support_map] at hw
      obtain ⟨v, _, rfl⟩ := hw
      exact projNonH1_enncard_cacheQuery_of_isH1 c ht v

private theorem impl₁_resource_growth
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ (t : XeddsaRomOracleSpec.Domain) (p : sha512RoSpec.QueryCache × Bool), p.2 = false →
      isRomSigChalQuery t = true ∨ isRomGrowthQuery t = true →
      ∀ z ∈ support ((liftNoBad (impl₁ P isValidDhTriple sk) t).run p),
        (projNonH1 z.2.1).enncard ≤ (projNonH1 p.1).enncard + 1 := by
  intro t ⟨c, b⟩ hb hpred z hz
  dsimp only at hb; subst hb
  rw [liftNoBad_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  dsimp only
  rcases t with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
      isRomPrimVerifyQuery, isRomPrimSigSignQuery] at hpred
  · rw [impl₁_prim] at hw
    cases pq with
    | sigSign sk' m' r' =>
        dsimp only [primRoStep] at hw
        rw [simulateQ_sha512RoImpl_xeddsaSignRo_run, mem_support_bind_iff] at hw
        obtain ⟨p1, hp1, hw⟩ := hw
        rw [mem_support_bind_iff] at hw
        obtain ⟨p2, hp2, hw⟩ := hw
        simp only [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        have hp1_eq := sha512RoImpl_projNonH1_enncard_eq_of_isH1 (h1Input_isH1 sk' m' r') c hp1
        exact hp1_eq ▸ sha512RoImpl_projNonH1_enncard_le _ p1.2 (w := p2) hp2
    | sigVerify pk' m' sg' =>
        dsimp only [primRoStep] at hw
        unfold xeddsaVerifyRo at hw
        split_ifs at hw
        · dsimp only at hw
          cases hmont : P.montToEd pk' ((sg'.getD 63 0 &&& 0x80) >>> 7) with
          | none =>
              rw [hmont] at hw
              simp only [simulateQ_pure, StateT.run_pure, support_pure,
                Set.mem_singleton_iff] at hw
              subst hw; exact le_self_add
          | some edPk =>
              rw [hmont] at hw
              dsimp only at hw
              simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
                OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure,
                StateT.run_pure, mem_support_bind_iff, support_pure,
                Set.mem_singleton_iff] at hw
              obtain ⟨p1, hp1, rfl⟩ := hw
              exact sha512RoImpl_projNonH1_enncard_le _ c (w := p1) hp1
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
          subst hw; exact le_self_add
    | _ =>
        simp [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
          isRomPrimVerifyQuery, isRomPrimSigSignQuery] at hpred
  · rw [impl₁_ro] at hw
    exact sha512RoImpl_projNonH1_enncard_le bs c hw
  · rcases sq with ⟨m⟩
    rw [impl₁_sig, sigRoImpl₁_run, mem_support_bind_iff] at hw
    obtain ⟨h1Digest, _, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨p2, hp2, hw⟩ := hw
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact sha512RoImpl_projNonH1_enncard_le _ c (w := p2) hp2
  · simp [isRomSigChalQuery, isRomGrowthQuery, isRomDirectRoQuery,
      isRomPrimVerifyQuery, isRomPrimSigSignQuery] at hpred

private theorem impl₁_resource_free
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ (t : XeddsaRomOracleSpec.Domain) (p : sha512RoSpec.QueryCache × Bool), p.2 = false →
      ¬ isRomSigChalQuery t = true → ¬ isRomGrowthQuery t = true →
      ∀ z ∈ support ((liftNoBad (impl₁ P isValidDhTriple sk) t).run p),
        (projNonH1 z.2.1).enncard ≤ (projNonH1 p.1).enncard := by
  intro t ⟨c, b⟩ hb hnotS hnotG z hz
  dsimp only at hb; subst hb
  rw [liftNoBad_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  dsimp only
  rcases t with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · simp only [impl₁_unif, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨_, _, rfl⟩ := hw; exact le_rfl
  · rw [impl₁_prim] at hw
    cases pq with
    | sigSign _ _ _ =>
        exfalso; exact hnotG (by simp [isRomGrowthQuery, isRomPrimSigSignQuery])
    | sigVerify _ _ _ =>
        exfalso; exact hnotG (by simp [isRomGrowthQuery, isRomPrimVerifyQuery])
    | _ =>
        dsimp only [primRoStep] at hw
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        subst hw; exact le_rfl
  · exfalso; exact hnotG (by simp [isRomGrowthQuery, isRomDirectRoQuery])
  · exfalso; exact hnotS (by simp [isRomSigChalQuery])
  · simp only [impl₁_ddh, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw; exact le_rfl

private theorem hop23_step_charged
    (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    ∀ (t : XeddsaRomOracleSpec.Domain), isRomSigChalQuery t = true →
      ∀ (s : sha512RoSpec.QueryCache),
        letI : MeasurableSpace (XeddsaRomOracleSpec.Range t × sha512RoSpec.QueryCache × Bool) := ⊤
        measureETVDist
          ((liftNoBad (impl₁ P isValidDhTriple sk) t).run (s, false))
          ((liftNoBad
            (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) t).run
            (s, false)) ≤
          ENNReal.ofReal deltaWide + (projNonH1 s).enncard * (l25519 : ℝ≥0∞)⁻¹ := by
  intro t ht s
  rcases t with (((n | pq) | bs) | (sq | dq)) <;>
    try { simp [isRomSigChalQuery] at ht }
  rcases sq with ⟨m⟩
  let : MeasurableSpace (Bytes × sha512RoSpec.QueryCache) := ⊤
  let : MeasurableSpace (Bytes × sha512RoSpec.QueryCache × Bool) := ⊤
  rw [liftNoBad_run, liftNoBad_run, impl₁_sig, impl₃_sig]
  exact (measureETVDist_map_le _ _ _ Measurable.of_discrete).trans
    (measureETVDist_sig_hop23_step P C sk m s)

private theorem hop23_step_uncharged
    (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (sk pk : Bytes) (bSim : UInt8) :
    ∀ (t : XeddsaRomOracleSpec.Domain), ¬ isRomSigChalQuery t = true →
      ∀ (s : sha512RoSpec.QueryCache),
        (liftNoBad (impl₁ P isValidDhTriple sk) t).run (s, false) =
          (liftNoBad (impl₃ P isValidDhTriple pk bSim) t).run (s, false) := by
  intro t ht s
  rcases t with (((n | pq) | bs) | (sq | ⟨X, Y, Z⟩))
  · rfl
  · rfl
  · rfl
  · exfalso; exact ht (by simp [isRomSigChalQuery])
  · rfl

private theorem measureETVDist_hop23_le {α : Type}
    (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) {qS qH : ℕ}
    (hqS : oa.IsQueryBoundP (fun q => isRomSigChalQuery q = true) qS)
    (hqH : oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true) qH) :
    letI : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
    measureETVDist
      ((simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅)
      ((simulateQ (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa).run ∅) ≤
      ENNReal.ofReal
        ((qS : ℝ) * deltaWide + (qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) := by
  let : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
  let : MeasurableSpace (α × sha512RoSpec.QueryCache × Bool) := ⊤
  have hprojL := simulateQ_liftNoBad_proj (impl₁ P isValidDhTriple sk) oa ∅ false
  have hprojR := simulateQ_liftNoBad_proj
    (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa ∅ false
  have hsd :=
    OracleComp.ProgramLogic.Relational.measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad
      (liftNoBad (impl₁ P isValidDhTriple sk))
      (liftNoBad (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))))
      (fun q => isRomSigChalQuery q = true)
      (fun s => ENNReal.ofReal deltaWide + (projNonH1 s).enncard * (l25519 : ℝ≥0∞)⁻¹)
      (hop23_step_charged P C isValidDhTriple sk)
      (hop23_step_uncharged P isValidDhTriple sk (P.x25519Base sk) (C.edSign (clampedScalarZMod sk)))
      (liftNoBad_mono _) oa hqS (∅, false)
  rw [prEvent_liftNoBad_bad_eq_zero, add_zero] at hsd
  have hslack :=
    OracleComp.ProgramLogic.Relational.expectedQuerySlack_resource_le
      (liftNoBad (impl₁ P isValidDhTriple sk))
      (fun q => isRomSigChalQuery q = true)
      (fun q => isRomGrowthQuery q = true)
      (fun s => (projNonH1 s).enncard)
      (ENNReal.ofReal deltaWide)
      (l25519 : ℝ≥0∞)⁻¹
      (impl₁_resource_growth P isValidDhTriple sk)
      (impl₁_resource_free P isValidDhTriple sk)
      oa hqS hqH ∅
  simp only [projNonH1_empty, QueryCache.enncard_empty, zero_add] at hslack
  have hdelta_nonneg : 0 ≤ deltaWide := by
    unfold deltaWide
    have hl_pos : (0 : ℝ) < (l25519 : ℝ) := by exact_mod_cast l25519_pos
    positivity
  have hcast_rhs :
      (qS : ℝ≥0∞) * ENNReal.ofReal deltaWide +
          (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * (l25519 : ℝ≥0∞)⁻¹ =
        ENNReal.ofReal
          ((qS : ℝ) * deltaWide + (qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) := by
    have hl_pos : (0 : ℝ) < (l25519 : ℝ) := by exact_mod_cast l25519_pos
    have hterm1 : (qS : ℝ≥0∞) * ENNReal.ofReal deltaWide = ENNReal.ofReal ((qS : ℝ) * deltaWide) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg qS), ENNReal.ofReal_natCast]
    have hterm2 :
        (qS : ℝ≥0∞) * ((qS : ℝ≥0∞) + (qH : ℝ≥0∞)) * (l25519 : ℝ≥0∞)⁻¹ =
          ENNReal.ofReal ((qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hl_pos, div_eq_mul_inv,
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (Nat.cast_nonneg qS) (Nat.cast_nonneg qH),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast l25519]
    rw [hterm1, hterm2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc measureETVDist
        ((simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅)
        ((simulateQ (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa).run ∅)
      = measureETVDist
          (Prod.map id Prod.fst <$> (simulateQ (liftNoBad (impl₁ P isValidDhTriple sk)) oa).run (∅, false))
          (Prod.map id Prod.fst <$>
            (simulateQ (liftNoBad (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk)))) oa).run
              (∅, false)) := by
          rw [hprojL, hprojR]
    _ ≤ measureETVDist ((simulateQ (liftNoBad (impl₁ P isValidDhTriple sk)) oa).run (∅, false))
          ((simulateQ (liftNoBad (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk)))) oa).run
            (∅, false)) :=
          measureETVDist_map_le _ _ _ Measurable.of_discrete
    _ ≤ _ := hsd.trans hslack
    _ = ENNReal.ofReal
          ((qS : ℝ) * deltaWide + (qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) := hcast_rhs

/-! ## Combined HVZK simulation bounds -/

private theorem xeddsaSimLoss_nonneg (qS qH : ℕ) : 0 ≤ xeddsaSimLoss qS qH := by
  unfold xeddsaSimLoss deltaWide
  have hl_pos : (0 : ℝ) < (l25519 : ℝ) := by exact_mod_cast l25519_pos
  positivity

private theorem measureETVDist_projNonH1_impl₀_impl₃_le {α : Type}
    (P : Primitives) (C : XeddsaCurveWitness P)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (sk : Bytes)
    (oa : OracleComp XeddsaRomOracleSpec α) {qS qH : ℕ}
    (hqS : oa.IsQueryBoundP (fun q => isRomSigChalQuery q = true) qS)
    (hqH : oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true) qH) :
    letI : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
    measureETVDist
      (Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅)
      (Prod.map id projNonH1 <$>
        (simulateQ (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa).run ∅) ≤
      ENNReal.ofReal (xeddsaSimLoss qS qH) := by
  let : MeasurableSpace (α × sha512RoSpec.QueryCache) := ⊤
  have h1 := measureETVDist_hop1_le P isValidDhTriple sk oa hqS hqH
  have h23 :
      measureETVDist
        (Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅)
        (Prod.map id projNonH1 <$>
          (simulateQ (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa).run ∅) ≤
        ENNReal.ofReal
          ((qS : ℝ) * deltaWide + (qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) :=
    (measureETVDist_map_le _ _ (Prod.map id projNonH1) Measurable.of_discrete).trans
      (measureETVDist_hop23_le P C isValidDhTriple sk oa hqS hqH)
  have hdelta_nonneg : 0 ≤ deltaWide := by
    unfold deltaWide
    have hl_pos : (0 : ℝ) < (l25519 : ℝ) := by exact_mod_cast l25519_pos
    positivity
  have hl_pos : (0 : ℝ) < (l25519 : ℝ) := by exact_mod_cast l25519_pos
  calc measureETVDist
        (Prod.map id projNonH1 <$> (simulateQ (impl₀ P isValidDhTriple sk) oa).run ∅)
        (Prod.map id projNonH1 <$>
          (simulateQ (impl₃ P isValidDhTriple (P.x25519Base sk) (C.edSign (clampedScalarZMod sk))) oa).run ∅)
      ≤ _ := measureETVDist_triangle _
              (Prod.map id projNonH1 <$> (simulateQ (impl₁ P isValidDhTriple sk) oa).run ∅) _
    _ ≤ ENNReal.ofReal ((qS : ℝ) * (2 * (qH : ℝ) + 3 * (qS : ℝ)) / (2 : ℝ) ^ 512) +
          ENNReal.ofReal
            ((qS : ℝ) * deltaWide + (qS : ℝ) * ((qS : ℝ) + (qH : ℝ)) / (l25519 : ℝ)) :=
          add_le_add h1 h23
    _ = ENNReal.ofReal (xeddsaSimLoss qS qH) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          unfold xeddsaSimLoss
          rw [← add_assoc]

private theorem sha512RoImpl_run'_eq_of_apply_eq {t : Bytes} {c₁ c₂ : sha512RoSpec.QueryCache}
    (h : c₁ t = c₂ t) :
    (sha512RoImpl t).run' c₁ = (sha512RoImpl t).run' c₂ := by
  rw [StateT.run'_eq, StateT.run'_eq]
  cases hc1 : c₁ t with
  | some v =>
      have hc2 : c₂ t = some v := h.symm.trans hc1
      rw [sha512RoImpl_run_some hc1, sha512RoImpl_run_some hc2, map_pure, map_pure]
  | none =>
      have hc2 : c₂ t = none := h.symm.trans hc1
      rw [sha512RoImpl_run_none hc1, sha512RoImpl_run_none hc2,
        Functor.map_map, Functor.map_map]

private theorem evalDistEq_const_of_probComp {α β : Type} (mx : ProbComp α) (b : β) :
    (fun _ => b) <$> mx =ᵈ (pure b : ProbComp β) := by
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  let : MeasurableSpace α := ⊤
  rw [prEvent_map]
  by_cases hpb : p b
  · rw [prEvent_const_of_lossless mx
      (by rw [prEvent_true_eq_evalDist_apply_univ, evalDist_apply_univ_eq_one]) hpb]
    simp [hpb]
  · simp [hpb]

private theorem evalDistEq_xeddsaVerifyRo_projNonH1
    (P : Primitives) (C : XeddsaCurveWitness P) (sk m sig : Bytes)
    (c : sha512RoSpec.QueryCache) :
    (simulateQ sha512RoImpl (xeddsaVerifyRo P (P.x25519Base sk) m sig)).run' c =ᵈ
      (simulateQ sha512RoImpl (xeddsaVerifyRo P (P.x25519Base sk) m sig)).run' (projNonH1 c) := by
  unfold xeddsaVerifyRo
  split_ifs with hguard
  · dsimp only
    set signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    obtain ⟨edPk, hmont, hrep_raw⟩ :=
      C.montToEd_base sk signBit (uint8_shift_signBit_bool (sig.getD 63 0))
    rw [hmont]
    dsimp only
    set capA := P.compress edPk
    set minusCapA := P.edNeg edPk
    set capR := sig.take 32
    set sRaw := sig.drop 32
    set sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
    set sScalar := P.scalarFromBytesModOrder sClamped
    let checkFn : Bytes → Bool := fun hDigest =>
      P.compress (P.doubleScalarMulBasepoint (P.scalarFromWide hDigest) minusCapA sScalar) == capR
    have hrun' : ∀ c' : sha512RoSpec.QueryCache,
        (simulateQ sha512RoImpl
          (liftM (OracleSpec.query (spec := sha512RoSpec) (capR ++ capA ++ m)) >>= fun hDigest =>
            pure (checkFn hDigest))).run' c' =
        checkFn <$> (sha512RoImpl (capR ++ capA ++ m)).run' c' := by
      intro c'
      simp [StateT.run'_eq, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, Functor.map_map, bind_pure_comp]
    change (simulateQ sha512RoImpl
        (liftM (OracleSpec.query (spec := sha512RoSpec) (capR ++ capA ++ m)) >>= fun hDigest =>
          pure (checkFn hDigest))).run' c =ᵈ
      (simulateQ sha512RoImpl
        (liftM (OracleSpec.query (spec := sha512RoSpec) (capR ++ capA ++ m)) >>= fun hDigest =>
          pure (checkFn hDigest))).run' (projNonH1 c)
    rw [hrun' c, hrun' (projNonH1 c)]
    cases ht : isH1 (capR ++ capA ++ m) with
    | false =>
        have happly : c (capR ++ capA ++ m) = projNonH1 c (capR ++ capA ++ m) := by
          simp only [projNonH1_apply, ht, Bool.false_eq_true, ↓reduceIte]
        rw [sha512RoImpl_run'_eq_of_apply_eq happly]
    | true =>
        have hsig_len : sig.length = 64 := by
          have hg1 := (Bool.and_eq_true _ _).mp hguard
          have hg2 := (Bool.and_eq_true _ _).mp hg1.1
          exact of_decide_eq_true hg2.2
        have hcapR_len : capR.length = 32 := by simp [capR, hsig_len]
        have hcapR_eq_pref : capR = xeddsaHashPrefix := by
          unfold isH1 at ht
          rw [List.append_assoc, List.take_append_of_le_length (by omega),
            List.take_of_length_le (by omega)] at ht
          exact eq_of_beq ht
        have hcheck_false : checkFn = fun _ => false := by
          funext hDigest
          dsimp only [checkFn]
          have hrep_neg : C.RepresentsEd
              (-(if signBit == C.edSign (clampedScalarZMod sk) then
                  clampedScalarZMod sk else -clampedScalarZMod sk))
              minusCapA := C.edNeg_represents hrep_raw
          have hs_eq : sScalar = encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 sClamped)) :=
            C.scalarMod_eq sClamped
          have hh_eq : P.scalarFromWide hDigest =
              encodeScalarBytes (decodeScalarBytes (fitBytesRef 64 hDigest)) :=
            C.scalarWide_eq hDigest
          rw [hh_eq, hs_eq, C.compress_of_represents (C.dsmb_represents _ _ hrep_neg), hcapR_eq_pref]
          cases hbeq : (C.compressEd _ == xeddsaHashPrefix)
          · rfl
          · have heq := eq_of_beq hbeq
            have hrange := C.compressEd_inRange
              (decodeScalarBytes (fitBytesRef 64 hDigest) *
                -(if signBit == C.edSign (clampedScalarZMod sk) then
                    clampedScalarZMod sk else -clampedScalarZMod sk) +
                decodeScalarBytes (fitBytesRef 32 sClamped))
            rw [heq, scalarIsInRange_clearSignBit32_xeddsaHashPrefix] at hrange
            exact absurd hrange Bool.false_ne_true
        rw [hcheck_false]
        exact (evalDistEq_const_of_probComp _ false).trans
          (evalDistEq_const_of_probComp _ false).symm
  · rfl

private theorem abs_toReal_sub_le_of_measureETVDist_le
    (mx my : ProbComp Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (htv : letI : MeasurableSpace Bool := ⊤; measureETVDist mx my ≤ ENNReal.ofReal δ) :
    |(𝒟[mx] {true}).toReal - (𝒟[my] {true}).toReal| ≤ δ := by
  let : MeasurableSpace Bool := ⊤
  have habs : ENNReal.absDiff (𝒟[mx] {true}) (𝒟[my] {true}) ≤ ENNReal.ofReal δ :=
    (measure_absDiff_apply_le_measureETVDist mx my MeasurableSet.of_discrete).trans htv
  set p := 𝒟[mx] {true}
  set q := 𝒟[my] {true}
  have hp_top : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_le_one mx {true})
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_le_one my {true})
  rcases le_total p q with hpq | hqp
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hpq, zero_add] at habs
    have hle_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
    have hdiff_le : q.toReal - p.toReal ≤ δ := by
      rw [← ENNReal.toReal_sub_of_le hpq hq_top, ← ENNReal.toReal_ofReal hδ]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top habs
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle_real)]
    exact hdiff_le
  · simp only [ENNReal.absDiff, tsub_eq_zero_of_le hqp, add_zero] at habs
    have hle_real : q.toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hqp
    have hdiff_le : p.toReal - q.toReal ≤ δ := by
      rw [← ENNReal.toReal_sub_of_le hqp hp_top, ← ENNReal.toReal_ofReal hδ]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top habs
    rw [abs_of_nonneg (sub_nonneg.mpr hle_real)]
    exact hdiff_le

private theorem measureETVDist_bind_probComp_le {α β : Type} [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β) {ε : ℝ≥0∞}
    (hfg : ∀ a, measureETVDist (f a) (g a) ≤ ε) :
    measureETVDist (mx >>= f) (mx >>= g) ≤ ε := by
  let : MeasurableSpace α := ⊤
  have : IsProbabilityMeasure 𝒟[mx] := ⟨evalDist_apply_univ_eq_one mx⟩
  refine (measureETVDist_bind_bind_le_lintegral mx f g
    Measurable.of_discrete Measurable.of_discrete (fun _ => ε)
    (Filter.Eventually.of_forall hfg)).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

private theorem measureETVDist_gapDhWithSignRoExpAt_le
    (P : Primitives) (C : XeddsaCurveWitness P) (A : GapDhWithSignRoAdv)
    (hA : A.Bounded) (u v : Bytes) :
    letI : MeasurableSpace Bool := ⊤
    measureETVDist
      (gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A)
      (gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
        (C.edSign (clampedScalarZMod u)) A) ≤
      ENNReal.ofReal
        (xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSpace (Bytes × sha512RoSpec.QueryCache) := ⊤
  obtain ⟨_, hq_sig, _, hq_ro, hq_ver, hq_psig⟩ := hA
  set U := P.x25519Base u
  set V := P.x25519Base v
  have hqH := isQueryBoundP_growth_of_bounds (hq_ro U V) (hq_ver U V) (hq_psig U V)
  have h3hop := measureETVDist_projNonH1_impl₀_impl₃_le P C P.isValidDhTriple u
    (A.run U V) (hq_sig U V) hqH
  let winFn : Bytes × sha512RoSpec.QueryCache → Bool :=
    fun z => P.pow8 z.1 == P.pow8 (P.x25519 u V)
  have hL : gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A =
      winFn <$> (Prod.map id projNonH1 <$>
        (simulateQ (impl₀ P P.isValidDhTriple u) (A.run U V)).run ∅) := by
    have hsig :
        (fun (.sign m) => do
          let r ← liftM (m := ProbComp) sampleRandom64
          simulateQ sha512RoImpl (xeddsaSignRo P u m r)) =
        sigRoImpl₀ P u := by
      funext ⟨m⟩; rfl
    have hddh :
        (fun (X, Y, Z) => (pure (P.isValidDhTriple X Y Z) : Sha512RoComp Bool)) =
        ddhRoImpl P.isValidDhTriple := by
      funext ⟨X, Y, Z⟩; rfl
    unfold gapDhWithSignRoExpAt
    dsimp only
    rw [hsig, hddh]
    simp [impl₀, StateT.run'_eq, Functor.map_map, bind_pure_comp, winFn, U, V]
  have hR : gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
      (C.edSign (clampedScalarZMod u)) A =
      winFn <$> (Prod.map id projNonH1 <$>
        (simulateQ (impl₃ P P.isValidDhTriple U (C.edSign (clampedScalarZMod u)))
          (A.run U V)).run ∅) := by
    have hsig :
        (fun (.sign m) => xeddsaSimSign P U (C.edSign (clampedScalarZMod u)) m) =
        sigRoImpl₃ P U (C.edSign (clampedScalarZMod u)) := by
      funext ⟨m⟩; rfl
    have hddh :
        (fun (X, Y, Z) => (pure (P.isValidDhTriple X Y Z) : Sha512RoComp Bool)) =
        ddhRoImpl P.isValidDhTriple := by
      funext ⟨X, Y, Z⟩; rfl
    unfold gapDhWithSignSimExpAt gapDhWithSignSimRun
    dsimp only
    rw [hsig, hddh]
    simp [impl₃, StateT.run'_eq, Functor.map_map, bind_pure_comp, winFn, U, V]
  rw [hL, hR]
  exact (measureETVDist_map_le _ _ winFn Measurable.of_discrete).trans h3hop

theorem gapDhWithSignRoExpAt_abs_sub_sim_le (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapDhWithSignRoAdv) (hA : A.Bounded) (u v : Bytes) :
    |(𝒟[gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A] {true}).toReal -
      (𝒟[gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
        (C.edSign (clampedScalarZMod u)) A] {true}).toReal| ≤
      xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  let _ := hWF
  exact abs_toReal_sub_le_of_measureETVDist_le _ _ (xeddsaSimLoss_nonneg _ _)
    (measureETVDist_gapDhWithSignRoExpAt_le P C A hA u v)

theorem gapDhWithSignRoExpAt_le_sim (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapDhWithSignRoAdv) (hA : A.Bounded) (u v : Bytes) :
    (𝒟[gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A] {true}).toReal ≤
      (𝒟[gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
        (C.edSign (clampedScalarZMod u)) A] {true}).toReal +
        xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  have h := gapDhWithSignRoExpAt_abs_sub_sim_le P hWF C A hA u v
  linarith [le_abs_self ((𝒟[gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A] {true}).toReal -
    (𝒟[gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
      (C.edSign (clampedScalarZMod u)) A] {true}).toReal)]

/-- HVZK signing-simulation bound for `GapDhWithSignRo`. -/
theorem gapDhWithSignRo_le_sim (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapDhWithSignRoAdv) (hA : A.Bounded) :
    GapDhWithSignRo P P.isValidDhTriple P.pow8 A ≤
      (𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true}).toReal +
        xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  let _ := hWF
  let : MeasurableSpace Bool := ⊤
  have htv : measureETVDist
      (gapDhWithSignRoExp P P.isValidDhTriple P.pow8 A)
      (gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A) ≤
      ENNReal.ofReal
        (xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) := by
    change measureETVDist
      (sampleScalar32 >>= fun u => sampleScalar32 >>= fun v =>
        gapDhWithSignRoExpAt P P.isValidDhTriple P.pow8 u v A)
      (sampleScalar32 >>= fun u => sampleScalar32 >>= fun v =>
        gapDhWithSignSimExpAt P P.isValidDhTriple P.pow8 u v
          (C.edSign (clampedScalarZMod u)) A) ≤ _
    exact measureETVDist_bind_probComp_le sampleScalar32 _ _ fun u =>
      measureETVDist_bind_probComp_le sampleScalar32 _ _ fun v =>
        measureETVDist_gapDhWithSignRoExpAt_le P C A hA u v
  have habs := abs_toReal_sub_le_of_measureETVDist_le _ _ (xeddsaSimLoss_nonneg _ _) htv
  unfold GapDhWithSignRo
  linarith [le_abs_self ((𝒟[gapDhWithSignRoExp P P.isValidDhTriple P.pow8 A] {true}).toReal -
    (𝒟[gapDhWithSignSimExp P C P.isValidDhTriple P.pow8 A] {true}).toReal)]

private theorem measureETVDist_gapSigEufCmaRoExpAt_le
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv) (hA : A.Bounded) (sk : Bytes) :
    letI : MeasurableSpace Bool := ⊤
    measureETVDist
      (gapSigEufCmaRoExpAt P P.isValidDhTriple sk A)
      (gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A) ≤
      ENNReal.ofReal
        (xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSpace (((Bytes × Bytes) × List Bytes) × sha512RoSpec.QueryCache) := ⊤
  obtain ⟨hq_sig, _, _, hq_ro, hq_ver, hq_psig⟩ := hA
  set pk := P.x25519Base sk
  set oa := (simulateQ logSigQuery (A.run pk)).run ([] : List Bytes)
  have hqS_oa : oa.IsQueryBoundP (fun q => isRomSigChalQuery q = true) A.q_sig :=
    isQueryBoundP_logSigQuery (hq_sig pk) []
  have hqH_oa : oa.IsQueryBoundP (fun q => isRomGrowthQuery q = true)
      (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) :=
    isQueryBoundP_logSigQuery
      (isQueryBoundP_growth_of_bounds (hq_ro pk) (hq_ver pk) (hq_psig pk)) []
  have h3hop := measureETVDist_projNonH1_impl₀_impl₃_le P C P.isValidDhTriple sk oa hqS_oa hqH_oa
  let post : ((Bytes × Bytes) × List Bytes) × sha512RoSpec.QueryCache → ProbComp Bool :=
    fun z =>
      (fun ok : Bool => ok && decide (z.1.1.1 ∉ z.1.2)) <$>
        (simulateQ sha512RoImpl (xeddsaVerifyRo P pk z.1.1.1 z.1.1.2)).run' z.2
  have hL : gapSigEufCmaRoExpAt P P.isValidDhTriple sk A =ᵈ
      ((Prod.map id projNonH1 <$> (simulateQ (impl₀ P P.isValidDhTriple sk) oa).run ∅) >>=
        post) := by
    have hsig_eq :
        (fun (.sign m) => do
          let r ← liftM (m := ProbComp) sampleRandom64
          let sig ← liftM (m := Sha512RoComp) (simulateQ sha512RoImpl (xeddsaSignRo P sk m r))
          modify (m :: ·)
          return sig) =
        (fun (.sign m) => do
          let sig ← liftM (m := Sha512RoComp) (sigRoImpl₀ P sk (.sign m))
          modify (m :: ·)
          return sig : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp)) := by
      funext ⟨m⟩
      simp only [sigRoImpl₀, monadLift_bind, bind_assoc]
      rfl
    unfold gapSigEufCmaRoExpAt
    rw [hWF.sigPkGen_eq_x25519Base]
    dsimp only
    rw [hsig_eq,
      simulateQ_stateSig_eq_logSigQuery P P.isValidDhTriple (sigRoImpl₀ P sk) (A.run pk) []]
    have hddh :
        (fun (X, Y, Z) => (pure (P.isValidDhTriple X Y Z) : Sha512RoComp Bool)) =
        ddhRoImpl P.isValidDhTriple := by
      funext ⟨X, Y, Z⟩; rfl
    rw [hddh]
    change (((simulateQ (impl₀ P P.isValidDhTriple sk) oa) >>= fun out =>
        (simulateQ sha512RoImpl (xeddsaVerifyRo P pk out.1.1 out.1.2)) >>= fun ok =>
          pure (ok && decide (out.1.1 ∉ out.2))).run' ∅) =ᵈ _
    have hunfold :
        (((simulateQ (impl₀ P P.isValidDhTriple sk) oa) >>= fun out =>
          (simulateQ sha512RoImpl (xeddsaVerifyRo P pk out.1.1 out.1.2)) >>= fun ok =>
            pure (ok && decide (out.1.1 ∉ out.2))).run' ∅) =
        ((simulateQ (impl₀ P P.isValidDhTriple sk) oa).run ∅ >>= post) := by
      simp [StateT.run'_eq, StateT.run_bind, map_bind, Functor.map_map,
        bind_pure_comp, post]
    rw [hunfold, bind_map_left]
    refine EvalDistEq.bind EvalDistEq.rfl fun z => ?_
    dsimp only [post, Prod.map, id_eq]
    exact (evalDistEq_xeddsaVerifyRo_projNonH1 P C sk z.1.1.1 z.1.1.2 z.2).map _
  have hR : gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A =ᵈ
      ((Prod.map id projNonH1 <$>
        (simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa).run ∅) >>=
        post) := by
    have hsig_eq :
        (fun (.sign m) => do
          let sig ← liftM (m := Sha512RoComp)
            (xeddsaSimSign P pk (C.edSign (clampedScalarZMod sk)) m)
          modify (m :: ·)
          return sig) =
        (fun (.sign m) => do
          let sig ← liftM (m := Sha512RoComp)
            (sigRoImpl₃ P pk (C.edSign (clampedScalarZMod sk)) (.sign m))
          modify (m :: ·)
          return sig : QueryImpl sigOracleSpec (StateT (List Bytes) Sha512RoComp)) := by
      funext ⟨m⟩; rfl
    unfold gapSigEufCmaSimExpAt gapSigEufCmaSimExpOnPk
    dsimp only
    rw [hsig_eq, simulateQ_stateSig_eq_logSigQuery P P.isValidDhTriple
      (sigRoImpl₃ P pk (C.edSign (clampedScalarZMod sk))) (A.run pk) []]
    have hddh :
        (fun (X, Y, Z) => (pure (P.isValidDhTriple X Y Z) : Sha512RoComp Bool)) =
        ddhRoImpl P.isValidDhTriple := by
      funext ⟨X, Y, Z⟩; rfl
    rw [hddh]
    change (((simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa) >>=
        fun out =>
          (simulateQ sha512RoImpl (xeddsaVerifyRo P pk out.1.1 out.1.2)) >>= fun ok =>
            pure (ok && decide (out.1.1 ∉ out.2))).run' ∅) =ᵈ _
    have hunfold :
        (((simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa) >>=
          fun out =>
            (simulateQ sha512RoImpl (xeddsaVerifyRo P pk out.1.1 out.1.2)) >>= fun ok =>
              pure (ok && decide (out.1.1 ∉ out.2))).run' ∅) =
        ((simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa).run ∅ >>=
          post) := by
      simp [StateT.run'_eq, StateT.run_bind, map_bind, Functor.map_map,
        bind_pure_comp, post]
    rw [hunfold, bind_map_left]
    refine EvalDistEq.bind EvalDistEq.rfl fun z => ?_
    dsimp only [post, Prod.map, id_eq]
    exact (evalDistEq_xeddsaVerifyRo_projNonH1 P C sk z.1.1.1 z.1.1.2 z.2).map _
  calc measureETVDist
        (gapSigEufCmaRoExpAt P P.isValidDhTriple sk A)
        (gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A)
      = Measure.etvDist 𝒟[gapSigEufCmaRoExpAt P P.isValidDhTriple sk A]
          𝒟[gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A] := rfl
    _ = Measure.etvDist
          𝒟[(Prod.map id projNonH1 <$> (simulateQ (impl₀ P P.isValidDhTriple sk) oa).run ∅) >>=
            post]
          𝒟[(Prod.map id projNonH1 <$>
            (simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa).run ∅) >>=
            post] := by rw [hL.evalDist_eq, hR.evalDist_eq]
    _ = measureETVDist
          ((Prod.map id projNonH1 <$> (simulateQ (impl₀ P P.isValidDhTriple sk) oa).run ∅) >>= post)
          ((Prod.map id projNonH1 <$>
            (simulateQ (impl₃ P P.isValidDhTriple pk (C.edSign (clampedScalarZMod sk))) oa).run ∅) >>=
            post) := rfl
    _ ≤ _ := (measureETVDist_bind_le _ _ post Measurable.of_discrete).trans h3hop

theorem gapSigEufCmaRoExpAt_abs_sub_sim_le (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv) (hA : A.Bounded) (sk : Bytes) :
    |(𝒟[gapSigEufCmaRoExpAt P P.isValidDhTriple sk A] {true}).toReal -
      (𝒟[gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A]
        {true}).toReal| ≤
      xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) :=
  abs_toReal_sub_le_of_measureETVDist_le _ _ (xeddsaSimLoss_nonneg _ _)
    (measureETVDist_gapSigEufCmaRoExpAt_le P hWF C A hA sk)

theorem gapSigEufCmaRoExpAt_le_sim (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv) (hA : A.Bounded) (sk : Bytes) :
    (𝒟[gapSigEufCmaRoExpAt P P.isValidDhTriple sk A] {true}).toReal ≤
      (𝒟[gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A]
        {true}).toReal +
        xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  have h := gapSigEufCmaRoExpAt_abs_sub_sim_le P hWF C A hA sk
  linarith [le_abs_self ((𝒟[gapSigEufCmaRoExpAt P P.isValidDhTriple sk A] {true}).toReal -
    (𝒟[gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A]
      {true}).toReal)]

/-- HVZK signing-simulation bound for `GapSigEufCmaRo`. -/
theorem gapSigEufCmaRo_le_sim (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (C : XeddsaCurveWitness P) (A : GapSigEufCmaRoAdv) (hA : A.Bounded) :
    GapSigEufCmaRo P P.isValidDhTriple A ≤
      (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal +
        xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign) := by
  let : MeasurableSpace Bool := ⊤
  have htv : measureETVDist
      (gapSigEufCmaRoExp P P.isValidDhTriple A)
      (gapSigEufCmaSimExp P C P.isValidDhTriple A) ≤
      ENNReal.ofReal
        (xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)) := by
    change measureETVDist
      (sampleScalar32 >>= fun sk => gapSigEufCmaRoExpAt P P.isValidDhTriple sk A)
      (sampleScalar32 >>= fun sk =>
        gapSigEufCmaSimExpAt P P.isValidDhTriple sk (C.edSign (clampedScalarZMod sk)) A) ≤ _
    exact measureETVDist_bind_probComp_le sampleScalar32 _ _ fun sk =>
      measureETVDist_gapSigEufCmaRoExpAt_le P hWF C A hA sk
  have habs := abs_toReal_sub_le_of_measureETVDist_le _ _ (xeddsaSimLoss_nonneg _ _) htv
  unfold GapSigEufCmaRo
  linarith [le_abs_self ((𝒟[gapSigEufCmaRoExp P P.isValidDhTriple A] {true}).toReal -
    (𝒟[gapSigEufCmaSimExp P C P.isValidDhTriple A] {true}).toReal)]

end Computational.Proofs.SignalPqxdh.XeddsaRom.HvzkSim
