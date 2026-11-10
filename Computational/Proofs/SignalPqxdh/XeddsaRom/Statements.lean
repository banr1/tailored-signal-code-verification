/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthGames
public import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# XEdDSA SHA-512 random-oracle games, curve laws, and reduction statements

**Checked by Lean.** Defines honest XEdDSA signing (`xeddsaSignRef`), the SHA-512 random-oracle
games `GapDhWithSignRo` and `GapSigEufCmaRo` over a shared `sha512RoSpec.QueryCache`, the
prime-order group-algebra interface `XeddsaCurveLaws`, and the quantitative bounds reducing both
games to standalone `GapDH`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.Statements

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery
open _root_.SignalPqxdh (
  Bytes Primitives PrimQuery primSpec PrimBaseSpec
  DdhQuery gapDhOracleSpec SigQuery sigOracleSpec sigAndDdhSpec
  GapDhAdv GapDH WellFormedPrimitivesδ
  clampScalar25519 fitBytesRef scalarIsInRange xeddsaVerifyRef
  sampleScalar32 sampleRandom64
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 encodeScalarBytes decodeScalarBytes xeddsaHashPrefix
  clearSignBit32 clampedScalarZMod
)

/-! ## Honest XEdDSA signing -/

def zeroScalar32 : Bytes :=
  List.replicate 32 0

/-- Canonical on-subgroup Edwards dummy point lifted from `x25519Base zeroScalar32` for `edBaseMul`. -/
def edDummy (P : Primitives) : Bytes :=
  (P.montToEd (P.x25519Base zeroScalar32) 0).getD (List.replicate 160 0)

/-- Edwards basepoint scalar multiplication `[x]B_Ed` expressed via `doubleScalarMulBasepoint`. -/
def edBaseMul (P : Primitives) (x : Bytes) : Bytes :=
  P.doubleScalarMulBasepoint zeroScalar32 (edDummy P) x

/-- Reference XEdDSA signature generation packing the Edwards sign bit of `[a]B_Ed` into bit 7 of
byte 63 without negating the clamped scalar. -/
def xeddsaSignRef (P : Primitives) (sk m rand : Bytes) : Bytes :=
  let keyData := clampScalar25519 sk
  let a := P.scalarFromBytesModOrder keyData
  let edPk := edBaseMul P a
  let capA := P.compress edPk
  let signBitByte : UInt8 := capA.getD 31 0 &&& 0x80
  let r := P.scalarFromWide (P.sha512 (xeddsaHashPrefix ++ keyData ++ m ++ fitBytesRef 64 rand))
  let capR := P.compress (edBaseMul P r)
  let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
  let s := P.scalarAdd (P.scalarMul h a) r
  capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte]

/-! ## SHA-512 random-oracle model and XEdDSA ROM games -/

/-- Random-oracle specification for unkeyed SHA-512 (`Bytes →ₒ Bytes`, answered with uniform 64-byte
digests). -/
abbrev sha512RoSpec : OracleSpec Bytes :=
  Bytes →ₒ Bytes

def sha512RoBaseImpl : QueryImpl sha512RoSpec ProbComp :=
  fun _ => sampleRandom64

abbrev Sha512RoComp : Type → Type :=
  StateT sha512RoSpec.QueryCache ProbComp

def sha512RoImpl : QueryImpl sha512RoSpec Sha512RoComp :=
  sha512RoBaseImpl.withCaching

/-- XEdDSA signing in the SHA-512 random-oracle model. -/
def xeddsaSignRo (P : Primitives) (sk m rand : Bytes) : OracleComp sha512RoSpec Bytes := do
  let keyData := clampScalar25519 sk
  let a := P.scalarFromBytesModOrder keyData
  let edPk := edBaseMul P a
  let capA := P.compress edPk
  let signBitByte : UInt8 := capA.getD 31 0 &&& 0x80
  let h1Digest ← liftM (OracleSpec.query (spec := sha512RoSpec)
    (xeddsaHashPrefix ++ keyData ++ m ++ fitBytesRef 64 rand))
  let r := P.scalarFromWide h1Digest
  let capR := P.compress (edBaseMul P r)
  let hDigest ← liftM (OracleSpec.query (spec := sha512RoSpec) (capR ++ capA ++ m))
  let h := P.scalarFromWide hDigest
  let s := P.scalarAdd (P.scalarMul h a) r
  return (capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte])

/-- XEdDSA verification in the SHA-512 random-oracle model. -/
def xeddsaVerifyRo (P : Primitives) (pk m sig : Bytes) : OracleComp sha512RoSpec Bool := do
  if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
    let signBit : UInt8 := (sig.getD 63 0 &&& 0x80) >>> 7
    match P.montToEd pk signBit with
    | none => return false
    | some edPk =>
      let capA := P.compress edPk
      let minusCapA := P.edNeg edPk
      let capR := sig.take 32
      let sRaw := sig.drop 32
      let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
      let hDigest ← liftM (OracleSpec.query (spec := sha512RoSpec) (capR ++ capA ++ m))
      let h := P.scalarFromWide hDigest
      let sScalar := P.scalarFromBytesModOrder sClamped
      let capRCheck := P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar)
      return (capRCheck == capR)
  else
    return false

/-- Primitive-oracle handler routing `.sigSign` and `.sigVerify` through `sha512RoSpec` and
evaluating all other primitives deterministically from `P`. -/
def primRoStep (P : Primitives) : QueryImpl primSpec (OracleComp sha512RoSpec) := fun
  | .x25519 sk pk          => pure (P.x25519 sk pk)
  | .x25519Base sk         => pure (P.x25519Base sk)
  | .isCanonical pk        => pure (P.isCanonical pk)
  | .pow8 pk               => pure (P.pow8 pk)
  | .sigPkGen sk           => pure (P.sigPkGen sk)
  | .sigSign sk m r        => xeddsaSignRo P sk m r
  | .sigVerify pk m sg     => xeddsaVerifyRo P pk m sg
  | .kemKeyGen seed        => pure (P.kemKeyGen seed)
  | .kemEncaps pk r        => pure (P.kemEncaps pk r)
  | .kemDecaps sk ct       => pure (P.kemDecaps sk ct)
  | .hkdfDerive96 ikm      => pure (P.hkdfDerive96 ikm)
  | .rootCreateChain rk dh => pure (P.rootCreateChain rk dh)
  | .chainKdfSeed ck       => pure (P.chainKdfSeed ck)
  | .chainKdfNext ck       => pure (P.chainKdfNext ck)
  | .spqrInitSend p r      => pure (P.spqrInitSend p r)
  | .spqrInitRecv p m      => pure (P.spqrInitRecv p m)
  | .deriveMsgKeys m s     => pure (P.deriveMsgKeys m s)
  | .aeadEnc mk ad pt      => pure (P.aeadEnc mk ad pt)
  | .aeadDec mk ad ct      => pure (P.aeadDec mk ad ct)

def primRoImpl (P : Primitives) : QueryImpl primSpec Sha512RoComp :=
  fun q => simulateQ sha512RoImpl (primRoStep P q)

def primBaseRoImpl (P : Primitives) : QueryImpl (PrimBaseSpec + sha512RoSpec) Sha512RoComp :=
  (QueryImpl.ofLift unifSpec Sha512RoComp + primRoImpl P) + sha512RoImpl

/-- Combined oracle interface available to adversaries in `GapDhWithSignRo` and `GapSigEufCmaRo`. -/
abbrev XeddsaRomOracleSpec :
    OracleSpec (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) :=
  PrimBaseSpec + sha512RoSpec + sigAndDdhSpec

def isRomPrimQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inl (.inl (.inr _)) => true
  | _                    => false

def isRomPrimVerifyQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inl (.inl (.inr (.sigVerify _ _ _))) => true
  | _                                     => false

def isRomPrimSigSignQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inl (.inl (.inr (.sigSign _ _ _))) => true
  | _                                   => false

def isRomDirectRoQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inl (.inr _) => true
  | _             => false

def isRomSigChalQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inr (.inl _) => true
  | _             => false

def isRomDdhChalQuery : (((ℕ ⊕ PrimQuery) ⊕ Bytes) ⊕ (SigQuery ⊕ DdhQuery)) → Bool
  | .inr (.inr _) => true
  | _             => false

/-- Adversary against `GapDhWithSignRo` with per-channel query budgets. -/
structure GapDhWithSignRoAdv where
  run            : Bytes → Bytes → OracleComp XeddsaRomOracleSpec Bytes
  q_ddh          : ℕ
  q_sig          : ℕ
  q_prim         : ℕ
  q_ro           : ℕ
  q_verify       : ℕ
  q_prim_sigSign : ℕ

def GapDhWithSignRoAdv.Bounded (A : GapDhWithSignRoAdv) : Prop :=
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isRomDdhChalQuery q = true) A.q_ddh) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isRomSigChalQuery q = true) A.q_sig) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isRomPrimQuery q = true) A.q_prim) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isRomDirectRoQuery q = true) A.q_ro) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V) (fun q => isRomPrimVerifyQuery q = true) A.q_verify) ∧
  (∀ U V, OracleComp.IsQueryBoundP (A.run U V)
    (fun q => isRomPrimSigSignQuery q = true) A.q_prim_sigSign)

/-- SHA-512 random-oracle `GapDhWithSign` experiment over a shared `sha512RoSpec.QueryCache`. -/
noncomputable def gapDhWithSignRoExp (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignRoAdv) : ProbComp Bool := do
  let u ← sampleScalar32
  let v ← sampleScalar32
  let U := P.x25519Base u
  let V := P.x25519Base v
  let sigImpl : QueryImpl sigOracleSpec Sha512RoComp := fun (.sign m) => do
    let r ← liftM (m := ProbComp) sampleRandom64
    simulateQ sha512RoImpl (xeddsaSignRo P u m r)
  let ddhImpl : QueryImpl gapDhOracleSpec Sha512RoComp := fun (X, Y, Z) =>
    pure (isValidDhTriple X Y Z)
  let Z ← (simulateQ (primBaseRoImpl P + (sigImpl + ddhImpl)) (A.run U V)).run' ∅
  return (pow8 Z == pow8 (P.x25519 u V))

noncomputable def GapDhWithSignRo (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (A : GapDhWithSignRoAdv) : ℝ :=
  (𝒟[gapDhWithSignRoExp P isValidDhTriple pow8 A] {true}).toReal

/-- Adversary against `GapSigEufCmaRo` with per-channel query budgets. -/
structure GapSigEufCmaRoAdv where
  run            : Bytes → OracleComp XeddsaRomOracleSpec (Bytes × Bytes)
  q_sig          : ℕ
  q_ddh          : ℕ
  q_prim         : ℕ
  q_ro           : ℕ
  q_verify       : ℕ
  q_prim_sigSign : ℕ

def GapSigEufCmaRoAdv.Bounded (A : GapSigEufCmaRoAdv) : Prop :=
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isRomSigChalQuery q = true) A.q_sig) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isRomDdhChalQuery q = true) A.q_ddh) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isRomPrimQuery q = true) A.q_prim) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isRomDirectRoQuery q = true) A.q_ro) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk) (fun q => isRomPrimVerifyQuery q = true) A.q_verify) ∧
  (∀ pk, OracleComp.IsQueryBoundP (A.run pk)
    (fun q => isRomPrimSigSignQuery q = true) A.q_prim_sigSign)

/-- SHA-512 random-oracle `GapSigEufCma` experiment over a shared `sha512RoSpec.QueryCache`. -/
noncomputable def gapSigEufCmaRoExp (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaRoAdv) :
    ProbComp Bool := do
  let sk ← sampleScalar32
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

noncomputable def GapSigEufCmaRo (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (A : GapSigEufCmaRoAdv) : ℝ :=
  (𝒟[gapSigEufCmaRoExp P isValidDhTriple A] {true}).toReal

/-! ## Curve25519/Ed25519 subgroup laws -/

/-- Prime-order `ZMod l25519` scalar and projective-compatible Edwards subgroup laws on `P`
supporting XEdDSA roundtrip correctness, HVZK simulation, and 2-special-soundness extraction. -/
structure XeddsaCurveWitness (P : Primitives) where
  x25519Base_len : ∀ k : Bytes, (P.x25519Base k).length = 32
  scalarMod_eq : ∀ bs : Bytes,
    P.scalarFromBytesModOrder bs = encodeScalarBytes (decodeScalarBytes (fitBytesRef 32 bs))
  scalarWide_eq : ∀ w : Bytes,
    P.scalarFromWide w = encodeScalarBytes (decodeScalarBytes (fitBytesRef 64 w))
  scalarAdd_eq : ∀ x y : ZMod l25519,
    P.scalarAdd (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x + y)
  scalarMul_eq : ∀ x y : ZMod l25519,
    P.scalarMul (encodeScalarBytes x) (encodeScalarBytes y) = encodeScalarBytes (x * y)
  /-- Projective-compatible membership predicate witnessing that `pt` represents `[x]B_Ed`. -/
  RepresentsEd : ZMod l25519 → Bytes → Prop
  compressEd : ZMod l25519 → Bytes
  edSign : ZMod l25519 → UInt8
  edNeg_represents : ∀ {x : ZMod l25519} {pt : Bytes},
    RepresentsEd x pt → RepresentsEd (-x) (P.edNeg pt)
  dsmb_represents : ∀ (h : ZMod l25519) {y : ZMod l25519} {pt : Bytes} (s : ZMod l25519),
    RepresentsEd y pt →
      RepresentsEd (h * y + s)
        (P.doubleScalarMulBasepoint (encodeScalarBytes h) pt (encodeScalarBytes s))
  compress_of_represents : ∀ {x : ZMod l25519} {pt : Bytes},
    RepresentsEd x pt → P.compress pt = compressEd x
  compressEd_inj : Function.Injective compressEd
  compressEd_len : ∀ x : ZMod l25519, (compressEd x).length = 32
  compressEd_inRange : ∀ x : ZMod l25519,
    scalarIsInRange (clearSignBit32 (compressEd x)) = true
  edSign_bool : ∀ x : ZMod l25519, edSign x = 0 ∨ edSign x = 1
  edSign_neg : ∀ x : ZMod l25519, x ≠ 0 → edSign (-x) = 1 - edSign x
  compressEd_signBit : ∀ x : ZMod l25519,
    ((compressEd x).getD 31 0 &&& 0x80) >>> 7 = edSign x
  /-- `montToEd` on `x25519Base sk` and `b ∈ {0, 1}` represents `[±clampedScalarZMod sk]B_Ed`
      according to whether `b == edSign (clampedScalarZMod sk)`. -/
  montToEd_base : ∀ (sk : Bytes) (b : UInt8), (b = 0 ∨ b = 1) →
    ∃ pt : Bytes,
      P.montToEd (P.x25519Base sk) b = some pt ∧
      RepresentsEd
        (if b == edSign (clampedScalarZMod sk) then clampedScalarZMod sk else -clampedScalarZMod sk)
        pt
  /-- Keys whose clamped scalars agree up to sign modulo `l25519` share `x25519Base`. -/
  x25519Base_eq_of_clamped_pm : ∀ u1 u2 : Bytes,
    (clampedScalarZMod u1 = clampedScalarZMod u2 ∨
      clampedScalarZMod u1 = -clampedScalarZMod u2) →
      P.x25519Base u1 = P.x25519Base u2

def XeddsaCurveLaws (P : Primitives) : Prop :=
  Nonempty (XeddsaCurveWitness P)

/-! ## Quantitative loss terms and reduction statements -/

def wideRem : ℕ :=
  2 ^ 512 % l25519

/-- Total-variation distance between `scalarFromWide <$> sampleRandom64` and `$ᵗ (ZMod l25519)`. -/
noncomputable def deltaWide : ℝ :=
  (wideRem : ℝ) * ((l25519 - wideRem : ℕ) : ℝ) / ((l25519 : ℝ) * (2 : ℝ) ^ 512)

/-- Effective adversarial non-`H_1` challenge-hash query budget `q_ro + q_verify + q_prim_sigSign`. -/
def xeddsaChalBudget (q_ro q_verify q_prim_sigSign : ℕ) : ℕ :=
  q_ro + q_verify + q_prim_sigSign

/-- HVZK and random-oracle programming simulation loss across `q_S` signing queries and `q_H`
adversarial challenge-hash queries. -/
noncomputable def xeddsaSimLoss (q_S q_H : ℕ) : ℝ :=
  (q_S : ℝ) * (2 * (q_H : ℝ) + 3 * (q_S : ℝ)) / (2 : ℝ) ^ 512 +
    (q_S : ℝ) * deltaWide +
    (q_S : ℝ) * ((q_S : ℝ) + (q_H : ℝ)) / (l25519 : ℝ)

/-- Modular-reduction loss `(q_H + 1) * deltaWide` for lifting uniform `ZMod l25519` challenges to
64-byte digests. -/
noncomputable def xeddsaModLoss (q_H : ℕ) : ℝ :=
  ((q_H : ℝ) + 1) * deltaWide

/-- Concrete and SHA-512 ROM XEdDSA sign-then-verify roundtrip correctness under
`XeddsaCurveLaws`. -/
def XeddsaSignRoundtrip : Prop :=
  (∀ (P : Primitives), XeddsaCurveLaws P →
    ∀ sk m rand : Bytes,
      xeddsaVerifyRef P (P.x25519Base sk) m (xeddsaSignRef P sk m rand) = true) ∧
  (∀ (P : Primitives), WellFormedPrimitivesδ P → XeddsaCurveLaws P →
    WellFormedPrimitivesδ { P with sigSign := xeddsaSignRef P }) ∧
  (∀ (P : Primitives), XeddsaCurveLaws P →
    ∀ (sk m rand : Bytes) (cache : sha512RoSpec.QueryCache),
      𝒟[(simulateQ sha512RoImpl (do
          let sig ← xeddsaSignRo P sk m rand
          xeddsaVerifyRo P (P.x25519Base sk) m sig)).run' cache] {true} = 1)

/-- Single-run `2×` reduction from `GapDhWithSignRo` to standalone `GapDH` preserving `1×` query
budgets. -/
def GapDhWithSignRoBound1A : Prop :=
  ∀ (P : Primitives), WellFormedPrimitivesδ P → XeddsaCurveLaws P →
    ∀ (A : GapDhWithSignRoAdv), A.Bounded →
      ∃ (B₁ : GapDhAdv),
        B₁.Bounded ∧
        B₁.q_ddh ≤ A.q_ddh ∧
        B₁.q_prim ≤ A.q_prim ∧
        GapDhWithSignRo P P.isValidDhTriple P.pow8 A ≤
          2 * GapDH P P.isValidDhTriple P.pow8 B₁ +
            xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)

/-- Two-run DDH-checked `1×` reduction from `GapDhWithSignRo` to standalone `GapDH` with zero
sign-bit loss. -/
def GapDhWithSignRoBound1B : Prop :=
  ∀ (P : Primitives), WellFormedPrimitivesδ P → XeddsaCurveLaws P →
    ∀ (A : GapDhWithSignRoAdv), A.Bounded →
      ∃ (B₁_2run : GapDhAdv),
        B₁_2run.Bounded ∧
        B₁_2run.q_ddh ≤ 2 * A.q_ddh + 1 ∧
        B₁_2run.q_prim ≤ 2 * A.q_prim ∧
        GapDhWithSignRo P P.isValidDhTriple P.pow8 A ≤
          GapDH P P.isValidDhTriple P.pow8 B₁_2run +
            xeddsaSimLoss A.q_sig (xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign)

/-- Raw quadratic forking-lemma bound reducing `GapSigEufCmaRo` to standalone `GapDH`. -/
def GapSigEufCmaRoBoundQuad : Prop :=
  ∀ (P : Primitives), WellFormedPrimitivesδ P → XeddsaCurveLaws P →
    ∀ (A : GapSigEufCmaRoAdv), A.Bounded →
      ∃ (B₂ : GapDhAdv),
        let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
        let eps' := max 0
          (GapSigEufCmaRo P P.isValidDhTriple A -
            xeddsaSimLoss A.q_sig q_H - xeddsaModLoss q_H)
        B₂.Bounded ∧
        B₂.q_ddh ≤ 2 * A.q_ddh ∧
        B₂.q_prim ≤ 2 * A.q_prim + 1 ∧
        eps' * (eps' / ((q_H : ℝ) + 1) - 1 / (l25519 : ℝ)) ≤
          2 * GapDH P P.isValidDhTriple P.pow8 B₂

/-- Closed-form square-root forking-lemma bound reducing `GapSigEufCmaRo` to standalone `GapDH`. -/
def GapSigEufCmaRoBound : Prop :=
  ∀ (P : Primitives), WellFormedPrimitivesδ P → XeddsaCurveLaws P →
    ∀ (A : GapSigEufCmaRoAdv), A.Bounded →
      ∃ (B₂ : GapDhAdv),
        let q_H := xeddsaChalBudget A.q_ro A.q_verify A.q_prim_sigSign
        B₂.Bounded ∧
        B₂.q_ddh ≤ 2 * A.q_ddh ∧
        B₂.q_prim ≤ 2 * A.q_prim + 1 ∧
        GapSigEufCmaRo P P.isValidDhTriple A ≤
          Real.sqrt (2 * ((q_H : ℝ) + 1) * GapDH P P.isValidDhTriple P.pow8 B₂) +
            ((q_H : ℝ) + 1) / (l25519 : ℝ) +
            xeddsaSimLoss A.q_sig q_H +
            xeddsaModLoss q_H

end Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
