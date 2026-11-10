/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.XeddsaRom.Statements
import VCVio.OracleComp.EvalDist.Measure

/-!
# Concrete and SHA-512 ROM XEdDSA sign-then-verify roundtrip

**Checked by Lean.** Discharges `XeddsaSignRoundtrip` under `XeddsaCurveLaws`: deterministic
roundtrip correctness of `xeddsaSignRef`, preservation of `WellFormedPrimitivesδ`, and probability-1
roundtrip correctness of `xeddsaSignRo` and `xeddsaVerifyRo` in the shared SHA-512 random-oracle
cache.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery
open _root_.SignalPqxdh (
  Bytes Primitives WellFormedPrimitivesδ
  clampScalar25519 fitBytesRef fitBytesRef_length xeddsaVerifyRef
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.PrimeL25519 (
  l25519 encodeScalarBytes decodeScalarBytes xeddsaHashPrefix clampedScalarZMod
  encodeScalarBytes_length encodeScalarBytes_zero decodeScalarBytes_encodeScalarBytes
  encodeScalarBytes_byte31_lt_32 clampScalar25519_length
)
open Computational.Proofs.SignalPqxdh.XeddsaRom.Statements (
  zeroScalar32 edDummy edBaseMul xeddsaSignRef
  sha512RoSpec sha512RoBaseImpl sha512RoImpl xeddsaSignRo xeddsaVerifyRo
  XeddsaCurveWitness XeddsaCurveLaws XeddsaSignRoundtrip
)

private theorem fitBytesRef_of_length_eq {n : ℕ} {bs : Bytes} (h : bs.length = n) :
    fitBytesRef n bs = bs := by
  simp [fitBytesRef, h]

private theorem getD_append_right {xs ys : Bytes} {i : ℕ} (hi : xs.length ≤ i) :
    (xs ++ ys).getD i 0 = ys.getD (i - xs.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private theorem uint8_ofNat_toNat_eq (b : UInt8) : UInt8.ofNat b.toNat = b :=
  UInt8.toNat_inj.mp (UInt8.toNat_ofNat_of_lt' b.toBitVec.isLt)

private theorem uint8_and_80_dichotomy (b : UInt8) :
    (b &&& 0x80) = 0 ∨ (b &&& 0x80) = 0x80 := by
  have hcheck : ∀ i : Fin 256,
      (UInt8.ofNat i.val &&& 0x80) = 0 ∨ (UInt8.ofNat i.val &&& 0x80) = 0x80 := by decide
  simpa [uint8_ofNat_toNat_eq b] using hcheck ⟨b.toNat, b.toBitVec.isLt⟩

private theorem packedByte63_and_60 {bS bSign : UInt8} (hbS : bS.toNat < 32) :
    (((bS &&& 0x7F) ||| (bSign &&& 0x80)) &&& 0x60) = 0 := by
  rcases uint8_and_80_dichotomy bSign with h0 | h80
  · rw [h0, UInt8.or_zero]
    have hcheck : ∀ i : Fin 32, ((UInt8.ofNat i.val &&& 0x7F) &&& 0x60) = 0 := by decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩
  · rw [h80]
    have hcheck : ∀ i : Fin 32, (((UInt8.ofNat i.val &&& 0x7F) ||| 0x80) &&& 0x60) = 0 := by decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩

private theorem packedByte63_signBit {bS bSign : UInt8} (hbS : bS.toNat < 32) :
    ((((bS &&& 0x7F) ||| (bSign &&& 0x80)) &&& 0x80) >>> 7) = ((bSign &&& 0x80) >>> 7) := by
  rcases uint8_and_80_dichotomy bSign with h0 | h80
  · rw [h0, UInt8.or_zero]
    have hcheck : ∀ i : Fin 32,
        (((UInt8.ofNat i.val &&& 0x7F) &&& 0x80) >>> 7) = ((0 : UInt8) >>> 7) := by
      decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩
  · rw [h80]
    have hcheck : ∀ i : Fin 32,
        ((((UInt8.ofNat i.val &&& 0x7F) ||| 0x80) &&& 0x80) >>> 7) = ((0x80 : UInt8) >>> 7) := by
      decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩

private theorem packedByte63_and_7f {bS bSign : UInt8} (hbS : bS.toNat < 32) :
    (((bS &&& 0x7F) ||| (bSign &&& 0x80)) &&& 0x7F) = bS := by
  rcases uint8_and_80_dichotomy bSign with h0 | h80
  · rw [h0, UInt8.or_zero]
    have hcheck : ∀ i : Fin 32, ((UInt8.ofNat i.val &&& 0x7F) &&& 0x7F) = UInt8.ofNat i.val := by
      decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩
  · rw [h80]
    have hcheck : ∀ i : Fin 32,
        (((UInt8.ofNat i.val &&& 0x7F) ||| 0x80) &&& 0x7F) = UInt8.ofNat i.val := by decide
    simpa [uint8_ofNat_toNat_eq bS] using hcheck ⟨bS.toNat, hbS⟩

private theorem take31_append_last_of_length_32 {bs : Bytes} (hlen : bs.length = 32) :
    bs.take 31 ++ [bs.getD 31 0] = bs := by
  have hlt : 31 < bs.length := by omega
  have hdrop : bs.drop 31 = [bs.getD 31 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
  conv_rhs => rw [← List.take_append_drop 31 bs, hdrop]

theorem edDummy_represents {P : Primitives} (C : XeddsaCurveWitness P) :
    ∃ y₀ : ZMod l25519, C.RepresentsEd y₀ (edDummy P) := by
  obtain ⟨pt, hmont, hrep⟩ := C.montToEd_base zeroScalar32 0 (Or.inl rfl)
  refine ⟨if (0 : UInt8) == C.edSign (clampedScalarZMod zeroScalar32) then
      clampedScalarZMod zeroScalar32 else -clampedScalarZMod zeroScalar32, ?_⟩
  unfold edDummy
  rw [hmont]
  exact hrep

theorem edBaseMul_represents {P : Primitives} (C : XeddsaCurveWitness P) (x : ZMod l25519) :
    C.RepresentsEd x (edBaseMul P (encodeScalarBytes x)) := by
  obtain ⟨y₀, hy₀⟩ := edDummy_represents C
  unfold edBaseMul
  have hz : zeroScalar32 = encodeScalarBytes 0 := encodeScalarBytes_zero.symm
  rw [hz]
  have hrep := C.dsmb_represents 0 x hy₀
  simpa using hrep

theorem compress_edBaseMul {P : Primitives} (C : XeddsaCurveWitness P) (x : ZMod l25519) :
    P.compress (edBaseMul P (encodeScalarBytes x)) = C.compressEd x :=
  C.compress_of_represents (edBaseMul_represents C x)

/-- Pure signature assembly from 64-byte nonce and challenge digests, shared by `xeddsaSignRef` and
`xeddsaSignRo`. -/
def xeddsaSignFromDigests (P : Primitives) (sk h1Digest hDigest : Bytes) : Bytes :=
  let keyData := clampScalar25519 sk
  let a := P.scalarFromBytesModOrder keyData
  let edPk := edBaseMul P a
  let capA := P.compress edPk
  let signBitByte : UInt8 := capA.getD 31 0 &&& 0x80
  let r := P.scalarFromWide h1Digest
  let capR := P.compress (edBaseMul P r)
  let h := P.scalarFromWide hDigest
  let s := P.scalarAdd (P.scalarMul h a) r
  capR ++ s.take 31 ++ [(s.getD 31 0 &&& 0x7F) ||| signBitByte]

private theorem xeddsaSignFromDigests_verify_parts {P : Primitives} (C : XeddsaCurveWitness P)
    (sk h1Digest hDigest : Bytes) :
    let keyData := clampScalar25519 sk
    let a := P.scalarFromBytesModOrder keyData
    let capA := P.compress (edBaseMul P a)
    let capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
    let sig := xeddsaSignFromDigests P sk h1Digest hDigest
    let pk := P.x25519Base sk
    (pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0)) = true ∧
      ∃ edPk : Bytes,
        P.montToEd pk ((sig.getD 63 0 &&& 0x80) >>> 7) = some edPk ∧
        P.compress edPk = capA ∧
        sig.take 32 = capR ∧
        (let minusCapA := P.edNeg edPk
         let sRaw := sig.drop 32
         let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
         let h := P.scalarFromWide hDigest
         let sScalar := P.scalarFromBytesModOrder sClamped
         (P.compress (P.doubleScalarMulBasepoint h minusCapA sScalar) == sig.take 32) = true) := by
  dsimp only
  set keyData := clampScalar25519 sk
  set aScalar : ZMod l25519 := clampedScalarZMod sk
  have ha_eq : P.scalarFromBytesModOrder keyData = encodeScalarBytes aScalar := by
    rw [C.scalarMod_eq, fitBytesRef_of_length_eq (clampScalar25519_length sk)]
    rfl
  set capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
  have hcapA_eq : capA = C.compressEd aScalar := by
    dsimp only [capA]
    rw [ha_eq, compress_edBaseMul C]
  set rScalar : ZMod l25519 := decodeScalarBytes (fitBytesRef 64 h1Digest)
  have hr_eq : P.scalarFromWide h1Digest = encodeScalarBytes rScalar := C.scalarWide_eq h1Digest
  set capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
  have hcapR_eq : capR = C.compressEd rScalar := by
    dsimp only [capR]
    rw [hr_eq, compress_edBaseMul C]
  have hcapR_len : capR.length = 32 := by
    rw [hcapR_eq]; exact C.compressEd_len rScalar
  set hScalar : ZMod l25519 := decodeScalarBytes (fitBytesRef 64 hDigest)
  have hh_eq : P.scalarFromWide hDigest = encodeScalarBytes hScalar := C.scalarWide_eq hDigest
  set sVal : ZMod l25519 := hScalar * aScalar + rScalar
  set sBytes := P.scalarAdd (P.scalarMul (P.scalarFromWide hDigest) (P.scalarFromBytesModOrder keyData))
    (P.scalarFromWide h1Digest)
  have hsBytes_eq : sBytes = encodeScalarBytes sVal := by
    dsimp only [sBytes, sVal]
    rw [hh_eq, ha_eq, hr_eq, C.scalarMul_eq, C.scalarAdd_eq]
  have hsBytes_len : sBytes.length = 32 := by
    rw [hsBytes_eq]; exact encodeScalarBytes_length sVal
  have hsByte31_lt : (sBytes.getD 31 0).toNat < 32 := by
    rw [hsBytes_eq]; exact encodeScalarBytes_byte31_lt_32 sVal
  set b63 : UInt8 := (sBytes.getD 31 0 &&& 0x7F) ||| (capA.getD 31 0 &&& 0x80)
  set sig := xeddsaSignFromDigests P sk h1Digest hDigest
  have hsig_def : sig = capR ++ sBytes.take 31 ++ [b63] := rfl
  have htake31_len : (sBytes.take 31).length = 31 := by simp [hsBytes_len]
  have hsig_len : sig.length = 64 := by
    rw [hsig_def]
    simp [hcapR_len, htake31_len]
  have hsig_getD63 : sig.getD 63 0 = b63 := by
    rw [hsig_def, List.append_assoc, getD_append_right (by omega)]
    have hidx : 63 - capR.length = 31 := by omega
    rw [hidx, getD_append_right (by omega)]
    have hidx2 : 31 - (sBytes.take 31).length = 0 := by omega
    rw [hidx2]
    rfl
  have hpk_len : (P.x25519Base sk).length = 32 := C.x25519Base_len sk
  have hb63_60 : (sig.getD 63 0 &&& 0x60) = 0 := by
    rw [hsig_getD63]
    exact packedByte63_and_60 hsByte31_lt
  have hguard :
      ((P.x25519Base sk).length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0)) =
        true := by
    rw [hpk_len, hsig_len, hb63_60]
    rfl
  have hsignBit_eq : ((sig.getD 63 0 &&& 0x80) >>> 7) = C.edSign aScalar := by
    rw [hsig_getD63, packedByte63_signBit hsByte31_lt, hcapA_eq, C.compressEd_signBit]
  obtain ⟨edPk, hmont, hrep_edPk_raw⟩ :=
    C.montToEd_base sk (C.edSign (clampedScalarZMod sk)) (C.edSign_bool (clampedScalarZMod sk))
  have hrep_edPk : C.RepresentsEd aScalar edPk := by
    simpa only [beq_self_eq_true, ↓reduceIte] using hrep_edPk_raw
  have hcompress_edPk : P.compress edPk = capA := by
    rw [C.compress_of_represents hrep_edPk, hcapA_eq]
  have hsig_take32 : sig.take 32 = capR := by
    rw [hsig_def, List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  have hsig_drop32 : sig.drop 32 = sBytes.take 31 ++ [b63] := by
    rw [hsig_def, List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  refine ⟨hguard, edPk, ?_, hcompress_edPk, hsig_take32, ?_⟩
  · rw [hsignBit_eq]
    exact hmont
  · rw [hsig_drop32]
    set sRaw := sBytes.take 31 ++ [b63]
    have hsRaw_take31 : sRaw.take 31 = sBytes.take 31 := by
      dsimp only [sRaw]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hsRaw_getD31 : sRaw.getD 31 0 = b63 := by
      dsimp only [sRaw]
      rw [getD_append_right (by omega)]
      have hidx : 31 - (sBytes.take 31).length = 0 := by omega
      rw [hidx]
      rfl
    have hsClamped_eq : sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F] = sBytes := by
      rw [hsRaw_take31, hsRaw_getD31, packedByte63_and_7f hsByte31_lt,
        take31_append_last_of_length_32 hsBytes_len]
    rw [hsClamped_eq, hsBytes_eq]
    have hsScalar_eq :
        P.scalarFromBytesModOrder (encodeScalarBytes sVal) = encodeScalarBytes sVal := by
      rw [C.scalarMod_eq, fitBytesRef_of_length_eq (encodeScalarBytes_length sVal),
        decodeScalarBytes_encodeScalarBytes]
    rw [hsScalar_eq, hh_eq, hsig_take32, hcapR_eq]
    have hminus : C.RepresentsEd (-aScalar) (P.edNeg edPk) := C.edNeg_represents hrep_edPk
    have hdsmb : C.RepresentsEd (hScalar * (-aScalar) + sVal)
        (P.doubleScalarMulBasepoint (encodeScalarBytes hScalar) (P.edNeg edPk)
          (encodeScalarBytes sVal)) :=
      C.dsmb_represents hScalar sVal hminus
    have halg : hScalar * (-aScalar) + sVal = rScalar := by
      dsimp only [sVal]
      ring
    rw [halg] at hdsmb
    rw [C.compress_of_represents hdsmb]
    exact beq_self_eq_true (C.compressEd rScalar)

/-- Honest signing `xeddsaSignRef P` passes `xeddsaVerifyRef P (P.x25519Base sk)` under
`XeddsaCurveLaws P`. -/
theorem xeddsaSignRef_correct {P : Primitives} (hCurve : XeddsaCurveLaws P)
    (sk m rand : Bytes) :
    xeddsaVerifyRef P (P.x25519Base sk) m (xeddsaSignRef P sk m rand) = true := by
  obtain ⟨C⟩ := hCurve
  set keyData := clampScalar25519 sk
  set h1Digest := P.sha512 (xeddsaHashPrefix ++ keyData ++ m ++ fitBytesRef 64 rand)
  set capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
  set capR := P.compress (edBaseMul P (P.scalarFromWide h1Digest))
  set hDigest := P.sha512 (capR ++ capA ++ m)
  have hsig_eq : xeddsaSignRef P sk m rand = xeddsaSignFromDigests P sk h1Digest hDigest := rfl
  rw [hsig_eq]
  obtain ⟨hguard, edPk, hmont, hcompA, htakeR, hcheck⟩ :=
    xeddsaSignFromDigests_verify_parts C sk h1Digest hDigest
  unfold xeddsaVerifyRef
  rw [hguard]
  simp only [↓reduceIte]
  rw [hmont]
  dsimp only
  rw [hcompA]
  have hdigest_eq :
      P.sha512 ((xeddsaSignFromDigests P sk h1Digest hDigest).take 32 ++ capA ++ m) = hDigest := by
    rw [htakeR]
  rw [hdigest_eq]
  exact hcheck

/-- Overriding `sigSign` with `xeddsaSignRef P` preserves `WellFormedPrimitivesδ` under
`XeddsaCurveLaws P`. -/
theorem wellFormedPrimitivesδ_with_xeddsaSignRef {P : Primitives}
    (hwf : WellFormedPrimitivesδ P) (hCurve : XeddsaCurveLaws P) :
    WellFormedPrimitivesδ { P with sigSign := xeddsaSignRef P } where
  sha256Compress_len := hwf.sha256Compress_len
  sha512Compress_len := hwf.sha512Compress_len
  aesEncBlock_len := hwf.aesEncBlock_len
  aesDecBlock_len := hwf.aesDecBlock_len
  aesBlock_corr := hwf.aesBlock_corr
  sha512_eq_ref := hwf.sha512_eq_ref
  hkdfDerive96_eq_ref := hwf.hkdfDerive96_eq_ref
  rootCreateChain_eq_ref := hwf.rootCreateChain_eq_ref
  chainKdfSeed_eq_ref := hwf.chainKdfSeed_eq_ref
  chainKdfNext_eq_ref := hwf.chainKdfNext_eq_ref
  deriveMsgKeys_eq_ref := hwf.deriveMsgKeys_eq_ref
  aeadEnc_eq_ref := hwf.aeadEnc_eq_ref
  aeadDec_eq_ref := hwf.aeadDec_eq_ref
  x25519_clamp := hwf.x25519_clamp
  x25519Base_clamp := hwf.x25519Base_clamp
  x25519_base_ne_zero := hwf.x25519_base_ne_zero
  x25519_zero_iff := hwf.x25519_zero_iff
  kemDecaps_isSome := hwf.kemDecaps_isSome
  kemEncaps_isSome := hwf.kemEncaps_isSome
  x25519_comm := hwf.x25519_comm
  canon_base := hwf.canon_base
  canon_x25519 := hwf.canon_x25519
  sigPkGen_eq_x25519Base := hwf.sigPkGen_eq_x25519Base
  pow8_idemp := hwf.pow8_idemp
  pow8_x25519_comm := hwf.pow8_x25519_comm
  ddh_consistent := hwf.ddh_consistent
  ddh_consistent_left := hwf.ddh_consistent_left
  ddh_symm := hwf.ddh_symm
  isValidDhTriple_eq_ref := hwf.isValidDhTriple_eq_ref
  x25519_pow8_congr := hwf.x25519_pow8_congr
  x25519_congr_of_base_eq := hwf.x25519_congr_of_base_eq
  canon_pow8_inj := hwf.canon_pow8_inj
  x25519_len := hwf.x25519_len
  x25519Base_len := hwf.x25519Base_len
  pow8_len := hwf.pow8_len
  sha512_len := hwf.sha512_len
  scalarMul_len := hwf.scalarMul_len
  scalarAdd_len := hwf.scalarAdd_len
  scalarFromBytesModOrder_len := hwf.scalarFromBytesModOrder_len
  scalarFromWide_len := hwf.scalarFromWide_len
  montToEd_len := hwf.montToEd_len
  edNeg_len := hwf.edNeg_len
  doubleScalarMulBasepoint_len := hwf.doubleScalarMulBasepoint_len
  compress_len := hwf.compress_len
  sigVerify_eq_xeddsaVerifyRef := hwf.sigVerify_eq_xeddsaVerifyRef
  isCanonical_eq_isCanonicalRef := hwf.isCanonical_eq_isCanonicalRef
  kemKeyGen_valid := hwf.kemKeyGen_valid
  kemEncaps_len := hwf.kemEncaps_len
  kemDecaps_len := hwf.kemDecaps_len
  spqrInitSend_some := hwf.spqrInitSend_some
  aead_corr := hwf.aead_corr
  sig_corr := fun sk msg r => by
    change P.sigVerify (P.sigPkGen sk) msg (xeddsaSignRef P sk msg r) = true
    rw [hwf.sigVerify_eq_xeddsaVerifyRef, hwf.sigPkGen_eq_x25519Base]
    exact xeddsaSignRef_correct hCurve sk msg r
  spqr_corr := hwf.spqr_corr
  spqrInitRecv_salt_len := hwf.spqrInitRecv_salt_len

private theorem simulateQ_query_bind_run {α : Type}
    (t : Bytes) (mx : Bytes → OracleComp sha512RoSpec α) (s : sha512RoSpec.QueryCache) :
    (simulateQ sha512RoImpl (liftM (OracleSpec.query (spec := sha512RoSpec) t) >>= mx)).run s =
      (sha512RoBaseImpl.withCaching t).run s >>= fun p : Bytes × sha512RoSpec.QueryCache =>
        (simulateQ sha512RoImpl (mx p.1)).run p.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-- In the SHA-512 ROM, `xeddsaSignRo` followed by `xeddsaVerifyRo` in the shared cache accepts
with probability `1`. -/
theorem xeddsaSignRo_verifyRo_prob_one {P : Primitives} (hCurve : XeddsaCurveLaws P)
    (sk m rand : Bytes) (cache : sha512RoSpec.QueryCache) :
    𝒟[(simulateQ sha512RoImpl (do
        let sig ← xeddsaSignRo P sk m rand
        xeddsaVerifyRo P (P.x25519Base sk) m sig)).run' cache] {true} = 1 := by
  obtain ⟨C⟩ := hCurve
  show 𝒟[(simulateQ sha512RoImpl (do
      let sig ← xeddsaSignRo P sk m rand
      xeddsaVerifyRo P (P.x25519Base sk) m sig)).run' cache] {b : Bool | b = true} = 1
  rw [evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  intro b hb
  rw [StateT.run'_eq, support_map] at hb
  obtain ⟨⟨bOut, cacheFinal⟩, hmem, rfl⟩ := hb
  dsimp only
  unfold xeddsaSignRo at hmem
  rw [bind_assoc, simulateQ_query_bind_run, support_bind, Set.mem_iUnion] at hmem
  obtain ⟨⟨h1Val, cache1⟩, hmem⟩ := hmem
  rw [Set.mem_iUnion] at hmem
  obtain ⟨_, hmem2⟩ := hmem
  dsimp only at hmem2
  rw [bind_assoc, simulateQ_query_bind_run, support_bind, Set.mem_iUnion] at hmem2
  obtain ⟨⟨hVal, cache2⟩, hmem2⟩ := hmem2
  rw [Set.mem_iUnion] at hmem2
  obtain ⟨hh2, hmem3⟩ := hmem2
  dsimp only at hmem3
  rw [pure_bind] at hmem3
  let keyData := clampScalar25519 sk
  let capA := P.compress (edBaseMul P (P.scalarFromBytesModOrder keyData))
  let capR := P.compress (edBaseMul P (P.scalarFromWide h1Val))
  have hcached : cache2 (capR ++ capA ++ m) = some hVal :=
    QueryImpl.withCaching_run_caches sha512RoBaseImpl (capR ++ capA ++ m) cache1
      (hVal, cache2) hh2
  let sig := xeddsaSignFromDigests P sk h1Val hVal
  change (bOut, cacheFinal) ∈ support ((simulateQ sha512RoImpl
    (xeddsaVerifyRo P (P.x25519Base sk) m sig)).run cache2) at hmem3
  obtain ⟨hguard, edPk, hmont, hcompA, htakeR, hcheck⟩ :=
    xeddsaSignFromDigests_verify_parts C sk h1Val hVal
  unfold xeddsaVerifyRo at hmem3
  rw [hguard] at hmem3
  simp only [↓reduceIte] at hmem3
  rw [hmont] at hmem3
  dsimp only at hmem3
  rw [simulateQ_query_bind_run, hcompA, htakeR,
    QueryImpl.withCaching_run_some sha512RoBaseImpl hcached, pure_bind] at hmem3
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem3
  rw [htakeR] at hcheck
  exact hmem3.1.trans hcheck

theorem xeddsaSignRoundtrip_holds : XeddsaSignRoundtrip :=
  ⟨fun _ hCurve sk m rand => xeddsaSignRef_correct hCurve sk m rand,
   fun _ hwf hCurve => wellFormedPrimitivesδ_with_xeddsaSignRef hwf hCurve,
   fun _ hCurve sk m rand cache => xeddsaSignRo_verifyRo_prob_one hCurve sk m rand cache⟩

end Computational.Proofs.SignalPqxdh.XeddsaRom.Roundtrip
