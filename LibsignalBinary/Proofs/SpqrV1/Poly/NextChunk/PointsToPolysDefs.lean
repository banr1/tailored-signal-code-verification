/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
public import LibsignalBinary.Proofs.SpqrV1.Poly.Repr
public import ProofLib.SepLogic.Bytes
import ProofLib.VCGen
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure -- shake: keep

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Pure and Representation Helpers

**Checked by Lean.**

Byte-slice bridges for `polysToBytes`, `gf16SliceAt`, and `polyOf`, together with `.rodata`
slicing and NEON word-splitting lemmas for `COMPLETE_POINTS_POLYS_{5,30,34,36}`.
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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.CodeLayout

/-! ## 1. `polysToBytes` Length and Slicing Lemmas -/

@[simp]
theorem polysToBytes_append (ps1 ps2 : List Poly) :
    polysToBytes (ps1 ++ ps2) = polysToBytes ps1 ++ polysToBytes ps2 := by
  unfold polysToBytes
  exact List.flatMap_append

theorem polysToBytes_length_of_fixed {polys : List Poly} {m : Nat}
    (hlen : ∀ p ∈ polys, p.coefficients.length = m) :
    (polysToBytes polys).length = 2 * m * polys.length := by
  induction polys with
  | nil => simp
  | cons p ps ih =>
    have hp : p.coefficients.length = m := hlen p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.coefficients.length = m :=
      fun q hq => hlen q (List.mem_cons_of_mem p hq)
    simp only [polysToBytes_cons, List.length_append, gf16SliceBytes_length, hp, ih hps,
      List.length_cons]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem polysToBytes_drop_of_fixed {polys : List Poly} {m : Nat}
    (hlen : ∀ p ∈ polys, p.coefficients.length = m) :
    ∀ (i : Nat),
      (polysToBytes polys).drop (2 * m * i) = polysToBytes (polys.drop i) := by
  induction polys with
  | nil =>
    intro i
    simp
  | cons p ps ih =>
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have hp : p.coefficients.length = m := hlen p (List.mem_cons_self ..)
      have hps : ∀ q ∈ ps, q.coefficients.length = m :=
        fun q hq => hlen q (List.mem_cons_of_mem p hq)
      have hplen : (gf16SliceBytes p.coefficients).length = 2 * m := by
        simp [hp]
      have hmul : 2 * m * (i + 1) = (gf16SliceBytes p.coefficients).length + 2 * m * i := by
        rw [Nat.mul_add, Nat.mul_one, hplen, Nat.add_comm]
      rw [polysToBytes_cons, List.drop_succ_cons, hmul, ← List.drop_drop, List.drop_left]
      exact ih hps i

theorem polysToBytes_drop_take_of_fixed {polys : List Poly} {m : Nat}
    (hlen : ∀ p ∈ polys, p.coefficients.length = m) {i : Nat} (hi : i < polys.length) :
    ((polysToBytes polys).drop (2 * m * i)).take (2 * m) =
      gf16SliceBytes (polys[i]'hi).coefficients := by
  rw [polysToBytes_drop_of_fixed hlen i]
  have hcons : polys.drop i = (polys[i]'hi) :: polys.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  rw [hcons, polysToBytes_cons]
  have hp : (polys[i]'hi).coefficients.length = m :=
    hlen (polys[i]'hi) (List.getElem_mem hi)
  have hplen : 2 * m = (gf16SliceBytes (polys[i]'hi).coefficients).length := by
    simp [hp]
  rw [hplen, List.take_left]

/-! ## 2. `COMPLETE_POINTS_POLYS_{30,34,36}` Unfolding & Slicing Lemmas -/

theorem completePointsPolys5_spec :
    (∃ cps, COMPLETE_POINTS_POLYS_5 = .ok cps ∧
      constPolysToPolys cps = extractCompletePolys COMPLETE_POINTS_POLYS_5) ∧
    (extractCompletePolys COMPLETE_POINTS_POLYS_5).length = 5 ∧
    (∀ p ∈ extractCompletePolys COMPLETE_POINTS_POLYS_5, p.coefficients.length = 5) :=
  let h := checkCompletePolys_spec checkCompletePolys5
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem completePointsPolys30_spec :
    (∃ cps, COMPLETE_POINTS_POLYS_30 = .ok cps ∧
      constPolysToPolys cps = extractCompletePolys COMPLETE_POINTS_POLYS_30) ∧
    (extractCompletePolys COMPLETE_POINTS_POLYS_30).length = 30 ∧
    (∀ p ∈ extractCompletePolys COMPLETE_POINTS_POLYS_30, p.coefficients.length = 30) :=
  let h := checkCompletePolys_spec checkCompletePolys30
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem completePointsPolys34_spec :
    (∃ cps, COMPLETE_POINTS_POLYS_34 = .ok cps ∧
      constPolysToPolys cps = extractCompletePolys COMPLETE_POINTS_POLYS_34) ∧
    (extractCompletePolys COMPLETE_POINTS_POLYS_34).length = 34 ∧
    (∀ p ∈ extractCompletePolys COMPLETE_POINTS_POLYS_34, p.coefficients.length = 34) :=
  let h := checkCompletePolys_spec checkCompletePolys34
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem completePointsPolys36_spec :
    (∃ cps, COMPLETE_POINTS_POLYS_36 = .ok cps ∧
      constPolysToPolys cps = extractCompletePolys COMPLETE_POINTS_POLYS_36) ∧
    (extractCompletePolys COMPLETE_POINTS_POLYS_36).length = 36 ∧
    (∀ p ∈ extractCompletePolys COMPLETE_POINTS_POLYS_36, p.coefficients.length = 36) :=
  let h := checkCompletePolys_spec checkCompletePolys36
  ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## 3. `gf16SliceAt` and `polyOf` Byte-Slice Bridges -/

theorem gf16SliceAt_eq_pointsToBytes (ptr : BitVec 64) (cs : List GF16) :
    gf16SliceAt ptr cs = (ptr ↦ₛ gf16SliceBytes cs) := by
  induction cs generalizing ptr with
  | nil =>
    simp [gf16SliceAt, arrayAt, gf16SliceBytes]
  | cons g cs ih =>
    have ih' : arrayAt gf16At 2 (ptr + 2#64) cs = ((ptr + 2#64) ↦ₛ gf16SliceBytes cs) :=
      ih (ptr + 2#64)
    simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, gf16SliceBytes_cons]
    have hsplit :
        (g.value.extractLsb' 0 8 :: g.value.extractLsb' 8 8 :: gf16SliceBytes cs) =
          [g.value.extractLsb' 0 8, g.value.extractLsb' 8 8] ++ gf16SliceBytes cs := rfl
    rw [hsplit, pointsToBytes_append]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    have h16 : (ptr ↦₁₆ g.value) = (ptr ↦ₛ [g.value.extractLsb' 0 8, g.value.extractLsb' 8 8]) := by
      rw [pointsTo16_eq_pointsToBytes]
      rfl
    rw [h16, ih']

theorem polyOf_of_pointsToBytes (A : RustAlloc) (v ptr : BitVec 64) (p : Poly) (m : Nat)
    (hm_pos : 0 < m) (hm_lt : m * 2 < 2 ^ 63) (hptr : ptr ≠ 0#64) (hlen : p.coefficients.length = m) :
    ((v ↦₆₄ BitVec.ofNat 64 m) ∗
     ((v + 8#64) ↦₆₄ ptr) ∗
     ((v + 16#64) ↦₆₄ BitVec.ofNat 64 m) ∗
     A.live ptr (2 * m) 2 ∗
     (ptr ↦ₛ gf16SliceBytes p.coefficients)) ⊢
    polyOf A v p := by
  rw [← gf16SliceAt_eq_pointsToBytes]
  have hm64 : m < 2 ^ 64 := by omega
  have hcap_toNat : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  have hcap_ne : BitVec.ofNat 64 m ≠ (0 : BitVec 64) := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hcap_toNat] at this
    change m = 0 at this
    omega
  have hpure : m ≤ (BitVec.ofNat 64 m).toNat ∧
      (BitVec.ofNat 64 m).toNat * 2 < 2 ^ 63 ∧ ptr ≠ (0 : BitVec 64) := by
    rw [hcap_toNat]
    exact ⟨Nat.le_refl m, hm_lt, hptr⟩
  have h1 :
      ((v ↦₆₄ BitVec.ofNat 64 m) ∗
       ((v + 8#64) ↦₆₄ ptr) ∗
       ((v + 16#64) ↦₆₄ BitVec.ofNat 64 m) ∗
       A.live ptr (2 * m) 2 ∗
       gf16SliceAt ptr p.coefficients) ⊢
      polyAt A v (BitVec.ofNat 64 m) ptr p := by
    unfold polyAt vecAt vecHeader vecBuf gf16Stride gf16Align gf16SliceAt
    simp only [hlen, hcap_ne, ↓reduceIte]
    rw [sepConj_pure_left_comm]
    refine Entails.pure_right hpure ?_
    simp only [hcap_toNat, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp,
      Nat.mul_comm m 2]
    exact Entails.of_eq (by ac_rfl)
  refine Entails.trans h1 ?_
  unfold polyOf vecOf
  exact Entails.sepExists_right (BitVec.ofNat 64 m) (Entails.sepExists_right ptr (Entails.refl _))

theorem polyOf_of_pointsToBytes_off (A : RustAlloc) (base off0 off8 off16 ptr : BitVec 64)
    (p : Poly) (m : Nat)
    (h8 : (base + off0) + 8#64 = base + off8)
    (h16 : (base + off0) + 16#64 = base + off16)
    (hm_pos : 0 < m) (hm_lt : m * 2 < 2 ^ 63) (hptr : ptr ≠ 0#64) (hlen : p.coefficients.length = m) :
    (((base + off0) ↦₆₄ BitVec.ofNat 64 m) ∗
     ((base + off8) ↦₆₄ ptr) ∗
     ((base + off16) ↦₆₄ BitVec.ofNat 64 m) ∗
     A.live ptr (2 * m) 2 ∗
     (ptr ↦ₛ gf16SliceBytes p.coefficients)) ⊢
    polyOf A (base + off0) p := by
  rw [← h8, ← h16]
  exact polyOf_of_pointsToBytes A (base + off0) ptr p m hm_pos hm_lt hptr hlen

/-! ## 4. `COMPLETE_POINTS_POLYS_5` Exact Value and `.rodata` Slicing -/

def cp5Polys : List (PolyConst 5) :=
  [ { coefficients := [⟨0x0001#16⟩, ⟨0xb405#16⟩, ⟨0x9605#16⟩, ⟨0x7803#16⟩, ⟨0x5a02#16⟩] }
  , { coefficients := [⟨0x0000#16⟩, ⟨0x5003#16⟩, ⟨0xc007#16⟩, ⟨0x7803#16⟩, ⟨0xe806#16⟩] }
  , { coefficients := [⟨0x0000#16⟩, ⟨0xf006#16⟩, ⟨0x1400#16⟩, ⟨0x7803#16⟩, ⟨0x9c05#16⟩] }
  , { coefficients := [⟨0x0000#16⟩, ⟨0x9b68#16⟩, ⟨0xf006#16⟩, ⟨0x7803#16⟩, ⟨0x136d#16⟩] }
  , { coefficients := [⟨0x0000#16⟩, ⟨0x8f68#16⟩, ⟨0xb204#16⟩, ⟨0x0000#16⟩, ⟨0x3d6c#16⟩] } ]

def cp5BytesLit : List (BitVec 8) :=
  polysToBytes (constPolysToPolys cp5Polys)

theorem completePointsPolys5_eq :
    COMPLETE_POINTS_POLYS_5 = .ok cp5Polys := by
  decide +kernel

theorem completePointsPolys5Bytes_eq_lit :
    completePointsPolys5Bytes = cp5BytesLit := by
  unfold completePointsPolys5Bytes extractCompletePolys cp5BytesLit
  rw [completePointsPolys5_eq]

/-- The unread bytes of `COMPLETE_POINTS_POLYS_5` in `.rodata` (offsets `8..10`, `18..20`, `28..30`, `38..50`). -/
def completePointsPolys5RestAt (b : BitVec 64) : SepProp :=
  ((b + bv% (ls_bytes% "010005b405960378025a0000" + 8)) ↦ᵣ (completePointsPolys5Bytes.drop 8).take 2) ∗
  ((b + bv% (ls_bytes% "010005b405960378025a0000" + 18)) ↦ᵣ (completePointsPolys5Bytes.drop 18).take 2) ∗
  ((b + bv% (ls_bytes% "010005b405960378025a0000" + 28)) ↦ᵣ (completePointsPolys5Bytes.drop 28).take 2) ∗
  ((b + bv% (ls_bytes% "010005b405960378025a0000" + 38)) ↦ᵣ completePointsPolys5Bytes.drop 38)

theorem completePointsPolys5At_split (b : BitVec 64) :
    completePointsPolys5At b =
      ((b + bv% (ls_bytes% "010005b405960378025a0000")) ↦₆₄ᵣ 0x78039605b4050001#64) ∗
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) ↦₆₄ᵣ 0x7803c00750030000#64) ∗
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) ↦₆₄ᵣ 0x78031400f0060000#64) ∗
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) ↦₆₄ᵣ 0x7803f0069b680000#64) ∗
      completePointsPolys5RestAt b := by
  unfold completePointsPolys5At completePointsPolys5RestAt
  have hbase : b + bv% (ls_xref% 0x65758 0x6575c) = b + bv% (ls_bytes% "010005b405960378025a0000") := rfl
  rw [hbase]
  have hlen : completePointsPolys5Bytes.length = 50 := completePointsPolys5Bytes_length
  have hw0 : ((b + bv% (ls_bytes% "010005b405960378025a0000")) ↦ᵣ completePointsPolys5Bytes.take 8) =
      ((b + bv% (ls_bytes% "010005b405960378025a0000")) ↦₆₄ᵣ 0x78039605b4050001#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (b + bv% (ls_bytes% "010005b405960378025a0000")) completePointsPolys5Bytes 0 (by omega)
    rw [List.drop_zero] at h
    have hp : pack64 (cp5BytesLit.getD 0 0#8) (cp5BytesLit.getD 1 0#8)
        (cp5BytesLit.getD 2 0#8) (cp5BytesLit.getD 3 0#8)
        (cp5BytesLit.getD 4 0#8) (cp5BytesLit.getD 5 0#8)
        (cp5BytesLit.getD 6 0#8) (cp5BytesLit.getD 7 0#8) = 0x78039605b4050001#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw1 : ((b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) ↦ᵣ (completePointsPolys5Bytes.drop 10).take 8) =
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) ↦₆₄ᵣ 0x7803c00750030000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) completePointsPolys5Bytes 10 (by omega)
    have hp : pack64 (cp5BytesLit.getD 10 0#8) (cp5BytesLit.getD 11 0#8)
        (cp5BytesLit.getD 12 0#8) (cp5BytesLit.getD 13 0#8)
        (cp5BytesLit.getD 14 0#8) (cp5BytesLit.getD 15 0#8)
        (cp5BytesLit.getD 16 0#8) (cp5BytesLit.getD 17 0#8) = 0x7803c00750030000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw2 : ((b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) ↦ᵣ (completePointsPolys5Bytes.drop 20).take 8) =
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) ↦₆₄ᵣ 0x78031400f0060000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) completePointsPolys5Bytes 20 (by omega)
    have hp : pack64 (cp5BytesLit.getD 20 0#8) (cp5BytesLit.getD 21 0#8)
        (cp5BytesLit.getD 22 0#8) (cp5BytesLit.getD 23 0#8)
        (cp5BytesLit.getD 24 0#8) (cp5BytesLit.getD 25 0#8)
        (cp5BytesLit.getD 26 0#8) (cp5BytesLit.getD 27 0#8) = 0x78031400f0060000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw3 : ((b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) ↦ᵣ (completePointsPolys5Bytes.drop 30).take 8) =
      ((b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) ↦₆₄ᵣ 0x7803f0069b680000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) completePointsPolys5Bytes 30 (by omega)
    have hp : pack64 (cp5BytesLit.getD 30 0#8) (cp5BytesLit.getD 31 0#8)
        (cp5BytesLit.getD 32 0#8) (cp5BytesLit.getD 33 0#8)
        (cp5BytesLit.getD 34 0#8) (cp5BytesLit.getD 35 0#8)
        (cp5BytesLit.getD 36 0#8) (cp5BytesLit.getD 37 0#8) = 0x7803f0069b680000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hs0 := pointsToBytesRO_split3 (b + bv% (ls_bytes% "010005b405960378025a0000")) completePointsPolys5Bytes 8 2 (by omega)
  have hs1 := pointsToBytesRO_split3 (b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) (completePointsPolys5Bytes.drop 10) 8 2 (by simp [hlen])
  have hs2 := pointsToBytesRO_split3 (b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) (completePointsPolys5Bytes.drop 20) 8 2 (by simp [hlen])
  have hs3 := pointsToBytesRO_split3 (b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) (completePointsPolys5Bytes.drop 30) 8 0 (by simp [hlen])
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    List.drop_drop, Nat.reduceAdd, List.take_zero, pointsToBytesRO_nil, emp_sepConj] at hs0 hs1 hs2 hs3
  rw [hs0, hs1, hs2, hs3, hw0, hw1, hw2, hw3]
  ac_rfl

/-! ## 5. Degree-4 `polyOf` Helpers and 60/68/72-Byte Word Splitting Lemmas -/

theorem memRegion_split_basis5 (p : BitVec 64) :
    memRegion p 120 =
      memRegion p 24 ∗ memRegion (p + 24#64) 24 ∗ memRegion (p + 48#64) 24 ∗
      memRegion (p + 72#64) 24 ∗ memRegion (p + 96#64) 24 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 24) (k := 96) (b' := p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 24) (k := 72) (b' := p + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 48#64) (n := 24) (k := 48) (b' := p + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 72#64) (n := 24) (k := 24) (b' := p + 96#64) rfl (by bv_omega) (by decide)]

theorem polyAt_deg4_intro (A : RustAlloc) (addr p : BitVec 64)
    (w03 : BitVec 64) (c0 c1 c2 c3 c4 : BitVec 16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w03)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w03)
    (hc2 : c2 = BitVec.extractLsb' 32 16 w03)
    (hc3 : c3 = BitVec.extractLsb' 48 16 w03) :
    ((addr ↦₆₄ 5#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 5#64) ∗
     A.live p 10 2 ∗ (p ↦₆₄ w03) ∗ ((p + 8#64) ↦₁₆ c4)) ⊢
    polyAt A addr 5#64 p ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩, ⟨c3⟩, ⟨c4⟩]⟩ := by
  subst hc0 hc1 hc2 hc3
  rw [pointsTo64_split16 p w03]
  unfold polyAt vecAt vecHeader vecBuf gf16Stride gf16Align
  have h5ne : (5#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 5 ≤ (5#64 : BitVec 64).toNat ∧ (5#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, h5ne, ↓reduceIte,
    arrayAt, gf16At, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul,
    Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc,
    BitVec.reduceAdd]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  exact Entails.of_eq (by ac_rfl)

theorem polyOf_deg4_intro (A : RustAlloc) (addr p : BitVec 64)
    (w03 : BitVec 64) (c0 c1 c2 c3 c4 : BitVec 16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w03)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w03)
    (hc2 : c2 = BitVec.extractLsb' 32 16 w03)
    (hc3 : c3 = BitVec.extractLsb' 48 16 w03) :
    ((addr ↦₆₄ 5#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 5#64) ∗
     A.live p 10 2 ∗ (p ↦₆₄ w03) ∗ ((p + 8#64) ↦₁₆ c4)) ⊢
    polyOf A addr ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩, ⟨c3⟩, ⟨c4⟩]⟩ := by
  refine Entails.trans (polyAt_deg4_intro A addr p w03 c0 c1 c2 c3 c4 hp hc0 hc1 hc2 hc3) ?_
  unfold polyOf vecOf
  exact Entails.sepExists_right 5#64 (Entails.sepExists_right p (Entails.refl _))

theorem polyOf_deg4_intro_off (A : RustAlloc) (base off0 off8 off16 p : BitVec 64)
    (w03 : BitVec 64) (c0 c1 c2 c3 c4 : BitVec 16)
    (h8 : (base + off0) + 8#64 = base + off8)
    (h16 : (base + off0) + 16#64 = base + off16)
    (hp : p ≠ 0#64)
    (hc0 : c0 = BitVec.extractLsb' 0 16 w03)
    (hc1 : c1 = BitVec.extractLsb' 16 16 w03)
    (hc2 : c2 = BitVec.extractLsb' 32 16 w03)
    (hc3 : c3 = BitVec.extractLsb' 48 16 w03) :
    (((base + off0) ↦₆₄ 5#64) ∗ ((base + off8) ↦₆₄ p) ∗ ((base + off16) ↦₆₄ 5#64) ∗
     A.live p 10 2 ∗ (p ↦₆₄ w03) ∗ ((p + 8#64) ↦₁₆ c4)) ⊢
    polyOf A (base + off0) ⟨[⟨c0⟩, ⟨c1⟩, ⟨c2⟩, ⟨c3⟩, ⟨c4⟩]⟩ := by
  rw [← h8, ← h16]
  exact polyOf_deg4_intro A (base + off0) p w03 c0 c1 c2 c3 c4 hp hc0 hc1 hc2 hc3

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ d : BitVec 32,
      bs = unpack32 d ∧
      (∀ a : BitVec 64, (a ↦ᵣ bs) = (a ↦₃₂ᵣ d)) ∧
      (∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ d)) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  refine ⟨b3 ++ b2 ++ b1 ++ b0, (unpack32_pack32 b0 b1 b2 b3).symm,
    fun a => pointsToBytesRO4_eq_pointsTo32RO a b0 b1 b2 b3,
    fun a => pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3⟩

theorem exists_words_8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w : BitVec 64,
      bs = unpack64 w ∧
      (∀ a : BitVec 64, (a ↦ᵣ bs) = (a ↦₆₄ᵣ w)) ∧
      (∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₆₄ w)) := by
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 h
  refine ⟨w, hw, fun a => ?_, fun a => ?_⟩
  · rw [hw, ← pointsTo64RO_eq_pointsToBytesRO]
  · rw [hw, ← pointsTo64_eq_pointsToBytes]

theorem exists_words_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) := by
  obtain ⟨w0, w1, w2, w3, hbs, hrw⟩ := exists_unpack64_of_length_32 h
  refine ⟨w0, w1, w2, w3, fun a => ?_, hrw⟩
  rw [hbs, List.append_assoc, List.append_assoc,
      pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
      ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO]
  simp only [unpack64_length, BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_words_72 {bs : List (BitVec 8)} (h : bs.length = 72) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64,
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3) ∗
           ((a + 32#64) ↦₆₄ᵣ w4) ∗ ((a + 40#64) ↦₆₄ᵣ w5) ∗ ((a + 48#64) ↦₆₄ᵣ w6) ∗ ((a + 56#64) ↦₆₄ᵣ w7) ∗
           ((a + 64#64) ↦₆₄ᵣ w8))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
           ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
           ((a + 64#64) ↦₆₄ w8))) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 64).length = 8 := by simp [h]
  obtain ⟨w0, w1, w2, w7_tmp, hro0, hrw0⟩ := exists_words_32 h0
  obtain ⟨w4, w5, w6, w7, hro1, hrw1⟩ := exists_words_32 h1
  obtain ⟨w8, _, hro2, hrw2⟩ := exists_words_8 h2
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ bs.drop 64) := by
    have hd : (bs.drop 32).drop 32 = bs.drop 64 := by simp [List.drop_drop]
    rw [← hd, List.take_append_drop, List.take_append_drop]
  refine ⟨w0, w1, w2, w7_tmp, w4, w5, w6, w7, w8, fun a => ?_, fun a => ?_⟩
  · conv => lhs; rw [hsplit]
    rw [pointsToBytesRO_append, pointsToBytesRO_append, h0, h1, hro0, hro1, hro2]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · conv => lhs; rw [hsplit]
    rw [pointsToBytes_append, pointsToBytes_append, h0, h1, hrw0, hrw1, hrw2]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_words_68 {bs : List (BitVec 8)} (h : bs.length = 68) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (d8 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3) ∗
           ((a + 32#64) ↦₆₄ᵣ w4) ∗ ((a + 40#64) ↦₆₄ᵣ w5) ∗ ((a + 48#64) ↦₆₄ᵣ w6) ∗ ((a + 56#64) ↦₆₄ᵣ w7) ∗
           ((a + 64#64) ↦₃₂ᵣ d8))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
           ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
           ((a + 64#64) ↦₃₂ d8))) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 64).length = 4 := by simp [h]
  obtain ⟨w0, w1, w2, w3, hro0, hrw0⟩ := exists_words_32 h0
  obtain ⟨w4, w5, w6, w7, hro1, hrw1⟩ := exists_words_32 h1
  obtain ⟨d8, _, hro2, hrw2⟩ := exists_unpack32_of_length_4 h2
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ bs.drop 64) := by
    have hd : (bs.drop 32).drop 32 = bs.drop 64 := by simp [List.drop_drop]
    rw [← hd, List.take_append_drop, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, d8, fun a => ?_, fun a => ?_⟩
  · conv => lhs; rw [hsplit]
    rw [pointsToBytesRO_append, pointsToBytesRO_append, h0, h1, hro0, hro1, hro2]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · conv => lhs; rw [hsplit]
    rw [pointsToBytes_append, pointsToBytes_append, h0, h1, hrw0, hrw1, hrw2]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem pointsTo32RO_pair (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ᵣ lo) ∗ ((a + 4#64) ↦₃₂ᵣ hi)) = (a ↦₆₄ᵣ (hi ++ lo)) := by
  rw [pointsTo32RO_eq_pointsToBytesRO, pointsTo32RO_eq_pointsToBytesRO, pointsTo64RO_eq_pointsToBytesRO,
      unpack64_append32, pointsToBytesRO_append, unpack32_length]

theorem ro_shift_40_48 (a : BitVec 64) (d2 d3 d4 : BitVec 32) :
    ((a + 40#64) ↦₆₄ᵣ (d3 ++ d2)) ∗ ((a + 48#64) ↦₃₂ᵣ d4) =
      ((a + 40#64) ↦₃₂ᵣ d2) ∗ ((a + 44#64) ↦₆₄ᵣ (d4 ++ d3)) := by
  have h44 : a + 40#64 + 4#64 = a + 44#64 := by bv_arith
  have h48 : a + 44#64 + 4#64 = a + 48#64 := by bv_arith
  rw [← pointsTo32RO_pair (a + 40#64) d2 d3, h44,
      ← pointsTo32RO_pair (a + 44#64) d3 d4, h48, sepConj_assoc]

theorem rw_shift_40_48 (a : BitVec 64) (d2 d3 u48 : BitVec 32) :
    ((a + 40#64) ↦₆₄ (d3 ++ d2)) ∗ ((a + 48#64) ↦₃₂ u48) =
      ((a + 40#64) ↦₃₂ d2) ∗ ((a + 44#64) ↦₆₄ (u48 ++ d3)) := by
  have h44 : a + 40#64 + 4#64 = a + 44#64 := by bv_arith
  have h48 : a + 44#64 + 4#64 = a + 48#64 := by bv_arith
  rw [← pointsTo32_pair (a + 40#64) d2 d3, h44,
      ← pointsTo32_pair (a + 44#64) d3 u48, h48, sepConj_assoc]

theorem exists_words_60 {bs : List (BitVec 8)} (h : bs.length = 60) :
    ∃ (w0 w1 w2 w3 w4 : BitVec 64) (d2 d3 d4 : BitVec 32) (w7 : BitVec 64),
      (∀ a : BitVec 64,
        (a ↦ᵣ bs) =
          ((a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3) ∗
           ((a + 32#64) ↦₆₄ᵣ w4) ∗ ((a + 40#64) ↦₆₄ᵣ (d3 ++ d2)) ∗ ((a + 48#64) ↦₃₂ᵣ d4) ∗ ((a + 52#64) ↦₆₄ᵣ w7))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
           ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₃₂ d2) ∗ ((a + 44#64) ↦₆₄ (d4 ++ d3)) ∗ ((a + 52#64) ↦₆₄ w7))) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h32 : ((bs.drop 32).take 8).length = 8 := by simp [h]
  have h40 : ((bs.drop 40).take 4).length = 4 := by simp [h]
  have h44 : ((bs.drop 44).take 4).length = 4 := by simp [h]
  have h48 : ((bs.drop 48).take 4).length = 4 := by simp [h]
  have h52 : (bs.drop 52).length = 8 := by simp [h]
  obtain ⟨w0, w1, w2, w3, hro0, hrw0⟩ := exists_words_32 h0
  obtain ⟨w4, _, hro32, hrw32⟩ := exists_words_8 h32
  obtain ⟨d2, _, hro40, hrw40⟩ := exists_unpack32_of_length_4 h40
  obtain ⟨d3, _, hro44, hrw44⟩ := exists_unpack32_of_length_4 h44
  obtain ⟨d4, _, hro48, hrw48⟩ := exists_unpack32_of_length_4 h48
  obtain ⟨w7, _, hro52, hrw52⟩ := exists_words_8 h52
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 8 ++ ((bs.drop 40).take 4 ++
      ((bs.drop 44).take 4 ++ ((bs.drop 48).take 4 ++ bs.drop 52)))) := by
    have hd48 : (bs.drop 48).drop 4 = bs.drop 52 := by simp [List.drop_drop]
    have hd44 : (bs.drop 44).drop 4 = bs.drop 48 := by simp [List.drop_drop]
    have hd40 : (bs.drop 40).drop 4 = bs.drop 44 := by simp [List.drop_drop]
    have hd32 : (bs.drop 32).drop 8 = bs.drop 40 := by simp [List.drop_drop]
    rw [← hd48, List.take_append_drop, ← hd44, List.take_append_drop,
        ← hd40, List.take_append_drop, ← hd32, List.take_append_drop, List.take_append_drop]
  refine ⟨w0, w1, w2, w3, w4, d2, d3, d4, w7, fun a => ?_, fun a => ?_⟩
  · conv => lhs; rw [hsplit]
    rw [pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
        pointsToBytesRO_append, pointsToBytesRO_append,
        h0, h32, h40, h44, h48, hro0, hro32, hro40, hro44, hro48, hro52]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hp40 : ((a + 40#64) ↦₃₂ᵣ d2) ∗ (((a + 44#64) ↦₃₂ᵣ d3) ∗ (((a + 48#64) ↦₃₂ᵣ d4) ∗ ((a + 52#64) ↦₆₄ᵣ w7))) =
        ((a + 40#64) ↦₆₄ᵣ (d3 ++ d2)) ∗ (((a + 48#64) ↦₃₂ᵣ d4) ∗ ((a + 52#64) ↦₆₄ᵣ w7)) := by
      have h44' : a + 40#64 + 4#64 = a + 44#64 := by bv_arith
      rw [← sepConj_assoc ((a + 40#64) ↦₃₂ᵣ d2), ← h44', pointsTo32RO_pair]
    rw [hp40]
  · conv => lhs; rw [hsplit]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append,
        h0, h32, h40, h44, h48, hrw0, hrw32, hrw40, hrw44, hrw48, hrw52]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hp44 : ((a + 44#64) ↦₃₂ d3) ∗ (((a + 48#64) ↦₃₂ d4) ∗ ((a + 52#64) ↦₆₄ w7)) =
        ((a + 44#64) ↦₆₄ (d4 ++ d3)) ∗ ((a + 52#64) ↦₆₄ w7) := by
      have h48' : a + 44#64 + 4#64 = a + 48#64 := by bv_arith
      rw [← sepConj_assoc ((a + 44#64) ↦₃₂ d3), ← h48', pointsTo32_pair]
    rw [hp44]

theorem memRegion_split_32 (p : BitVec 64) :
    memRegion p 32 =
      ∃∗ u24 : BitVec 64, ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) ∗ ((p + 24#64) ↦₆₄ u24) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 24) (b' := p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 16) (b' := p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 8) (b' := p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64),
      ProofLib.memRegion_eight (p + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_split_72 (p : BitVec 64) :
    memRegion p 72 =
      ∃∗ u64 : BitVec 64, ∃∗ u56 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u40 : BitVec 64, ∃∗ u32 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) ∗ ((p + 24#64) ↦₆₄ u24) ∗
        ((p + 32#64) ↦₆₄ u32) ∗ ((p + 40#64) ↦₆₄ u40) ∗ ((p + 48#64) ↦₆₄ u48) ∗ ((p + 56#64) ↦₆₄ u56) ∗
        ((p + 64#64) ↦₆₄ u64) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 32) (k := 40) (b' := p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 32) (k := 8) (b' := p + 64#64) rfl (by bv_omega) (by decide),
      memRegion_split_32 p,
      memRegion_split_32 (p + 32#64),
      ProofLib.memRegion_eight (p + 64#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_split_68 (p : BitVec 64) :
    memRegion p 68 =
      ∃∗ u64 : BitVec 32, ∃∗ u56 : BitVec 64, ∃∗ u48 : BitVec 64,
      ∃∗ u40 : BitVec 64, ∃∗ u32 : BitVec 64, ∃∗ u24 : BitVec 64,
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) ∗ ((p + 24#64) ↦₆₄ u24) ∗
        ((p + 32#64) ↦₆₄ u32) ∗ ((p + 40#64) ↦₆₄ u40) ∗ ((p + 48#64) ↦₆₄ u48) ∗ ((p + 56#64) ↦₆₄ u56) ∗
        ((p + 64#64) ↦₃₂ u64) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 32) (k := 36) (b' := p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 32) (k := 4) (b' := p + 64#64) rfl (by bv_omega) (by decide),
      memRegion_split_32 p,
      memRegion_split_32 (p + 32#64),
      ProofLib.memRegion_four (p + 64#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_split_60 (p : BitVec 64) :
    memRegion p 60 =
      ∃∗ u52 : BitVec 64, ∃∗ u48 : BitVec 32, ∃∗ u40 : BitVec 64,
      ∃∗ u32 : BitVec 64, ∃∗ u24 : BitVec 64, ∃∗ u16 : BitVec 64,
      ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ ((p + 16#64) ↦₆₄ u16) ∗ ((p + 24#64) ↦₆₄ u24) ∗
        ((p + 32#64) ↦₆₄ u32) ∗ ((p + 40#64) ↦₆₄ u40) ∗ ((p + 48#64) ↦₃₂ u48) ∗ ((p + 52#64) ↦₆₄ u52) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 32) (k := 28) (b' := p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 20) (b' := p + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 40#64) (n := 8) (k := 12) (b' := p + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 48#64) (n := 4) (k := 8) (b' := p + 52#64) rfl (by bv_omega) (by decide),
      memRegion_split_32 p,
      ProofLib.memRegion_eight (p + 32#64),
      ProofLib.memRegion_eight (p + 40#64),
      ProofLib.memRegion_four (p + 48#64),
      ProofLib.memRegion_eight (p + 52#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

end CryptoVerification.SpqrV1.Poly.NextChunk
