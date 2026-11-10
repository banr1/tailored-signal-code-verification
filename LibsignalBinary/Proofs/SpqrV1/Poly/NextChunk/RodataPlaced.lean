/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows30
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows34
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataRows36

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Placed `.rodata` Lagrange Basis Tables

Relocatable `[LibsignalPlacement]` `.rodata` assertions (`completePointsPolysPlacedAt`), loading
lemmas (`rodata_completePointsPolys_placed`), and row-slicing bridges for
`COMPLETE_POINTS_POLYS_{5,30,34,36}`.
-/

@[expose] public section

set_option autoImplicit false

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
open CryptoVerification.CodeLayout

/-- `.rodata` symbol of `COMPLETE_POINTS_POLYS_5` (50 bytes = 5 × 5 × `u16`). -/
abbrev completePointsPolys5Sym : String := "spqr:.rodata..Lanon.191"

/-- `.rodata` symbol of `COMPLETE_POINTS_POLYS_30` (1,800 bytes = 30 × 30 × `u16`). -/
abbrev completePointsPolys30Sym : String := "spqr:.rodata..Lanon.192"

/-- `.rodata` symbol of `COMPLETE_POINTS_POLYS_34` (2,312 bytes = 34 × 34 × `u16`). -/
abbrev completePointsPolys34Sym : String := "spqr:.rodata..Lanon.193"

/-- `.rodata` symbol of `COMPLETE_POINTS_POLYS_36` (2,592 bytes = 36 × 36 × `u16`). -/
abbrev completePointsPolys36Sym : String := "spqr:.rodata..Lanon.194"

set_option maxRecDepth 200000

def completePointsPolys5PlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ completePointsPolys5Sym) ↦ᵣ completePointsPolys5Bytes

private theorem lsroCheck_completePointsPolys5 :
    lsroCheck completePointsPolys5Sym completePointsPolys5Bytes = true := by
  rw [completePointsPolys5Bytes_eq_lit]
  decide +kernel

theorem rodata_completePointsPolys5_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ completePointsPolys5PlacedAt ∗ P :=
  lsro_intro_chk hro lsroCheck_completePointsPolys5 hP

def completePointsPolys30PlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ completePointsPolys30Sym) ↦ᵣ completePointsPolys30Bytes

private theorem lsroCheck_completePointsPolys30 :
    lsroCheck completePointsPolys30Sym completePointsPolys30Bytes = true := by
  unfold completePointsPolys30Bytes extractCompletePolys
  rw [completePointsPolys30_eq]
  decide +kernel

theorem rodata_completePointsPolys30_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ completePointsPolys30PlacedAt ∗ P :=
  lsro_intro_chk hro lsroCheck_completePointsPolys30 hP

def completePointsPolys34PlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ completePointsPolys34Sym) ↦ᵣ completePointsPolys34Bytes

private theorem lsroCheck_completePointsPolys34 :
    lsroCheck completePointsPolys34Sym completePointsPolys34Bytes = true := by
  unfold completePointsPolys34Bytes extractCompletePolys
  rw [completePointsPolys34_eq]
  decide +kernel

theorem rodata_completePointsPolys34_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ completePointsPolys34PlacedAt ∗ P :=
  lsro_intro_chk hro lsroCheck_completePointsPolys34 hP

def completePointsPolys36PlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ completePointsPolys36Sym) ↦ᵣ completePointsPolys36Bytes

private theorem lsroCheck_completePointsPolys36 :
    lsroCheck completePointsPolys36Sym completePointsPolys36Bytes = true := by
  unfold completePointsPolys36Bytes extractCompletePolys
  rw [completePointsPolys36_eq]
  decide +kernel

theorem rodata_completePointsPolys36_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ completePointsPolys36PlacedAt ∗ P :=
  lsro_intro_chk hro lsroCheck_completePointsPolys36 hP

/-- Bundled relocatable read-only separation-logic assertion for `COMPLETE_POINTS_POLYS_{5,30,34,36}`. -/
def completePointsPolysPlacedAt [LibsignalPlacement] : SepProp :=
  completePointsPolys5PlacedAt ∗
  completePointsPolys30PlacedAt ∗
  completePointsPolys34PlacedAt ∗
  completePointsPolys36PlacedAt

theorem rodata_completePointsPolys_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ completePointsPolysPlacedAt ∗ P := by
  have h36 := rodata_completePointsPolys36_placed hro hP
  have h34 := rodata_completePointsPolys34_placed hro h36
  have h30 := rodata_completePointsPolys30_placed hro h34
  have h5 := rodata_completePointsPolys5_placed hro h30
  simpa [completePointsPolysPlacedAt, sepConj_assoc] using h5

theorem sepWPp_intro_rodata_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s0 (completePointsPolysPlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s0 P Q Qp := by
  intro R0 hm hL
  have hm' : s0.mem ⊨ (completePointsPolysPlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact rodata_completePointsPolys_placed hro hm
  exact h R0 hm' hL

/-- Unread bytes of `COMPLETE_POINTS_POLYS_5` at `lsρ completePointsPolys5Sym`
    (offsets `8..10`, `18..20`, `28..30`, `38..50`). -/
def completePointsPolys5RestPlacedAt [LibsignalPlacement] : SepProp :=
  ((lsρ completePointsPolys5Sym + 8#64) ↦ᵣ (completePointsPolys5Bytes.drop 8).take 2) ∗
  ((lsρ completePointsPolys5Sym + 18#64) ↦ᵣ (completePointsPolys5Bytes.drop 18).take 2) ∗
  ((lsρ completePointsPolys5Sym + 28#64) ↦ᵣ (completePointsPolys5Bytes.drop 28).take 2) ∗
  ((lsρ completePointsPolys5Sym + 38#64) ↦ᵣ completePointsPolys5Bytes.drop 38)

theorem completePointsPolys5PlacedAt_split [LibsignalPlacement] :
    completePointsPolys5PlacedAt =
      ((lsρ completePointsPolys5Sym) ↦₆₄ᵣ 0x78039605b4050001#64) ∗
      ((lsρ completePointsPolys5Sym + 10#64) ↦₆₄ᵣ 0x7803c00750030000#64) ∗
      ((lsρ completePointsPolys5Sym + 20#64) ↦₆₄ᵣ 0x78031400f0060000#64) ∗
      ((lsρ completePointsPolys5Sym + 30#64) ↦₆₄ᵣ 0x7803f0069b680000#64) ∗
      completePointsPolys5RestPlacedAt := by
  unfold completePointsPolys5PlacedAt completePointsPolys5RestPlacedAt
  generalize lsρ completePointsPolys5Sym = base
  have hlen : completePointsPolys5Bytes.length = 50 := completePointsPolys5Bytes_length
  have hw0 : (base ↦ᵣ completePointsPolys5Bytes.take 8) =
      (base ↦₆₄ᵣ 0x78039605b4050001#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO base completePointsPolys5Bytes 0 (by omega)
    rw [List.drop_zero] at h
    have hp : pack64 (cp5BytesLit.getD 0 0#8) (cp5BytesLit.getD 1 0#8)
        (cp5BytesLit.getD 2 0#8) (cp5BytesLit.getD 3 0#8)
        (cp5BytesLit.getD 4 0#8) (cp5BytesLit.getD 5 0#8)
        (cp5BytesLit.getD 6 0#8) (cp5BytesLit.getD 7 0#8) = 0x78039605b4050001#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw1 : ((base + 10#64) ↦ᵣ (completePointsPolys5Bytes.drop 10).take 8) =
      ((base + 10#64) ↦₆₄ᵣ 0x7803c00750030000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (base + 10#64) completePointsPolys5Bytes 10 (by omega)
    have hp : pack64 (cp5BytesLit.getD 10 0#8) (cp5BytesLit.getD 11 0#8)
        (cp5BytesLit.getD 12 0#8) (cp5BytesLit.getD 13 0#8)
        (cp5BytesLit.getD 14 0#8) (cp5BytesLit.getD 15 0#8)
        (cp5BytesLit.getD 16 0#8) (cp5BytesLit.getD 17 0#8) = 0x7803c00750030000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw2 : ((base + 20#64) ↦ᵣ (completePointsPolys5Bytes.drop 20).take 8) =
      ((base + 20#64) ↦₆₄ᵣ 0x78031400f0060000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (base + 20#64) completePointsPolys5Bytes 20 (by omega)
    have hp : pack64 (cp5BytesLit.getD 20 0#8) (cp5BytesLit.getD 21 0#8)
        (cp5BytesLit.getD 22 0#8) (cp5BytesLit.getD 23 0#8)
        (cp5BytesLit.getD 24 0#8) (cp5BytesLit.getD 25 0#8)
        (cp5BytesLit.getD 26 0#8) (cp5BytesLit.getD 27 0#8) = 0x78031400f0060000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hw3 : ((base + 30#64) ↦ᵣ (completePointsPolys5Bytes.drop 30).take 8) =
      ((base + 30#64) ↦₆₄ᵣ 0x7803f0069b680000#64) := by
    have h := pointsToBytesRO_take8_eq_pointsTo64RO (base + 30#64) completePointsPolys5Bytes 30 (by omega)
    have hp : pack64 (cp5BytesLit.getD 30 0#8) (cp5BytesLit.getD 31 0#8)
        (cp5BytesLit.getD 32 0#8) (cp5BytesLit.getD 33 0#8)
        (cp5BytesLit.getD 34 0#8) (cp5BytesLit.getD 35 0#8)
        (cp5BytesLit.getD 36 0#8) (cp5BytesLit.getD 37 0#8) = 0x7803f0069b680000#64 := by
      decide +kernel
    rw [h, completePointsPolys5Bytes_eq_lit, hp]
  have hs0 := pointsToBytesRO_split3 base completePointsPolys5Bytes 8 2 (by omega)
  have hs1 := pointsToBytesRO_split3 (base + 10#64) (completePointsPolys5Bytes.drop 10) 8 2 (by simp [hlen])
  have hs2 := pointsToBytesRO_split3 (base + 20#64) (completePointsPolys5Bytes.drop 20) 8 2 (by simp [hlen])
  have hs3 := pointsToBytesRO_split3 (base + 30#64) (completePointsPolys5Bytes.drop 30) 8 0 (by simp [hlen])
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    List.drop_drop, Nat.reduceAdd, List.take_zero, pointsToBytesRO_nil, emp_sepConj] at hs0 hs1 hs2 hs3
  rw [hs0, hs1, hs2, hs3, hw0, hw1, hw2, hw3]
  ac_rfl

/-- `polyNextChunkPlacedSpec A` extended with `completePointsPolysPlacedAt` explicit in `pre`. -/
def polyNextChunkRodataPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec PolyNextChunkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A x.encA x.enc ∗
      completePointsPolysPlacedAt ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp polyNextChunkStack
  post := (polyNextChunkPlacedSpec A).post
  onPanic := (polyNextChunkPlacedSpec A).onPanic

/-- Relocatable `[LibsignalPlacement]` contract for `<PolyEncoder as Encoder>::next_chunk`
    (Block `416`) with explicit `completePointsPolysPlacedAt` wrapped with `withLsCodeLoaded lsmpl`. -/
def PolyNextChunkRodataPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
    (blkPl_416).base
    (withLsCodeLoaded lsmpl (polyNextChunkRodataPlacedSpec A))

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (completePointsPolysPlacedAt rodata_completePointsPolys_placed
  polyNextChunkRodataPlacedSpec PolyNextChunkRodataPlacedOkExt)
end CryptoVerification.SpqrV1.Poly
