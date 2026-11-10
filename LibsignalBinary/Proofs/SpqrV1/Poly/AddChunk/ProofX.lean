/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlaced

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk`: Extended-Stack Wrapper

**Checked by Lean.**

Frames the unused bottom stack region (`addChunkSpecX_of_addChunkSpec`) to derive `add_chunk_ok_x`
and `add_chunk_placed_ok_x`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc

private theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- `addChunkSpec A` entails `addChunkSpecX A` by framing the unused bottom stack region. -/
theorem addChunkSpecX_of_addChunkSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (addChunkSpec A)) :
    subroutine_ok P addr (addChunkSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : addChunkStack ≤ addChunkStackX := by decide
  have hsplit : stackAt s0.sp addChunkStackX =
      memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
        (addChunkStackX - addChunkStack) ∗
        stackAt s0.sp addChunkStack := by
    have h1 := stackAt_split_bottom s0.sp addChunkStack
      (addChunkStackX - addChunkStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 addChunkStackX)
      (addChunkStackX - addChunkStack) ∗ R
  have hpre' : s0.mem ⊨ (addChunkSpec A).pre x s0 ∗ R' := by
    dsimp only [addChunkSpecX, addChunkSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [addChunkSpecX, addChunkSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [addChunkSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

theorem add_chunk_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    AddChunkOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (addChunkSpecX_of_addChunkSpec (add_chunk_ok_ext hA))

theorem add_chunk_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemmove_sat : HookSat (Rust.withPanics ext) spqrMemmoveSym (sessionMemmoveSpec growOneStack))
    (hgrow_full : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (growOnePtFullSpec A))
    (hgrow_empty : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (lsmpl.base 357) (growOnePtSpec A)) :
    AddChunkPlacedOkX A ext :=
  addChunkSpecX_of_addChunkSpec (add_chunk_placed_ok_ext hmemmove_sat hgrow_full hgrow_empty)

end CryptoVerification.SpqrV1.Poly.AddChunk
