/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

/-!
# `<Vec<Vec<u8>> as Clone>::clone` (empty source) at `vecVecCloneStackX`

`serialize` clones `previous_sessions` (always empty here). On `x2 = len = 0` the function
branches at `+0x024: cbz x2, +0xc4` to `+0xc4: mov w23, #8; +0xc8: stp x19, x23, [x20];
+0xcc: str x19, [x20, #0x10]` and returns: `{cap 0, ptr 8, len 0}`, no allocation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private gen_decodes libsignalSessionCode_tree vecVecCloneX
  [(ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") →
   (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 36),
   (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 196) →
   (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 232)]

private theorem stackAt_vecVecCloneX (sp : BitVec 64) :
    stackAt sp vecVecCloneStackX =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        stackAt (sp - 96#64) extHookStack ∗
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp extHookStack 12 (by decide)
  have hadd : extHookStack + 8 * 12 = vecVecCloneStackX := by decide
  rw [hadd] at h1
  change stackAt sp vecVecCloneStackX =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]
  simp only [sepExists_sepConj_right]

private theorem memRegion_24_cells_vvc (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

theorem vecVecCloneEmpty_ok_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr vecVecCloneName)
      vecVecCloneEmptySpecX := by
  unfold vecVecCloneEmptySpecX
  simp only [stackAt_vecVecCloneX, memRegion_24_cells_vvc, vecHeader,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff vecVecCloneName =
      num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") :=
    (ls_lemma% fnOff "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")
  code_fetches_from CryptoVerification.libsignalSessionCode vecVecCloneX b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")) 0 40
  code_fetches_from CryptoVerification.libsignalSessionCode vecVecCloneX b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")) 0xc4 40
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨dst, src⟩ := x
  dsimp only at *
  wp_steps
  wp_done

theorem vecVecCloneEmpty_ok_x (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr vecVecCloneName)
      (vecVecCloneEmptySpecX.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (vecVecCloneEmpty_ok_ext img.base ext)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
