/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtCallees -- shake: keep

/-!
# Contract-Backed 4-Byte RNG Bridge and Initiator Callee Re-Exports (`tripleRatchetProgAtExt`)

Proves `sp2Rng4_ok_at_ext` on `tripleRatchetProgAtExt` and re-exports
`InitializeAliceStage1CommonExtA`, `InitializeAliceStage1CommonExtB`, and
`InitializeAliceStage1CommonExtCallees`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (rngFill_ok_at_tripleRatchet
  rngFillAfter0Spec)
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
theorem sp2Rng4_ok_at_ext {img : Obj.Image} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hRng : HookSat ext "libsignal_session_rng_fill" (rngFillAfter0Spec ctl))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "libsignal_session_rng_fill" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (sp2Rng4Spec ctl) := by
  have hrng : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (rngFillAfter0Spec ctl) :=
    hook_ok_at (hname := "libsignal_session_rng_fill") rfl hk
      (by rw [(ls_stub% "libsignal_session_rng_fill")]; decide)
      (fun H => by
        rw [(ls_stub% "libsignal_session_rng_fill")]
        exact (ls_hook% "libsignal_session_rng_fill") H)
      (by decide +kernel) hRng
  refine subroutine_ok_outcome_intro fun ⟨destPtr, w, cur, u, rest⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [sp2Rng4Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  have hx1_nat : (s0.readReg64 .x1).toNat = 4 := by rw [hx1]; rfl
  have hpre' : s0.mem ⊨
      (rngFillAfter0Spec ctl).pre (destPtr, 4, cur, word32Bytes u ++ rest) s0 ∗ R := by
    dsimp only [rngFillAfter0Spec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_nat⟩,
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (pointsTo32_entails_memRegion4 destPtr w))) hpre⟩
  refine hrng.mono_outcome (destPtr, 4, cur, word32Bytes u ++ rest) R s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rngFillAfter0Spec] at hq
    have htake : ((word32Bytes u ++ rest) ++ List.replicate 4 0#8).take 4 = word32Bytes u := by
      rw [List.append_assoc, List.take_append_of_le_length (by simp [word32Bytes]),
        List.take_of_length_le (by simp [word32Bytes])]
    have hmin : min 4 (word32Bytes u ++ rest).length = 4 := by simp [word32Bytes]
    rw [htake, hmin, ← pointsTo32_eq_pointsToBytes_word32Bytes destPtr u,
      tapeAfter_word32Bytes_four ctl cur u rest] at hq
    dsimp only [sp2Rng4Spec]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
  · exact Or.inr hpan

end CryptoVerification.E2E.Pqxdh.Initiator
