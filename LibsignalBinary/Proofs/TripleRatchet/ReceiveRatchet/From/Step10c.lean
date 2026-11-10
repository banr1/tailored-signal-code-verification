/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Step `+0x10c..+0x244` (`trFrom_step_10c_to_244`) -/

def scRawCells (sp : BitVec 64)
    (w0 w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) : SepProp :=
  ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
  ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
  ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
  ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
  ((sp - 365#64) ↦₈ b67) ∗
  ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
  ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
  ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
  ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)

theorem stack_456_160_split (sp : BitVec 64) :
    memRegion (sp - 456#64) 160 =
      (∃∗ c_456 : BitVec 64, (sp - 456#64) ↦₆₄ c_456) ∗
      (∃∗ c_448 : BitVec 64, (sp - 448#64) ↦₆₄ c_448) ∗
      (∃∗ c_440 : BitVec 64, (sp - 440#64) ↦₆₄ c_440) ∗
      (∃∗ s_432 : BitVec 64, (sp - 432#64) ↦₆₄ s_432) ∗
      (∃∗ s_424 : BitVec 64, (sp - 424#64) ↦₆₄ s_424) ∗
      (∃∗ s_416 : BitVec 64, (sp - 416#64) ↦₆₄ s_416) ∗
      (∃∗ s_408 : BitVec 64, (sp - 408#64) ↦₆₄ s_408) ∗
      (∃∗ s_400 : BitVec 32, (sp - 400#64) ↦₃₂ s_400) ∗
      (∃∗ s_396 : BitVec 8, (sp - 396#64) ↦₈ s_396) ∗
      (∃∗ s_395 : BitVec 32, (sp - 395#64) ↦₃₂ s_395) ∗
      (∃∗ s_391 : BitVec 16, (sp - 391#64) ↦₁₆ s_391) ∗
      (∃∗ s_389 : BitVec 64, (sp - 389#64) ↦₆₄ s_389) ∗
      (∃∗ s_381 : BitVec 64, (sp - 381#64) ↦₆₄ s_381) ∗
      (∃∗ s_373 : BitVec 64, (sp - 373#64) ↦₆₄ s_373) ∗
      (∃∗ s_365 : BitVec 8, (sp - 365#64) ↦₈ s_365) ∗
      (∃∗ s_364 : BitVec 32, (sp - 364#64) ↦₃₂ s_364) ∗
      (∃∗ s_360 : BitVec 64, (sp - 360#64) ↦₆₄ s_360) ∗
      (∃∗ s_352 : BitVec 16, (sp - 352#64) ↦₁₆ s_352) ∗
      (∃∗ s_350 : BitVec 8, (sp - 350#64) ↦₈ s_350) ∗
      (∃∗ s_349 : BitVec 32, (sp - 349#64) ↦₃₂ s_349) ∗
      (∃∗ s_345 : BitVec 8, (sp - 345#64) ↦₈ s_345) ∗
      (∃∗ s_344 : BitVec 16, (sp - 344#64) ↦₁₆ s_344) ∗
      (∃∗ s_342 : BitVec 8, (sp - 342#64) ↦₈ s_342) ∗
      (∃∗ s_341 : BitVec 64, (sp - 341#64) ↦₆₄ s_341) ∗
      (∃∗ s_333 : BitVec 8, (sp - 333#64) ↦₈ s_333) ∗
      (∃∗ s_332 : BitVec 32, (sp - 332#64) ↦₃₂ s_332) ∗
      (∃∗ k_328 : BitVec 8, (sp - 328#64) ↦₈ k_328) ∗
      (∃∗ k_327 : BitVec 8, (sp - 327#64) ↦₈ k_327) ∗
      (∃∗ k_326 : BitVec 8, (sp - 326#64) ↦₈ k_326) ∗
      (∃∗ k_325 : BitVec 8, (sp - 325#64) ↦₈ k_325) ∗
      (∃∗ k_324 : BitVec 8, (sp - 324#64) ↦₈ k_324) ∗
      (∃∗ k_323 : BitVec 8, (sp - 323#64) ↦₈ k_323) ∗
      (∃∗ k_322 : BitVec 8, (sp - 322#64) ↦₈ k_322) ∗
      (∃∗ k_321 : BitVec 64, (sp - 321#64) ↦₆₄ k_321) ∗
      (∃∗ k_313 : BitVec 64, (sp - 313#64) ↦₆₄ k_313) ∗
      (∃∗ k_305 : BitVec 64, (sp - 305#64) ↦₆₄ k_305) ∗
      (∃∗ k_297 : BitVec 8, (sp - 297#64) ↦₈ k_297) := by
  rw [mr_cut' sp 456 448 8 152 160 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 448 440 8 144 152 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 440 432 8 136 144 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 432 424 8 128 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 424 416 8 120 128 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 416 408 8 112 120 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 408 400 8 104 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 400 396 4 100 104 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 396 395 1 99 100 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 395 391 4 95 99 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 391 389 2 93 95 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 389 381 8 85 93 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 381 373 8 77 85 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 373 365 8 69 77 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 365 364 1 68 69 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 364 360 4 64 68 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 360 352 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 352 350 2 54 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 350 349 1 53 54 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 349 345 4 49 53 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 345 344 1 48 49 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 344 342 2 46 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 342 341 1 45 46 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 341 333 8 37 45 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 333 332 1 36 37 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 332 328 4 32 36 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 328 327 1 31 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 327 326 1 30 31 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 326 325 1 29 30 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 325 324 1 28 29 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 324 323 1 27 28 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 323 322 1 26 27 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 322 321 1 25 26 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 321 313 8 17 25 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 313 305 8 9 17 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 305 297 8 1 9 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two, memRegion_one]

theorem stack_256_24_split (sp : BitVec 64) :
    memRegion (sp - 256#64) 24 =
      (∃∗ t_256 : BitVec 64, (sp - 256#64) ↦₆₄ t_256) ∗
      (∃∗ t_248 : BitVec 8, (sp - 248#64) ↦₈ t_248) ∗
      memRegion (sp - 247#64) 7 ∗
      (∃∗ t_240 : BitVec 8, (sp - 240#64) ↦₈ t_240) ∗
      (∃∗ t_239 : BitVec 8, (sp - 239#64) ↦₈ t_239) ∗
      (∃∗ t_238 : BitVec 8, (sp - 238#64) ↦₈ t_238) ∗
      (∃∗ t_237 : BitVec 8, (sp - 237#64) ↦₈ t_237) ∗
      (∃∗ t_236 : BitVec 8, (sp - 236#64) ↦₈ t_236) ∗
      (∃∗ t_235 : BitVec 8, (sp - 235#64) ↦₈ t_235) ∗
      (∃∗ t_234 : BitVec 8, (sp - 234#64) ↦₈ t_234) ∗
      memRegion (sp - 233#64) 1 := by
  rw [mr_cut' sp 256 248 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 248 247 1 15 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 247 240 7 8 15 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 240 239 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 239 238 1 6 7 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 238 237 1 5 6 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 237 236 1 4 5 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 236 235 1 3 4 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 235 234 1 2 3 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 234 233 1 1 2 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_one]

theorem stack_184_24_split_10c (sp : BitVec 64) :
    memRegion (sp - 184#64) 24 =
      (∃∗ t_184 : BitVec 64, (sp - 184#64) ↦₆₄ t_184) ∗
      (∃∗ t_176 : BitVec 8, (sp - 176#64) ↦₈ t_176) ∗
      memRegion (sp - 175#64) 15 := by
  rw [mr_cut' sp 184 176 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 175 1 15 16 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_one]

theorem rk_10c_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8} {w7 w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
       ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
       ((a + 7#64) ↦₆₄ w7) ∗ ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗
       ((a + 31#64) ↦₈ b31))) :
    (((sp - 328#64) ↦₈ b0) ∗ ((sp - 327#64) ↦₈ b1) ∗ ((sp - 326#64) ↦₈ b2) ∗
     ((sp - 325#64) ↦₈ b3) ∗ ((sp - 324#64) ↦₈ b4) ∗ ((sp - 323#64) ↦₈ b5) ∗
     ((sp - 322#64) ↦₈ b6) ∗ ((sp - 321#64) ↦₆₄ w7) ∗ ((sp - 313#64) ↦₆₄ w15) ∗
     ((sp - 305#64) ↦₆₄ w23) ∗ ((sp - 297#64) ↦₈ b31)) ⊢
      ((sp - 328#64) ↦ₛ bs) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem sp_256_split_32_16_2 (sp : BitVec 64) (v : BitVec 64) :
    ((sp - 256#64) ↦₆₄ v) ⊢
      ∃∗ h_252 : BitVec 16, ∃∗ d_256 : BitVec 32,
        ((sp - 256#64) ↦₃₂ d_256) ∗ ((sp - 252#64) ↦₁₆ h_252) ∗ memRegion (sp - 250#64) 2 := by
  refine Entails.trans (pointsTo64_entails_memRegion (sp - 256#64) v) ?_
  rw [mr_cut' sp 256 252 4 4 8 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 252 250 2 2 4 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_four (sp - 256#64), memRegion_two (sp - 252#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem stack_256_24_fold (sp : BitVec 64)
    (d_256 : BitVec 32) (h_252 : BitVec 16)
    (t_248 t_240 t_239 t_238 t_237 t_236 t_235 t_234 : BitVec 8) :
    (((sp - 256#64) ↦₃₂ d_256) ∗ ((sp - 252#64) ↦₁₆ h_252) ∗ memRegion (sp - 250#64) 2 ∗
     ((sp - 248#64) ↦₈ t_248) ∗ memRegion (sp - 247#64) 7 ∗
     ((sp - 240#64) ↦₈ t_240) ∗ ((sp - 239#64) ↦₈ t_239) ∗
     ((sp - 238#64) ↦₈ t_238) ∗ ((sp - 237#64) ↦₈ t_237) ∗
     ((sp - 236#64) ↦₈ t_236) ∗ ((sp - 235#64) ↦₈ t_235) ∗
     ((sp - 234#64) ↦₈ t_234) ∗ memRegion (sp - 233#64) 1) ⊢
      memRegion (sp - 256#64) 24 := by
  rw [mr_cut' sp 256 252 4 20 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 252 250 2 18 20 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 250 248 2 16 18 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 248 247 1 15 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 247 240 7 8 15 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 240 239 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 239 238 1 6 7 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 238 237 1 5 6 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 237 236 1 4 5 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 236 235 1 3 4 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 235 234 1 2 3 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 234 233 1 1 2 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)

theorem stack_280_184_fold_10c (sp : BitVec 64)
    (w_232 : BitVec 64) (b_224 : BitVec 8)
    (b_216 b_215 b_214 b_213 b_212 b_211 b_210 : BitVec 8)
    (w_208 : BitVec 64) (b_200 : BitVec 8) (d_192 : BitVec 32) (h_188 : BitVec 16)
    (t_184 : BitVec 64) (t_176 : BitVec 8)
    (u_160 u_152 u_144 : BitVec 64) :
    (memRegion (sp - 280#64) 24 ∗
     memRegion (sp - 256#64) 24 ∗
     ((sp - 232#64) ↦₆₄ w_232) ∗
     ((sp - 224#64) ↦₈ b_224) ∗ memRegion (sp - 223#64) 7 ∗
     ((sp - 216#64) ↦₈ b_216) ∗ ((sp - 215#64) ↦₈ b_215) ∗
     ((sp - 214#64) ↦₈ b_214) ∗ ((sp - 213#64) ↦₈ b_213) ∗
     ((sp - 212#64) ↦₈ b_212) ∗ ((sp - 211#64) ↦₈ b_211) ∗
     ((sp - 210#64) ↦₈ b_210) ∗ memRegion (sp - 209#64) 1 ∗
     ((sp - 208#64) ↦₆₄ w_208) ∗
     ((sp - 200#64) ↦₈ b_200) ∗ memRegion (sp - 199#64) 7 ∗
     ((sp - 192#64) ↦₃₂ d_192) ∗ ((sp - 188#64) ↦₁₆ h_188) ∗ memRegion (sp - 186#64) 2 ∗
     ((sp - 184#64) ↦₆₄ t_184) ∗ ((sp - 176#64) ↦₈ t_176) ∗ memRegion (sp - 175#64) 15 ∗
     ((sp - 160#64) ↦₆₄ u_160) ∗ ((sp - 152#64) ↦₆₄ u_152) ∗ ((sp - 144#64) ↦₆₄ u_144) ∗
     memRegion (sp - 136#64) 16 ∗ memRegion (sp - 120#64) 24) ⊢
      memRegion (sp - 280#64) 184 := by
  rw [mr_cut' sp 280 256 24 160 184 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 256 232 24 136 160 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 232 224 8 128 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 224 223 1 127 128 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 223 216 7 120 127 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 216 215 1 119 120 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 215 214 1 118 119 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 214 213 1 117 118 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 213 212 1 116 117 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 212 211 1 115 116 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 211 210 1 114 115 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 210 209 1 113 114 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 209 208 1 112 113 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 208 200 8 104 112 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 200 199 1 103 104 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 199 192 7 96 103 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 192 188 4 92 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 188 186 2 90 92 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 186 184 2 88 90 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 184 176 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 175 1 79 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 175 160 15 64 79 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 160 152 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 152 144 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 144 136 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 136 120 16 24 40 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono (Entails.refl _) (Entails.refl _)

theorem vecU8At_nil_pq_ss (A : RustAlloc) (ss : BitVec 64) :
    (((ss + 120#64) ↦₆₄ 0#64) ∗ ((ss + 128#64) ↦₆₄ 1#64) ∗ ((ss + 136#64) ↦₆₄ 0#64)) ⊢
      vecU8At A (ss + 120#64) 0#64 1#64 [] := by
  have h := vecU8At_nil_0_1 A (ss + 120#64)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

theorem sessionAfter208Frame_intro (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    (sessionFromBase A ss G st ∗
     (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
     ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
     vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
     ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
     ((ss + 64#64) ↦₆₄ 32#64) ∗
     (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
     vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
     vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
     vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
     optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
     ((ss + 332#64) ↦₃₂ st.previousCounter)) ⊢
      sessionAfter208Frame A ss G st := by
  unfold sessionAfter208Frame
  exact Entails.refl _

theorem scRawCells_fold (sp : BitVec 64)
    (w0 w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
     ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
     ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
     ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
     ((sp - 365#64) ↦₈ b67) ∗
     ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
     ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
     ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
     ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)) ⊢
      scRawCells sp w0 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
        d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100 := by
  unfold scRawCells
  exact Entails.refl _

theorem trFrom_step_10c_to_244
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (target_pc : BitVec 64) (F_tail : SepProp)
    (post : State → SepProp → Prop)
    (w_208 : BitVec 64) (b_200 : BitVec 8) (d_192 : BitVec 32) (h_188 : BitVec 16)
    (u_296 : BitVec 64) (u_288 u_284 : BitVec 32)
    {rk_b0 rk_b1 rk_b2 rk_b3 rk_b4 rk_b5 rk_b6 : BitVec 8}
    {rk_w7 rk_w15 rk_w23 : BitVec 64} {rk_b31 : BitVec 8}
    {rx2 rx3 rx4 rx5 rx6 rx8 rx9 rx10 rx11 rx12 rx13 rx14 rx15 rx16 rx17 rx18 : BitVec 64}
    (hrk : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) =
        ((a ↦₈ rk_b0) ∗ ((a + 1#64) ↦₈ rk_b1) ∗ ((a + 2#64) ↦₈ rk_b2) ∗ ((a + 3#64) ↦₈ rk_b3) ∗
         ((a + 4#64) ↦₈ rk_b4) ∗ ((a + 5#64) ↦₈ rk_b5) ∗ ((a + 6#64) ↦₈ rk_b6) ∗
         ((a + 7#64) ↦₆₄ rk_w7) ∗ ((a + 15#64) ↦₆₄ rk_w15) ∗ ((a + 23#64) ↦₆₄ rk_w23) ∗
         ((a + 31#64) ↦₈ rk_b31)))
    (hcmn_chains : (G.chainsCap + 1#64 == 0#64) = false)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 268#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hw1 : (s.readReg64 .x1).setWidth 32 = 0#32)
    (hx2 : s.readReg64 .x2 = rx2)
    (hx3 : s.readReg64 .x3 = rx3)
    (hx4 : s.readReg64 .x4 = rx4)
    (hx5 : s.readReg64 .x5 = rx5)
    (hx6 : s.readReg64 .x6 = rx6)
    (hx8 : s.readReg64 .x8 = rx8)
    (hx9 : s.readReg64 .x9 = rx9)
    (hx10 : s.readReg64 .x10 = rx10)
    (hx11 : s.readReg64 .x11 = rx11)
    (hx12 : s.readReg64 .x12 = rx12)
    (hx13 : s.readReg64 .x13 = rx13)
    (hx14 : s.readReg64 .x14 = rx14)
    (hx15 : s.readReg64 .x15 = rx15)
    (hx16 : s.readReg64 .x16 = rx16)
    (hx17 : s.readReg64 .x17 = rx17)
    (hx18 : s.readReg64 .x18 = rx18)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = s0.sp - 456#64)
    (hx21 : s.readReg64 .x21 = rk_w15)
    (hx22 : s.readReg64 .x22 = rk_w7)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hcont : ∀ s_244,
      img.FrozenLoaded s_244 → s_244.symtab = img.symtab →
      s_244.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64 →
      s_244.status = .Running → s_244.trace = s0.trace →
      s_244.readReg64 .x0 = G.localIk.ptr →
      s_244.readReg64 .x1 = BitVec.ofNat 64 G.localIk.bytes.length →
      s_244.readReg64 .x8 = s0.sp - 160#64 →
      s_244.readReg64 .x19 = ret →
      s_244.readReg64 .x20 = G.pq.cap →
      s_244.readReg64 .x21 = G.pq.ptr →
      s_244.readReg64 .x22 = ss →
      s_244.readReg64 .x23 = 0x8000000000000014#64 →
      s_244.readReg64 .x24 = s0.sp - 184#64 →
      s_244.readReg64 .x25 = BitVec.ofNat 64 st.pqRatchetState.length →
      s_244.readReg64 .x29 = s0.sp - 96#64 →
      s_244.sp = s0.sp - 496#64 →
      calleeSavedVRegs s_244 = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext) target_pc s_244
        (((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
         scRawCells s0.sp
           rx4 rx5 rx6 rx2 (rx8.setWidth 32)
           (rx3.setWidth 8) d_192 h_188 rx9 rx10 rx11 (rx14.setWidth 8)
           (rx17.setWidth 32) rx18 (rx16.setWidth 16)
           ((((rx16.setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
           (rx13.setWidth 32) ((rx13 >>> 32).setWidth 8)
           (rx15.setWidth 16)
           ((((rx15.setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
           w_208 b_200 (rx12.setWidth 32) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion (s0.sp - 280#64) 184 ∗
         sessionAfter208Frame A ss G st ∗
         F_tail)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) target_pc s
      (memRegion (s0.sp - 456#64) 160 ∗
       ((s0.sp - 296#64) ↦₆₄ u_296) ∗
       ((s0.sp - 288#64) ↦₃₂ u_288) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion (s0.sp - 280#64) 24 ∗
       memRegion (s0.sp - 256#64) 24 ∗
       ((s0.sp - 232#64) ↦₆₄ rk_w23) ∗
       ((s0.sp - 224#64) ↦₈ rk_b31) ∗ memRegion (s0.sp - 223#64) 7 ∗
       ((s0.sp - 216#64) ↦₈ rk_b0) ∗ ((s0.sp - 215#64) ↦₈ rk_b1) ∗
       ((s0.sp - 214#64) ↦₈ rk_b2) ∗ ((s0.sp - 213#64) ↦₈ rk_b3) ∗
       ((s0.sp - 212#64) ↦₈ rk_b4) ∗ ((s0.sp - 211#64) ↦₈ rk_b5) ∗
       ((s0.sp - 210#64) ↦₈ rk_b6) ∗ memRegion (s0.sp - 209#64) 1 ∗
       ((s0.sp - 208#64) ↦₆₄ w_208) ∗
       ((s0.sp - 200#64) ↦₈ b_200) ∗ memRegion (s0.sp - 199#64) 7 ∗
       ((s0.sp - 192#64) ↦₃₂ d_192) ∗ ((s0.sp - 188#64) ↦₁₆ h_188) ∗ memRegion (s0.sp - 186#64) 2 ∗
       memRegion (s0.sp - 184#64) 24 ∗
       ((s0.sp - 160#64) ↦₆₄ G.chainsCap) ∗
       ((s0.sp - 152#64) ↦₆₄ G.chainsPtr) ∗
       ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
       memRegion (s0.sp - 136#64) 16 ∗
       memRegion (s0.sp - 120#64) 24 ∗
       sessionFromBase A ss G st ∗
       (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
       ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
       vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
       ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
       ((ss + 64#64) ↦₆₄ 32#64) ∗
       (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
       vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
       ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
       ((ss + 136#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
       optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
       ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
       F_tail)
      post := by
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName = entry
  apply SepWP.of_sepWP_inv (mid := entry + bv% (580)) hfl hsym
  rw [stack_456_160_split s0.sp, stack_256_24_split s0.sp, stack_184_24_split_10c s0.sp]
  simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun t_176 => SepWP.exists_elim fun t_184 => ?_
  refine SepWP.exists_elim fun t_234 => SepWP.exists_elim fun t_235 => ?_
  refine SepWP.exists_elim fun t_236 => SepWP.exists_elim fun t_237 => ?_
  refine SepWP.exists_elim fun t_238 => SepWP.exists_elim fun t_239 => ?_
  refine SepWP.exists_elim fun t_240 => SepWP.exists_elim fun t_248 => ?_
  refine SepWP.exists_elim fun t_256 => ?_
  refine SepWP.exists_elim fun k_297 => SepWP.exists_elim fun k_305 => ?_
  refine SepWP.exists_elim fun k_313 => SepWP.exists_elim fun k_321 => ?_
  refine SepWP.exists_elim fun k_322 => SepWP.exists_elim fun k_323 => ?_
  refine SepWP.exists_elim fun k_324 => SepWP.exists_elim fun k_325 => ?_
  refine SepWP.exists_elim fun k_326 => SepWP.exists_elim fun k_327 => ?_
  refine SepWP.exists_elim fun k_328 => SepWP.exists_elim fun s_332 => ?_
  refine SepWP.exists_elim fun s_333 => SepWP.exists_elim fun s_341 => ?_
  refine SepWP.exists_elim fun s_342 => SepWP.exists_elim fun s_344 => ?_
  refine SepWP.exists_elim fun s_345 => SepWP.exists_elim fun s_349 => ?_
  refine SepWP.exists_elim fun s_350 => SepWP.exists_elim fun s_352 => ?_
  refine SepWP.exists_elim fun s_360 => SepWP.exists_elim fun s_364 => ?_
  refine SepWP.exists_elim fun s_365 => SepWP.exists_elim fun s_373 => ?_
  refine SepWP.exists_elim fun s_381 => SepWP.exists_elim fun s_389 => ?_
  refine SepWP.exists_elim fun s_391 => SepWP.exists_elim fun s_395 => ?_
  refine SepWP.exists_elim fun s_396 => SepWP.exists_elim fun s_400 => ?_
  refine SepWP.exists_elim fun s_408 => SepWP.exists_elim fun s_416 => ?_
  refine SepWP.exists_elim fun s_424 => SepWP.exists_elim fun s_432 => ?_
  refine SepWP.exists_elim fun c_440 => SepWP.exists_elim fun c_448 => ?_
  refine SepWP.exists_elim fun c_456 => ?_
  tr_from_fetches img.base (Rust.withPanics ext) hfn hentry 0x10c 19
  wp_steps
  examples_clear_fetches
  refine SepWP.fold (sp_256_split_32_16_2 s0.sp _) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun h_252 => SepWP.exists_elim fun d_256 => ?_
  tr_from_fetches img.base (Rust.withPanics ext) hfn hentry 0x158 59
  wp_steps
  examples_clear_fetches
  refine SepWP.fold (rk_10c_pack_stack s0.sp hrk) (by sep_focus) ?_
  refine SepWP.fold (scRawCells_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_256_24_fold s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (stack_280_184_fold_10c s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (vecU8At_nil_pq_ss A ss) (by sep_focus) ?_
  refine SepWP.fold (sessionAfter208Frame_intro A ss G st) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_f hsym_f
  have h16 : BitVec.truncate 16 (BitVec.truncate 32 rx16) = BitVec.setWidth 16 rx16 := by bv_kernel
  have h15 : BitVec.truncate 16 (BitVec.truncate 32 rx15) = BitVec.setWidth 16 rx15 := by bv_kernel
  have hb200 : BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b_200 &&& 1095216660735#64) = b_200 := by bv_kernel
  rw [h16, h15, hb200]
  refine SepWP.mono_pre (Entails.of_eq (by ac_rfl))
    (hcont _ hfl_f hsym_f
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

theorem memRegion_100_to_bytes (a : BitVec 64) :
    memRegion a 100 ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 100⌝ ∗ (a ↦ₛ bs) := by
  have h1 : memRegion a 100 = memRegion a 32 ∗ memRegion (a + 32#64) 68 :=
    memRegion_split' (by decide) rfl (by decide)
  have h2 : memRegion (a + 32#64) 68 = memRegion (a + 32#64) 32 ∗ memRegion (a + 64#64) 36 :=
    mr_cut_add a 32 32 36 (by decide)
  have h3 : memRegion (a + 64#64) 36 = memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 4 :=
    mr_cut_add a 64 32 4 (by decide)
  rw [h1, h2, h3, memRegion_four (a + 96#64)]
  refine Entails.trans (sepConj_mono (memRegion_32_to_bytes a)
    (sepConj_mono (memRegion_32_to_bytes (a + 32#64))
      (sepConj_mono (memRegion_32_to_bytes (a + 64#64)) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro bs2
  apply Entails.sepExists_elim; intro bs1
  apply Entails.sepExists_elim; intro bs0
  apply Entails.pure_left; intro h0
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro h1'
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro h2'
  let out100 := bs0 ++ bs1 ++ bs2 ++ unpack32 d3
  have hout_len : out100.length = 100 := by
    have hd3 : (unpack32 d3).length = 4 := rfl
    simp [out100, h0, h1', h2', hd3]
  have hout_pts : (a ↦ₛ out100) =
      ((a ↦ₛ bs0) ∗ ((a + 32#64) ↦ₛ bs1) ∗ ((a + 64#64) ↦ₛ bs2) ∗ ((a + 96#64) ↦₃₂ d3)) := by
    dsimp only [out100]
    simp only [List.append_assoc, pointsToBytes_append, h0, h1', h2',
      ← pointsTo32_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_exists_right out100
  apply Entails.pure_right hout_len
  rw [hout_pts]
  exact Entails.refl _

theorem scRawCells_to_memRegion_100 (sp : BitVec 64)
    (d4 : BitVec 32) (w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    (((sp - 428#64) ↦₃₂ d4) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
     ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
     ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
     ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
     ((sp - 365#64) ↦₈ b67) ∗
     ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
     ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
     ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
     ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)) ⊢
      memRegion (sp - 428#64) 100 := by
  rw [mr_cut' sp 428 424 4 96 100 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 424 416 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 416 408 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 408 400 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 400 396 4 68 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 396 395 1 67 68 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 395 391 4 63 67 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 391 389 2 61 63 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 389 381 8 53 61 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 381 373 8 45 53 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 373 365 8 37 45 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 365 364 1 36 37 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 364 360 4 32 36 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 360 352 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 352 350 2 22 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 350 349 1 21 22 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 349 345 4 17 21 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 345 344 1 16 17 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 344 342 2 14 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 342 341 1 13 14 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 341 333 8 5 13 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 333 332 1 4 5 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _)

theorem scRawCells_none_entails (sp : BitVec 64)
    (w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    scRawCells sp 0#64 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
      d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100 ⊢
      ∃∗ senderPad : List (BitVec 8),
        ⌜senderPad.length = 100⌝ ∗
        ((sp - 432#64) ↦ₛ optSenderChainBytes none senderPad) := by
  unfold scRawCells
  have h0_64 : ((sp - 432#64) ↦₆₄ 0#64) =
      (((sp - 432#64) ↦₈ 0#8) ∗ ((sp - 431#64) ↦₈ 0#8) ∗
       ((sp - 430#64) ↦₈ 0#8) ∗ ((sp - 429#64) ↦₈ 0#8) ∗
       ((sp - 428#64) ↦₃₂ 0#32)) := by
    have hsplit : ((sp - 432#64) ↦₆₄ 0#64) =
        ((sp - 432#64) ↦₃₂ (0#8 ++ 0#8 ++ 0#8 ++ 0#8)) ∗ ((sp - 432#64 + 4#64) ↦₃₂ 0#32) :=
      pointsTo64_eq_pointsTo32 (sp - 432#64) (0#8 ++ 0#8 ++ 0#8 ++ 0#8) 0#32
    rw [hsplit, pointsTo32_eq_bytes4 (sp - 432#64)]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg, sepConj_assoc]
  rw [h0_64]
  simp only [sepConj_assoc]
  have hmr := Entails.trans
    (scRawCells_to_memRegion_100 sp 0#32 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
      d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100)
    (memRegion_100_to_bytes (sp - 428#64))
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _) hmr)))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro senderPad
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hlen
  apply entails_exists_right senderPad
  apply Entails.pure_right hlen
  rw [optSenderChainBytes_none_eq (sp - 432#64) senderPad]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem scRawCells_some_entails (sp : BitVec 64) (sc : SenderChain) (senderPad : List (BitVec 8))
    {pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 pk_b7 pk_b8 pk_b9 pk_b10 pk_b11
     pk_b12 pk_b13 pk_b14 pk_b15 pk_b16 pk_b17 pk_b18 pk_b19 pk_b20 pk_b21 pk_b22
     pk_b23 pk_b24 pk_b25 pk_b26 pk_b27 : BitVec 8}
    {pk_d28 : BitVec 32}
    {sk_b0 : BitVec 8} {sk_d1 : BitVec 32} {sk_h5 : BitVec 16}
    {sk_w7 sk_w15 sk_w23 : BitVec 64} {sk_b31 : BitVec 8}
    {ck_d0 : BitVec 32}
    {ck_b4 ck_b5 ck_b6 ck_b7 ck_b8 ck_b9 ck_b10 ck_b11 ck_b12 ck_b13 ck_b14
     ck_b15 ck_b16 ck_b17 ck_b18 ck_b19 ck_b20 ck_b21 ck_b22 : BitVec 8}
    {ck_w23 : BitVec 64} {ck_b31 : BitVec 8}
    (hpk2 : ∀ a : BitVec 64,
      ((a ↦₆₄ (pk_b3 ++ pk_b2 ++ pk_b1 ++ pk_b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8)) ∗
       ((a + 8#64) ↦₆₄ (pk_b11 ++ pk_b10 ++ pk_b9 ++ pk_b8 ++ pk_b7 ++ pk_b6 ++ pk_b5 ++ pk_b4)) ∗
       ((a + 16#64) ↦₆₄ (pk_b19 ++ pk_b18 ++ pk_b17 ++ pk_b16 ++ pk_b15 ++ pk_b14 ++ pk_b13 ++ pk_b12)) ∗
       ((a + 24#64) ↦₆₄ (pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)) ∗
       ((a + 32#64) ↦₃₂ pk_d28)) =
      ((a ↦₈ 1#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦₈ 0#8) ∗ ((a + 3#64) ↦₈ 0#8) ∗
       ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList)))
    (hsk : ∀ a : BitVec 64,
      (a ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
        ((a ↦₈ sk_b0) ∗ ((a + 1#64) ↦₃₂ sk_d1) ∗ ((a + 5#64) ↦₁₆ sk_h5) ∗
         ((a + 7#64) ↦₆₄ sk_w7) ∗ ((a + 15#64) ↦₆₄ sk_w15) ∗ ((a + 23#64) ↦₆₄ sk_w23) ∗
         ((a + 31#64) ↦₈ sk_b31)))
    (hck2 : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) =
        ((a ↦₃₂ ck_d0) ∗
         ((a + 4#64) ↦₆₄ (ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7 ++ ck_b6 ++ ck_b5 ++ ck_b4)) ∗
         ((a + 12#64) ↦₁₆ (ck_b13 ++ ck_b12)) ∗
         ((a + 14#64) ↦₈ ck_b14) ∗
         ((a + 15#64) ↦₃₂ (ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15)) ∗
         ((a + 19#64) ↦₈ ck_b19) ∗
         ((a + 20#64) ↦₁₆ (ck_b21 ++ ck_b20)) ∗
         ((a + 22#64) ↦₈ ck_b22) ∗
         ((a + 23#64) ↦₆₄ ck_w23) ∗
         ((a + 31#64) ↦₈ ck_b31))) :
    scRawCells sp
      (pk_b3 ++ pk_b2 ++ pk_b1 ++ pk_b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8)
      (pk_b11 ++ pk_b10 ++ pk_b9 ++ pk_b8 ++ pk_b7 ++ pk_b6 ++ pk_b5 ++ pk_b4)
      (pk_b19 ++ pk_b18 ++ pk_b17 ++ pk_b16 ++ pk_b15 ++ pk_b14 ++ pk_b13 ++ pk_b12)
      (pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)
      ((pk_d28.zeroExtend 64).setWidth 32)
      ((sk_b0.zeroExtend 64).setWidth 8) sk_d1 sk_h5 sk_w7 sk_w15 sk_w23
      ((sk_b31.zeroExtend 64).setWidth 8)
      ((ck_d0.zeroExtend 64).setWidth 32)
      (ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7 ++ ck_b6 ++ ck_b5 ++ ck_b4)
      (((0#8 ++ ck_b14 ++ ck_b13 ++ ck_b12 : BitVec 32).zeroExtend 64).setWidth 16)
      ((((((0#8 ++ ck_b14 ++ ck_b13 ++ ck_b12 : BitVec 32).zeroExtend 64).setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
      ((ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15).setWidth 32)
      (((ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15) >>> 32).setWidth 8)
      (((0#8 ++ ck_b22 ++ ck_b21 ++ ck_b20 : BitVec 32).zeroExtend 64).setWidth 16)
      ((((((0#8 ++ ck_b22 ++ ck_b21 ++ ck_b20 : BitVec 32).zeroExtend 64).setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
      ck_w23 ck_b31 ((sc.chainKey.index.zeroExtend 64).setWidth 32) ⊢
      ((sp - 432#64) ↦ₛ optSenderChainBytes (some sc) senderPad) := by
  simp only [arm64_norm]
  unfold scRawCells
  have h1 := hpk2 (sp - 432#64)
  rw [optSenderChainBytes_some_eq (sp - 432#64) sc senderPad,
      hsk (sp - 432#64 + 36#64),
      hck2 (sp - 432#64 + 68#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg,
    ← sepConj_assoc] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem stack_256_96_split (sp : BitVec 64) :
    memRegion (sp - 256#64) 96 =
      memRegion (sp - 256#64) 24 ∗
      (∃∗ w_232 : BitVec 64, (sp - 232#64) ↦₆₄ w_232) ∗
      (∃∗ b_224 : BitVec 8, (sp - 224#64) ↦₈ b_224) ∗ memRegion (sp - 223#64) 7 ∗
      (∃∗ b_216 : BitVec 8, (sp - 216#64) ↦₈ b_216) ∗
      (∃∗ b_215 : BitVec 8, (sp - 215#64) ↦₈ b_215) ∗
      (∃∗ b_214 : BitVec 8, (sp - 214#64) ↦₈ b_214) ∗
      (∃∗ b_213 : BitVec 8, (sp - 213#64) ↦₈ b_213) ∗
      (∃∗ b_212 : BitVec 8, (sp - 212#64) ↦₈ b_212) ∗
      (∃∗ b_211 : BitVec 8, (sp - 211#64) ↦₈ b_211) ∗
      (∃∗ b_210 : BitVec 8, (sp - 210#64) ↦₈ b_210) ∗ memRegion (sp - 209#64) 1 ∗
      (∃∗ w_208 : BitVec 64, (sp - 208#64) ↦₆₄ w_208) ∗
      (∃∗ b_200 : BitVec 8, (sp - 200#64) ↦₈ b_200) ∗ memRegion (sp - 199#64) 7 ∗
      (∃∗ d_192 : BitVec 32, (sp - 192#64) ↦₃₂ d_192) ∗
      (∃∗ h_188 : BitVec 16, (sp - 188#64) ↦₁₆ h_188) ∗ memRegion (sp - 186#64) 2 ∗
      memRegion (sp - 184#64) 24 := by
  rw [mr_cut' sp 256 232 24 72 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 232 224 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 224 223 1 63 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 223 216 7 56 63 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 216 215 1 55 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 215 214 1 54 55 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 214 213 1 53 54 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 213 212 1 52 53 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 212 211 1 51 52 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 211 210 1 50 51 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 210 209 1 49 50 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 209 208 1 48 49 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 208 200 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 200 199 1 39 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 199 192 7 32 39 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 192 188 4 28 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 188 186 2 26 28 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 186 184 2 24 26 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight, memRegion_four, memRegion_two, memRegion_one]

theorem stack_456_160_split_deser (sp : BitVec 64) :
    memRegion (sp - 456#64) 160 =
      memRegion (sp - 456#64) 33 ∗ memRegion (sp - 423#64) 127 :=
  mr_cut' sp 456 423 33 127 160 rfl rfl (by decide) (by decide) (by decide)

theorem stack_456_160_fold_some (sp : BitVec 64)
    (b_456 b_455 b_454 b_453 b_452 b_451 b_450 b_449
     b_448 b_447 b_446 b_445 b_444 b_443 b_442 b_441 : BitVec 8)
    (w_440 : BitVec 64) (d_432 : BitVec 32) (b_428 : BitVec 8) (d_427 : BitVec 32) :
    (((sp - 456#64) ↦₈ b_456) ∗ ((sp - 455#64) ↦₈ b_455) ∗
     ((sp - 454#64) ↦₈ b_454) ∗ ((sp - 453#64) ↦₈ b_453) ∗
     ((sp - 452#64) ↦₈ b_452) ∗ ((sp - 451#64) ↦₈ b_451) ∗
     ((sp - 450#64) ↦₈ b_450) ∗ ((sp - 449#64) ↦₈ b_449) ∗
     ((sp - 448#64) ↦₈ b_448) ∗ ((sp - 447#64) ↦₈ b_447) ∗
     ((sp - 446#64) ↦₈ b_446) ∗ ((sp - 445#64) ↦₈ b_445) ∗
     ((sp - 444#64) ↦₈ b_444) ∗ ((sp - 443#64) ↦₈ b_443) ∗
     ((sp - 442#64) ↦₈ b_442) ∗ ((sp - 441#64) ↦₈ b_441) ∗
     ((sp - 440#64) ↦₆₄ w_440) ∗ ((sp - 432#64) ↦₃₂ d_432) ∗
     ((sp - 428#64) ↦₈ b_428) ∗ ((sp - 427#64) ↦₃₂ d_427) ∗
     memRegion (sp - 423#64) 127) ⊢
      memRegion (sp - 456#64) 160 := by
  rw [mr_cut' sp 456 455 1 159 160 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 455 454 1 158 159 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 454 453 1 157 158 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 453 452 1 156 157 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 452 451 1 155 156 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 451 450 1 154 155 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 450 449 1 153 154 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 449 448 1 152 153 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 448 447 1 151 152 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 447 446 1 150 151 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 446 445 1 149 150 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 445 444 1 148 149 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 444 443 1 147 148 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 443 442 1 146 147 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 442 441 1 145 146 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 441 440 1 144 145 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 440 432 8 136 144 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 432 428 4 132 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 428 427 1 131 132 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 427 423 4 127 131 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)

theorem stack_184_24_split_some (sp : BitVec 64) :
    memRegion (sp - 184#64) 24 =
      (∃∗ t_184 : BitVec 8, (sp - 184#64) ↦₈ t_184) ∗
      (∃∗ t_183 : BitVec 8, (sp - 183#64) ↦₈ t_183) ∗
      (∃∗ t_182 : BitVec 8, (sp - 182#64) ↦₈ t_182) ∗
      (∃∗ t_181 : BitVec 8, (sp - 181#64) ↦₈ t_181) ∗
      (∃∗ t_180 : BitVec 8, (sp - 180#64) ↦₈ t_180) ∗
      (∃∗ t_179 : BitVec 8, (sp - 179#64) ↦₈ t_179) ∗
      (∃∗ t_178 : BitVec 8, (sp - 178#64) ↦₈ t_178) ∗
      (∃∗ t_177 : BitVec 8, (sp - 177#64) ↦₈ t_177) ∗
      (∃∗ t_176 : BitVec 8, (sp - 176#64) ↦₈ t_176) ∗
      (∃∗ t_175 : BitVec 8, (sp - 175#64) ↦₈ t_175) ∗
      (∃∗ t_174 : BitVec 8, (sp - 174#64) ↦₈ t_174) ∗
      (∃∗ t_173 : BitVec 8, (sp - 173#64) ↦₈ t_173) ∗
      (∃∗ t_172 : BitVec 8, (sp - 172#64) ↦₈ t_172) ∗
      (∃∗ t_171 : BitVec 8, (sp - 171#64) ↦₈ t_171) ∗
      (∃∗ t_170 : BitVec 8, (sp - 170#64) ↦₈ t_170) ∗
      (∃∗ t_169 : BitVec 8, (sp - 169#64) ↦₈ t_169) ∗
      (∃∗ t_168 : BitVec 8, (sp - 168#64) ↦₈ t_168) ∗
      (∃∗ t_167 : BitVec 8, (sp - 167#64) ↦₈ t_167) ∗
      (∃∗ t_166 : BitVec 8, (sp - 166#64) ↦₈ t_166) ∗
      memRegion (sp - 165#64) 1 ∗
      (∃∗ t_164 : BitVec 16, (sp - 164#64) ↦₁₆ t_164) ∗
      (∃∗ t_162 : BitVec 8, (sp - 162#64) ↦₈ t_162) ∗
      memRegion (sp - 161#64) 1 := by
  rw [mr_cut' sp 184 183 1 23 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 183 182 1 22 23 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 182 181 1 21 22 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 181 180 1 20 21 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 180 179 1 19 20 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 179 178 1 18 19 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 178 177 1 17 18 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 177 176 1 16 17 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 175 1 15 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 175 174 1 14 15 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 174 173 1 13 14 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 173 172 1 12 13 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 172 171 1 11 12 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 171 170 1 10 11 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 170 169 1 9 10 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 169 168 1 8 9 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 168 167 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 167 166 1 6 7 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 166 165 1 5 6 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 165 164 1 4 5 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 164 162 2 2 4 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 162 161 1 1 2 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_two, memRegion_one]

theorem stack_184_24_fold_some (sp : BitVec 64)
    (t_184 t_183 t_182 t_181 t_180 t_179 t_178 t_177
     t_176 t_175 t_174 t_173 t_172 t_171 t_170 t_169
     t_168 t_167 t_166 : BitVec 8)
    (t_164 : BitVec 16) (t_162 : BitVec 8) :
    (((sp - 184#64) ↦₈ t_184) ∗ ((sp - 183#64) ↦₈ t_183) ∗
     ((sp - 182#64) ↦₈ t_182) ∗ ((sp - 181#64) ↦₈ t_181) ∗
     ((sp - 180#64) ↦₈ t_180) ∗ ((sp - 179#64) ↦₈ t_179) ∗
     ((sp - 178#64) ↦₈ t_178) ∗ ((sp - 177#64) ↦₈ t_177) ∗
     ((sp - 176#64) ↦₈ t_176) ∗ ((sp - 175#64) ↦₈ t_175) ∗
     ((sp - 174#64) ↦₈ t_174) ∗ ((sp - 173#64) ↦₈ t_173) ∗
     ((sp - 172#64) ↦₈ t_172) ∗ ((sp - 171#64) ↦₈ t_171) ∗
     ((sp - 170#64) ↦₈ t_170) ∗ ((sp - 169#64) ↦₈ t_169) ∗
     ((sp - 168#64) ↦₈ t_168) ∗ ((sp - 167#64) ↦₈ t_167) ∗
     ((sp - 166#64) ↦₈ t_166) ∗ memRegion (sp - 165#64) 1 ∗
     ((sp - 164#64) ↦₁₆ t_164) ∗ ((sp - 162#64) ↦₈ t_162) ∗
     memRegion (sp - 161#64) 1) ⊢
      memRegion (sp - 184#64) 24 := by
  rw [mr_cut' sp 184 183 1 23 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 183 182 1 22 23 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 182 181 1 21 22 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 181 180 1 20 21 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 180 179 1 19 20 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 179 178 1 18 19 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 178 177 1 17 18 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 177 176 1 16 17 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 176 175 1 15 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 175 174 1 14 15 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 174 173 1 13 14 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 173 172 1 12 13 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 172 171 1 11 12 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 171 170 1 10 11 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 170 169 1 9 10 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 169 168 1 8 9 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 168 167 1 7 8 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 167 166 1 6 7 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 166 165 1 5 6 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 165 164 1 4 5 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 164 162 2 2 4 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 162 161 1 1 2 rfl rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo8_entails_memRegion _ _) ?_
  refine sepConj_mono (Entails.refl _) ?_
  refine sepConj_mono (pointsTo16_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)

theorem trFromGhost_model_fst (x : TrFromGhost) :
    x.model.1 =
      match x.st.remoteIdentity with
      | some rem =>
        .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
              x.st.previousCounter, maxForwardJumps⟩,
             x.st.pqRatchetState, x.st.localIdentity, rem⟩
      | none => .error (.invalidSessionStructure .missingRemoteIdentity) := by
  rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
  cases rik <;> rfl


end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet
