/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage 5 Scratch Stack Layout, Bundle Lens, and Call Combinators

Stack-offset normalizations, `stage5ScratchAt` split/merge helpers, `cliBundleAt_stage5_lens`, and
typed `SepWPp` call combinators for Stage 5 session and store callees.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

/-! ## Scratch Layout, Future Boxes, and Bundle Lens -/

@[scoped arm64_norm, scoped wp_norm]
theorem bv64_add_zero (v : BitVec 64) : v + 0#64 = v :=
  BitVec.add_zero v

@[scoped arm64_norm, scoped wp_norm]
theorem fsp_stage5_eqs (sp0 : BitVec 64) :
    let fsp := sp0 - BitVec.ofNat 64 cliInitiateFrame
    fsp + 208#64 = fsp + 0xd0#64 ∧
    fsp + 224#64 = fsp + 0xe0#64 ∧
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧
    fsp + 240#64 = fsp + 0xf0#64 ∧
    fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 248#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧
    fsp + 256#64 = fsp + 0x100#64 ∧
    fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 272#64 = fsp + 0x110#64 ∧
    fsp + 288#64 = fsp + 0x120#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧
    fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧
    fsp + 768#64 = fsp + 0x300#64 ∧
    fsp + 772#64 = fsp + 0x304#64 ∧
    fsp + 0x460#64 + 340#64 = (fsp + 0x460#64) + 0x154#64 ∧
    fsp + 1456#64 = (fsp + 0x460#64) + 0x150#64 ∧
    fsp + 1464#64 = fsp + 0x5b8#64 ∧
    fsp + 1472#64 = fsp + 0x5c0#64 ∧
    fsp + 1480#64 = fsp + 0x5c8#64 ∧
    fsp + 1488#64 = fsp + 0x5d0#64 ∧
    fsp + 1496#64 = fsp + 0x5d8#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 ∧
    fsp + 5632#64 = fsp + 0x1600#64 ∧
    fsp + 5640#64 = (fsp + 0x1600#64) + 0x08#64 ∧
    fsp + 5648#64 = (fsp + 0x1600#64) + 0x10#64 ∧
    fsp + 5656#64 = (fsp + 0x1600#64) + 0x18#64 ∧
    fsp + 5664#64 = (fsp + 0x1600#64) + 0x20#64 ∧
    fsp + 5672#64 = (fsp + 0x1600#64) + 0x28#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Decomposed Stage 5 scratch region `[fsp + 0x5ba, fsp + initLocalsSize)`. -/
def stage5ScratchAt (fsp w5c0 w5c8 w5d0 : BitVec 64) : SepProp :=
  memRegion (fsp + 0x5ba#64) 6 ∗
    ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
    ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
    ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
    memRegion (fsp + 0x5d8#64) (0x1600 - 0x5d8) ∗
    memRegion (fsp + 0x1600#64) 48 ∗
    memRegion (fsp + 0x1630#64) 296 ∗
    memRegion (fsp + 0x1758#64) (initLocalsSize - 0x1758)

theorem scratch_split (fsp : BitVec 64) :
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ⊢
      ∃∗ w5c0 : BitVec 64, ∃∗ w5c8 : BitVec 64, ∃∗ w5d0 : BitVec 64,
        stage5ScratchAt fsp w5c0 w5c8 w5d0 := by
  dsimp only [initLocalsSize]
  rw [ProofLib.memRegion_split' (b := fsp + 0x5ba#64) (n := 6) (k := 7312 - 0x5c0) (b' := fsp + 0x5c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5c0#64) (n := 8) (k := 7312 - 0x5c8) (b' := fsp + 0x5c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5c8#64) (n := 8) (k := 7312 - 0x5d0) (b' := fsp + 0x5d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5d0#64) (n := 8) (k := 7312 - 0x5d8) (b' := fsp + 0x5d8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5d8#64) (n := 0x1600 - 0x5d8) (k := 7312 - 0x1600) (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1600#64) (n := 48) (k := 7312 - 0x1630) (b' := fsp + 0x1630#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1630#64) (n := 296) (k := 7312 - 0x1758) (b' := fsp + 0x1758#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 0x5c0#64),
      ProofLib.memRegion_eight (fsp + 0x5c8#64),
      ProofLib.memRegion_eight (fsp + 0x5d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w5d0 => Entails.sepExists_elim fun w5c8 =>
    Entails.sepExists_elim fun w5c0 => ?_
  dsimp only [stage5ScratchAt, initLocalsSize]
  exact Entails.sepExists_right w5c0 (Entails.sepExists_right w5c8
    (Entails.sepExists_right w5d0 (Entails.of_eq (by ac_rfl))))

theorem scratch_merge (fsp w5c0 w5c8 w5d0 : BitVec 64) :
    stage5ScratchAt fsp w5c0 w5c8 w5d0 ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  dsimp only [stage5ScratchAt]
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (Entails.refl _))))) ?_
  dsimp only [initLocalsSize]
  rw [← ProofLib.memRegion_split' (b := fsp + 0x1630#64) (n := 296) (k := 7312 - 0x1758) (b' := fsp + 0x1758#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x1600#64) (n := 48) (k := 7312 - 0x1630) (b' := fsp + 0x1630#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5d8#64) (n := 0x1600 - 0x5d8) (k := 7312 - 0x1600) (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5d0#64) (n := 8) (k := 7312 - 0x5d8) (b' := fsp + 0x5d8#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5c8#64) (n := 8) (k := 7312 - 0x5d0) (b' := fsp + 0x5d0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5c0#64) (n := 8) (k := 7312 - 0x5c8) (b' := fsp + 0x5c8#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fsp + 0x5ba#64) (n := 6) (k := 7312 - 0x5c0) (b' := fsp + 0x5c0#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem scratch_sret344_eq (fsp : BitVec 64) :
    memRegion (fsp + 0x1600#64) 48 ∗ memRegion (fsp + 0x1630#64) 296 =
      memRegion (fsp + 0x1600#64) 344 :=
  (ProofLib.memRegion_split' (b := fsp + 0x1600#64) (n := 48) (k := 296)
    (b' := fsp + 0x1630#64) rfl (by bv_omega) (by decide)).symm

def pack64LoHi (lo hi : BitVec 32) : BitVec 64 :=
  lo.zeroExtend 64 ||| (hi.zeroExtend 64 <<< 32)

theorem pack64LoHi_setWidth32 (lo hi : BitVec 32) :
    (pack64LoHi lo hi).setWidth 32 = lo := by
  ext i hi_lt
  simp [pack64LoHi]

theorem pointsTo32_pair_entails_64 (b : BitVec 64) (lo hi : BitVec 32) :
    ((b ↦₃₂ lo) ∗ ((b + 4#64) ↦₃₂ hi)) ⊢ (b ↦₆₄ pack64LoHi lo hi) := by
  have hbytes : unpack32 lo ++ unpack32 hi = unpack64 (pack64LoHi lo hi) := by
    dsimp only [unpack32, unpack64, pack64LoHi]
    refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
      (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
        (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))))))) <;>
      (ext i hi_lt; interval_cases i <;> simp)
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, ← hbytes, pointsToBytes_append, unpack32_length]
  exact Entails.refl _

theorem memRegion_4_entails_32 (b : BitVec 64) :
    memRegion b 4 ⊢ ∃∗ w : BitVec 32, (b ↦₃₂ w) := by
  rw [ProofLib.memRegion_split' (b := b) (n := 1) (k := 3) (b' := b + 1#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := b + 1#64) (n := 1) (k := 2) (b' := b + 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := b + 2#64) (n := 1) (k := 1) (b' := b + 3#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one b, ProofLib.memRegion_one (b + 1#64),
      ProofLib.memRegion_one (b + 2#64), ProofLib.memRegion_one (b + 3#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun b3 => Entails.sepExists_elim fun b2 =>
    Entails.sepExists_elim fun b1 => Entails.sepExists_elim fun b0 => ?_
  refine Entails.sepExists_right (pack4LE b0 b1 b2 b3) ?_
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack4LE]
  have h1 : (b ↦ₛ [b0, b1, b2, b3]) =
      (b ↦₈ b0) ∗ ((b + 1#64) ↦₈ b1) ∗ ((b + 2#64) ↦₈ b2) ∗ ((b + 3#64) ↦₈ b3) := by
    change (b ↦ₛ ([b0] ++ [b1] ++ [b2] ++ [b3])) = _
    rw [List.append_assoc, List.append_assoc,
        pointsToBytes_append, List.length_singleton,
        pointsToBytes_append, List.length_singleton,
        pointsToBytes_append, List.length_singleton]
    have a2 : b + 1#64 + 1#64 = b + 2#64 := by bv_omega
    have a3 : b + 2#64 + 1#64 = b + 3#64 := by bv_omega
    rw [a2, a3]
    simp only [pointsToBytes_singleton]
  rw [h1]
  exact Entails.of_eq (by ac_rfl)

theorem tail32_words4 (out : BitVec 64) :
    memRegion (out + 0x10#64) 32 ⊢
      ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((out + 0x10#64) ↦₆₄ w2) ∗ ((out + 0x18#64) ↦₆₄ w3) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 24) (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 16) (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8) (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 0x10#64),
      ProofLib.memRegion_eight (out + 0x18#64),
      ProofLib.memRegion_eight (out + 0x20#64),
      ProofLib.memRegion_eight (out + 0x28#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => ?_
  exact Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.of_eq (by ac_rfl)))))

theorem u32_tail36_words5 (out : BitVec 64) (v : BitVec 32) :
    ((out + 0x08#64) ↦₃₂ v) ∗ memRegion (out + 0x0c#64) 36 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ⌜w1.setWidth 32 = v⌝ ∗
        ((out + 0x08#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
        ((out + 0x28#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 32)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion_4_entails_32 (out + 0x0c#64)) (tail32_words4 out))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
    Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_elim fun hi => ?_
  refine Entails.sepExists_right (pack64LoHi v hi) (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_))))
  refine Entails.pure_right (pack64LoHi_setWidth32 v hi) ?_
  have hc : (out + 0x08#64) + 4#64 = out + 0x0c#64 := by bv_omega
  have hp := pointsTo32_pair_entails_64 (out + 0x08#64) v hi
  rw [hc] at hp
  exact Entails.trans (Entails.of_eq (by ac_rfl :
    ((out + 0x08#64) ↦₃₂ v) ∗ (((out + 0x0c#64) ↦₃₂ hi) ∗
      (((out + 0x10#64) ↦₆₄ w2) ∗ ((out + 0x18#64) ↦₆₄ w3) ∗
       ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5))) =
    (((out + 0x08#64) ↦₃₂ v) ∗ ((out + 0x0c#64) ↦₃₂ hi)) ∗
      (((out + 0x10#64) ↦₆₄ w2) ∗ ((out + 0x18#64) ↦₆₄ w3) ∗
       ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5))))
    (sepConj_mono_left hp)

theorem tail40_words5 (out : BitVec 64) :
    memRegion (out + 0x08#64) 40 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((out + 0x08#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
        ((out + 0x28#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := out + 0x08#64) (n := 8) (k := 32)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 0x08#64)]
  refine Entails.trans (sepConj_mono_right (tail32_words4 out)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
    Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_elim fun w1 => ?_
  exact Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.of_eq (by ac_rfl))))))

theorem words6_entails_memRegion48 (out w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((out ↦₆₄ w0) ∗ ((out + 0x08#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ⊢
      memRegion out 48 := by
  rw [sret48_words6_split out]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.refl _))))))

theorem idOwnFutBoxAt_entails_memRegion16 (fut self : BitVec 64) (st : BitVec 8) :
    idOwnFutBoxAt fut self st ⊢ memRegion fut 16 := by
  dsimp only [idOwnFutBoxAt]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))) ?_
  rw [← ProofLib.memRegion_split' (b := fut + 8#64) (n := 1) (k := 7) (b' := fut + 9#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut) (n := 8) (k := 8) (b' := fut + 8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem idSaveBoxAt_entails_memRegion32 (fut self addrA keyA : BitVec 64) (st : BitVec 8) :
    idSaveBoxAt fut self addrA keyA st ⊢ memRegion fut 32 := by
  dsimp only [idSaveBoxAt]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := fut + 0x18#64) (n := 1) (k := 7) (b' := fut + 0x19#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut + 0x10#64) (n := 8) (k := 8) (b' := fut + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut + 8#64) (n := 8) (k := 16) (b' := fut + 0x10#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut) (n := 8) (k := 24) (b' := fut + 8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem sessStoreBoxAt_entails_memRegion32 (fut self addrA recA : BitVec 64) (st : BitVec 8) :
    sessStoreBoxAt fut self addrA recA st ⊢ memRegion fut 32 := by
  dsimp only [sessStoreBoxAt]
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := fut + 0x18#64) (n := 1) (k := 7) (b' := fut + 0x19#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut + 0x10#64) (n := 8) (k := 8) (b' := fut + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut + 8#64) (n := 8) (k := 16) (b' := fut + 0x10#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := fut) (n := 8) (k := 24) (b' := fut + 8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Extract the 4 fields of `cliBundleAt` read by Stage 5 (`spkId`, `kpkId`, `idKey`, `regId`) plus
`b.kpk.length = 1568`, with lossless re-folding into `cliBundleAt`. -/
theorem cliBundleAt_stage5_lens (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    ∀ R (m : Memory),
      m ⊨ cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr ∗ R →
      ∃ BRest : SepProp,
        b.kpk.length = 1568 ∧
        (m ⊨ ((a + 0x38#64) ↦₃₂ b.spkId) ∗
              ((a + 0x68#64) ↦₃₂ b.kpkId) ∗
              ((a + 0x78#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
              ((a + 0x98#64) ↦₃₂ b.regId) ∗
              (BRest ∗ R)) ∧
        (((a + 0x38#64) ↦₃₂ b.spkId) ∗
          ((a + 0x68#64) ↦₃₂ b.kpkId) ∗
          ((a + 0x78#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
          ((a + 0x98#64) ↦₃₂ b.regId) ∗ BRest ⊢
            cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr) := by
  intro R m hm
  dsimp only [cliBundleAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨opkW, hm⟩ := hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hpure, hm⟩ := hm
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  let BRest : SepProp :=
    (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    memRegion (a + 108#64) 4 ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkW) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2
  refine ⟨BRest, hpure.2.2.1, ?_, ?_⟩
  · dsimp only [BRest, opkFlag]
    exact sat_eq (by ac_rfl) hm
  · dsimp only [cliBundleAt, BRest, opkFlag]
    refine Entails.sepExists_right opkW ?_
    refine Entails.pure_right hpure ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## Typed `SepWPp` Call Combinators -/

theorem s5_call_setUnackMsg_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {callee ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base extP) callee
      (Slots.setUnackPreKeyMsgExtStackEpochSpec A img))
    (fsp : BitVec 64) (g : Pqxdh.TopLevel.SetUnackExactGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = g.optOpkTag)
    (hx2 : (s.readReg64 .x2).setWidth 32 = g.optOpkVal)
    (hx3 : (s.readReg64 .x3).setWidth 32 = g.spkId)
    (hx4 : s.readReg64 .x4 = g.baseKeyPtr)
    (hx5 : s.readReg64 .x5 = 0#64)
    (hx6 : (s.readReg64 .x6).setWidth 32 = 0#32)
    (hbLen : g.baseKeyBytes.length = 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ ((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (fsp - 144#64) (extHookStack + 32) ∗
      cells (fsp - 144#64) 18 ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        (((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
          Pqxdh.Initiator.vecU8 A (g.statePtr + 0xf8#64)
            (Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC g.baseKeyBytes)) ∗
          ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
          ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
          ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
          ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
          memRegion (g.statePtr + 0x124#64) 4 ∗
          stackAt (fsp - 144#64) (extHookStack + 32) ∗
          cells (fsp - 144#64) 18 ∗ A.pool) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  refine s5_call_raw hExt.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx5, hx6⟩
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbLen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec,
      Pqxdh.Initiator.rustPanicOnOom, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [Slots.setUnackPreKeyMsgExtStackEpochSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_setUnackMsg {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W))
    (hcall : subroutine_ok (initProg img W) callee (setUnackPreKeyMsgEpochSpec A img))
    (fsp : BitVec 64) (g : Pqxdh.TopLevel.SetUnackExactGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = g.optOpkTag)
    (hx2 : (s.readReg64 .x2).setWidth 32 = g.optOpkVal)
    (hx3 : (s.readReg64 .x3).setWidth 32 = g.spkId)
    (hx4 : s.readReg64 .x4 = g.baseKeyPtr)
    (hx5 : s.readReg64 .x5 = 0#64)
    (hx6 : (s.readReg64 .x6).setWidth 32 = 0#32)
    (hbLen : g.baseKeyBytes.length = 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ ((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (fsp - 144#64) (allocHookStack + 32) ∗
      cells (fsp - 144#64) 18 ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProg img W) ret sm
        (((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
          Pqxdh.Initiator.vecU8 A (g.statePtr + 0xf8#64)
            (Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC g.baseKeyBytes)) ∗
          ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
          ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
          ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
          ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
          memRegion (g.statePtr + 0x124#64) 4 ∗
          stackAt (fsp - 144#64) (allocHookStack + 32) ∗
          cells (fsp - 144#64) 18 ∗ A.pool) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp := by
  refine s5_call_raw hh.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec,
      hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx5, hx6⟩
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbLen⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec,
      Pqxdh.Initiator.rustPanicOnOom, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [setUnackPreKeyMsgEpochSpec, Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec,
      hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_setUnackKyb_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {callee ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base extP) callee Pqxdh.setUnackKyberPreKeyIdSpec)
    (fsp statePtr cap : BitVec 64) (w0 kpkId : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = statePtr) (hx1 : (s.readReg64 .x1).setWidth 32 = kpkId)
    (hcap : cap + 1#64 ≠ 0#64) (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ w0)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ kpkId)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  refine s5_call_raw hExt.fs hcall (statePtr, cap, kpkId) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, hcap⟩ ?_
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w0 (Entails.refl _)))
  · intro sm R' hpost; simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost; simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost; simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [Pqxdh.setUnackKyberPreKeyIdSpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [Pqxdh.setUnackKyberPreKeyIdSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_setUnackKyb {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W))
    (hcall : subroutine_ok (initProg img W) callee Pqxdh.setUnackKyberPreKeyIdSpec)
    (fsp statePtr cap : BitVec 64) (w0 kpkId : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = statePtr) (hx1 : (s.readReg64 .x1).setWidth 32 = kpkId)
    (hcap : cap + 1#64 ≠ 0#64) (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ w0)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProg img W) ret sm
        ((((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ kpkId)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_setUnackKyb_ext (stage5ExternDeps_of_runHooks hh) hcall fsp statePtr cap w0 kpkId F
    hpc hrun hsp hsp_align hlr htr hinv hx0 hx1 hcap hpan hpre hnext

theorem s5_call_idRegIdShim_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp self : BitVec 64) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = self) (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + idRegIdFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((A.live (sm.readReg64 .x0) 16 8 ∗ idOwnFutBoxAt (sm.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP idRegIdShimName ▸ hStore.idRegIdShim
  refine s5_call_raw hExt.fs hcall self F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [idOwnShimSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right hx0 (Entails.refl _))
  · intro sm R' hpost; simp only [idOwnShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.2.2.2
  · intro sm R' hpost; simp only [idOwnShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [idOwnShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [idOwnShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [idOwnShimSpec, Spec.inImage, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_idRegIdShim {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp self : BitVec 64) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = self) (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + idRegIdFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProg img W) ret sm
        ((A.live (sm.readReg64 .x0) 16 8 ∗ idOwnFutBoxAt (sm.readReg64 .x0) self 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_idRegIdShim_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp self F hpc hrun hsp hsp_align hlr htr hinv hx0 hpan hpre hnext

theorem s5_call_idRegIdPoll_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp : BitVec 64) (g : IdOwnPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdPollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.fut) (hx8 : s.readReg64 .x8 = g.out)
    (hpathLt : g.own.path.length < 2 ^ 32) (hpathOk : cliWrOk (pathOf g.own.path (utf8 "registration-id")))
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idOwnFutBoxAt g.fut g.self 0#8 ∗ dirAt A g.self g.own ∗
      memRegion g.out 48 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (ans : Except Unit (BitVec 32)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      ans = (IdGhost.mk g.own (.new [])).regId cliIo.rd s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((idRegIdOutAt A g.out ans ∗ idOwnFutBoxAt g.fut g.self 1#8 ∗
          dirAt A g.self g.own ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP idRegIdPollName ▸ hStore.idRegIdPoll
  refine s5_call_raw hExt.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [idRegIdPollSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx8, hpathLt, hpathOk⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [idRegIdPollSpec, Spec.inImage, sepExists_sepConj_left, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, ⟨_, htrm⟩, _⟩ := hpost; exact htrm
  · intro sm R' hpost; simp only [idRegIdPollSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [idRegIdPollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [idRegIdPollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [idRegIdPollSpec, Spec.inImage, hsp, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hans, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm ans hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hans)

theorem s5_call_idRegIdPoll {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp : BitVec 64) (g : IdOwnPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdPollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.fut) (hx8 : s.readReg64 .x8 = g.out)
    (hpathLt : g.own.path.length < 2 ^ 32) (hpathOk : cliWrOk (pathOf g.own.path (utf8 "registration-id")))
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idOwnFutBoxAt g.fut g.self 0#8 ∗ dirAt A g.self g.own ∗
      memRegion g.out 48 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (ans : Except Unit (BitVec 32)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      ans = (IdGhost.mk g.own (.new [])).regId cliIo.rd s.fs.files →
      SepWPp (initProg img W) ret sm
        ((idRegIdOutAt A g.out ans ∗ idOwnFutBoxAt g.fut g.self 1#8 ∗
          dirAt A g.self g.own ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_idRegIdPoll_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp g F hpc hrun hsp hsp_align hlr htr hinv hx0 hx8 hpathLt hpathOk hpan hpre hnext

theorem s5_call_idSaveShim_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp : BitVec 64) (c : IdentityShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSaveShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = c.self) (hx1 : s.readReg64 .x1 = c.addrA) (hx2 : s.readReg64 .x2 = c.keyA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + idSaveFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗ idSaveBoxAt (sm.readReg64 .x0) c.self c.addrA c.keyA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP idSaveShimName ▸ hStore.idSaveShim
  refine s5_call_raw hExt.fs hcall c F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [idSaveShimSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _))
  · intro sm R' hpost; simp only [idSaveShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.2.2.2
  · intro sm R' hpost; simp only [idSaveShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [idSaveShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [idSaveShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [idSaveShimSpec, Spec.inImage, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_idSaveShim {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp : BitVec 64) (c : IdentityShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSaveShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = c.self) (hx1 : s.readReg64 .x1 = c.addrA) (hx2 : s.readReg64 .x2 = c.keyA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + idSaveFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProg img W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗ idSaveBoxAt (sm.readReg64 .x0) c.self c.addrA c.keyA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_idSaveShim_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp c F hpc hrun hsp hsp_align hlr htr hinv hx0 hx1 hx2 hpan hpre hnext

theorem s5_call_idSavePoll_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp : BitVec 64) (g : IdPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSavePollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.call.fut) (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hpathLt : g.peers.path.length < 2 ^ 32) (hchgLt : g.peers.changed.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.peers.path g.call.call.addr.val.name))
    (hwf : ∀ bs, g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name = .ok bs → IdFileWf bs)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 0#8 ∗
      dirAt A (g.self + 0x28#64) g.peers ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8)))
      (p : Except Unit (Option IdentityKey)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      gr = g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name → IdPeerAns gr p →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((idSaveOutAt A g.call.out (idSaveOf p g.call.call.key) ∗
          dirAt A (g.self + 0x28#64)
            (idSavePeers g.peers g.call.call.addr.val.name g.call.call.key p) ∗
          idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 1#8 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP idSavePollName ▸ hStore.idSavePoll
  refine s5_call_raw hExt.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [idSavePollSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx8, hnameLt, hpathLt, hchgLt, hpathOk, hwf⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [idSavePollSpec, Spec.inImage, sepExists_sepConj_left, satisfies_sepExists,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨_, _, ⟨⟨_, htrm⟩, _⟩, _⟩ := hpost; exact htrm
  · intro sm R' hpost; simp only [idSavePollSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [idSavePollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [idSavePollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [idSavePollSpec, Spec.inImage, hsp, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.exists_elim fun p => ?_
    refine SepWPp.pure_elim fun ⟨⟨hgr, _⟩, hp⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr p hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hgr hp)

theorem s5_call_idSavePoll {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp : BitVec 64) (g : IdPollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSavePollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.call.fut) (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hpathLt : g.peers.path.length < 2 ^ 32) (hchgLt : g.peers.changed.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.peers.path g.call.call.addr.val.name))
    (hwf : ∀ bs, g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name = .ok bs → IdFileWf bs)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 0#8 ∗
      dirAt A (g.self + 0x28#64) g.peers ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8)))
      (p : Except Unit (Option IdentityKey)),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      gr = g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name → IdPeerAns gr p →
      SepWPp (initProg img W) ret sm
        ((idSaveOutAt A g.call.out (idSaveOf p g.call.call.key) ∗
          dirAt A (g.self + 0x28#64)
            (idSavePeers g.peers g.call.call.addr.val.name g.call.call.key p) ∗
          idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 1#8 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_idSavePoll_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp g F hpc hrun hsp hsp_align hlr htr hinv hx0 hx8 hnameLt hpathLt hchgLt hpathOk hwf hpan hpre hnext

theorem s5_call_memcpy_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {callee ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base extP) callee ((sessionMemcpySpec extHookStack).inImage img))
    (fsp dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  refine s5_call_raw hExt.fs hcall (dst, src, bs) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessionMemcpySpec, libcMemcpySpec, stackAt, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _))
  · intro sm R' hpost; simp only [sessionMemcpySpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.2
  · intro sm R' hpost; simp only [sessionMemcpySpec, Spec.inImage] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost; simp only [sessionMemcpySpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [sessionMemcpySpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [sessionMemcpySpec, Spec.inImage, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_memcpy {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W))
    (hcall : subroutine_ok (initProg img W) callee ((sessionMemcpySpec extHookStack).inImage img))
    (fsp dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProg img W) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_memcpy_ext (stage5ExternDeps_of_runHooks hh) hcall fsp dst src bs F
    hpc hrun hsp hsp_align hlr htr hinv hx0 hx1 hx2 hpan hpre hnext

theorem s5_call_promoteState_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {callee ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP)
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base extP) callee
      (promoteStateEmptyExtSpec img (extHookStack + 32)))
    (fsp recPtr srcPtr : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = recPtr) (hx1 : s.readReg64 .x1 = srcPtr) (hbLen : bs.length = 344)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗ stackAt fsp (extHookStack + 32)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗ stackAt fsp (extHookStack + 32)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  refine s5_call_raw hExt.fs hcall (recPtr, srcPtr, bs) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [promoteStateEmptyExtSpec, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hbLen⟩ (Entails.refl _))
  · intro sm R' hpost; simp only [promoteStateEmptyExtSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost; simp only [promoteStateEmptyExtSpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost; simp only [promoteStateEmptyExtSpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [promoteStateEmptyExtSpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [promoteStateEmptyExtSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_promoteState {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W))
    (hcall : subroutine_ok (initProg img W) callee Pqxdh.ResponderStore.promoteStateEmptySpec)
    (fsp recPtr srcPtr : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = recPtr) (hx1 : s.readReg64 .x1 = srcPtr) (hbLen : bs.length = 344)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗
      cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProg img W) ret sm
        ((((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
          cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp := by
  refine s5_call_raw hh.fs hcall (recPtr, srcPtr, bs) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hbLen⟩ (Entails.refl _)
  · intro sm R' hpost; simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost; simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost; exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost; simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [Pqxdh.ResponderStore.promoteStateEmptySpec] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [Pqxdh.ResponderStore.promoteStateEmptySpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_sessStoreShim_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp : BitVec 64) (c : StoreShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStoreShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = c.self) (hx1 : s.readReg64 .x1 = c.addrA) (hx2 : s.readReg64 .x2 = c.recA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + sessStoreFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗ sessStoreBoxAt (sm.readReg64 .x0) c.self c.addrA c.recA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP sessStoreShimName ▸ hStore.sessStoreShim
  refine s5_call_raw hExt.fs hcall c F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessStoreShimSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _))
  · intro sm R' hpost; simp only [sessStoreShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.2.2.2
  · intro sm R' hpost; simp only [sessStoreShimSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [sessStoreShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [sessStoreShimSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [sessStoreShimSpec, Spec.inImage, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, hnz, hal8, _⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm hx1m hnz hal8)

theorem s5_call_sessStoreShim {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp : BitVec 64) (c : StoreShimCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStoreShimName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = c.self) (hx1 : s.readReg64 .x1 = c.addrA) (hx2 : s.readReg64 .x2 = c.recA)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = img.base + sessStoreFutVtOff →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProg img W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗ sessStoreBoxAt (sm.readReg64 .x0) c.self c.addrA c.recA 0#8 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_sessStoreShim_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp c F hpc hrun hsp hsp_align hlr htr hinv hx0 hx1 hx2 hpan hpre hnext

theorem s5_call_sessStorePoll_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets} {stk : Nat} {ret_pc ret : BitVec 64}
    (hExt : Stage5ExternDeps img A extP) (hStore : InitStoreCalleesExt img A extP B stk)
    (fsp : BitVec 64) (g : SessStorePollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStorePollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.call.fut) (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hencLt : (E2E.Record.encodeRecord g.call.call.record).length < 2 ^ 32)
    (hchgLt : g.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 0#8 ∗
      dirAt A g.self g.dir ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (tripleRatchetProgAtExt img.base extP) ret sm
        ((sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 1#8 ∗
          dirAt A g.self (g.dir.put (addressText g.call.call.addr.val)
            (E2E.Record.encodeRecord g.call.call.record)) ∗
          (g.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (g.call.out + 8#64) 40 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) ret s P Q Qp := by
  have hcall := s5Prog_fnAddr_eq img extP sessStorePollName ▸ hStore.sessStorePoll
  refine s5_call_raw hExt.fs hcall g F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessStorePollSpec, Spec.inImage, hsp, sepConj_assoc]
    exact Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx8, hnameLt, hencLt, hchgLt⟩ (Entails.refl _))
  · intro sm R' hpost; simp only [sessStorePollSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1
  · intro sm R' hpost; simp only [sessStorePollSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.1.1
  · intro code sm R' hpost; simp only [sessStorePollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost; simp only [sessStorePollSpec, Spec.inImage] at hpost; exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hinvm htrm hfilesm
    simp only [sessStorePollSpec, Spec.inImage, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hinvm htrm hfilesm)

theorem s5_call_sessStorePoll {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (fsp : BitVec 64) (g : SessStorePollGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStorePollName))
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace) (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = g.call.fut) (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hencLt : (E2E.Record.encodeRecord g.call.call.record).length < 2 ^ 32)
    (hchgLt : g.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 0#8 ∗
      dirAt A g.self g.dir ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
      sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
      A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProg img W) ret sm
        ((sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 1#8 ∗
          dirAt A g.self (g.dir.put (addressText g.call.call.addr.val)
            (E2E.Record.encodeRecord g.call.call.record)) ∗
          (g.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (g.call.out + 8#64) 40 ∗
          protocolAddressAt A g.call.call.addr g.call.call.addrA ∗
          sessionRecordAt A g.call.call.recA g.call.call.g g.call.call.record ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp) :
    SepWPp (initProg img W) ret s P Q Qp :=
  s5_call_sessStorePoll_ext (stage5ExternDeps_of_runHooks hh) (initStoreCallees_to_ext hStore)
    fsp g F hpc hrun hsp hsp_align hlr htr hinv hx0 hx8 hnameLt hencLt hchgLt hpan hpre hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
