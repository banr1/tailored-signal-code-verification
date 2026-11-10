/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMoves
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMovesDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Previous-Session `memcpy` Chain Proof

Relocatable (`[LibsignalPlacement]`) proof of `OverPrevMovesCliPlacedStmt`
(`(blkPl_518).base + 0x2620 → (blkPl_518).base + 0x1fd4`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem entails_replace_sub_mv_pl {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

private theorem cmn_1_ne_zero_pl {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

private theorem cmn_2_ne_zero_pl {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

private theorem ss320_bytes_eq_pl (sp : BitVec 64) (r1 r2 : List (BitVec 8))
    (hr1 : r1.length = 304) :
    (((sp + 0x948#64) ↦ₛ r1) ∗
     ((sp + 0xa78#64) ↦₃₂ 4#32) ∗
     ((sp + 0xa7c#64) ↦ₛ r2)) =
    ((sp + 0x948#64) ↦ₛ (r1 ++ unpack32 4#32 ++ r2)) := by
  have e1 : sp + 0x948#64 + BitVec.ofNat 64 304 = sp + 0xa78#64 := by bv_omega
  have e2 : sp + 0xa78#64 + BitVec.ofNat 64 4 = sp + 0xa7c#64 := by bv_omega
  simp only [List.append_assoc]
  rw [pointsToBytes_append, hr1, e1, pointsToBytes_append, unpack32_length, e2,
      ← pointsTo32_eq_pointsToBytes]

private theorem overPrevMovesSS_eq_cells_pl (sp w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8)) :
    overPrevMovesSS (sp + 0x930#64) w0 w1 w2 r1 r2 =
      (((sp + 0x930#64) ↦₆₄ w0) ∗ ((sp + 0x938#64) ↦₆₄ w1) ∗ ((sp + 0x940#64) ↦₆₄ w2) ∗
       ((sp + 0x948#64) ↦ₛ r1) ∗ ((sp + 0xa78#64) ↦₃₂ 4#32) ∗ ((sp + 0xa7c#64) ↦ₛ r2)) := by
  dsimp only [overPrevMovesSS]
  have e1 : sp + 0x930#64 + 8#64 = sp + 0x938#64 := by bv_omega
  have e2 : sp + 0x930#64 + 0x10#64 = sp + 0x940#64 := by bv_omega
  have e3 : sp + 0x930#64 + 0x18#64 = sp + 0x948#64 := by bv_omega
  have e4 : sp + 0x930#64 + 0x148#64 = sp + 0xa78#64 := by bv_omega
  have e5 : sp + 0x930#64 + 0x14c#64 = sp + 0xa7c#64 := by bv_omega
  rw [e1, e2, e3, e4, e5]

private theorem overPrevMovesSS_merge_eq_pl (sp w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8))
    (hr1 : r1.length = 304) :
    overPrevMovesSS (sp + 0x930#64) w0 w1 w2 r1 r2 =
      (((sp + 0x930#64) ↦₆₄ w0) ∗ ((sp + 0x938#64) ↦₆₄ w1) ∗ ((sp + 0x940#64) ↦₆₄ w2) ∗
       ((sp + 0x948#64) ↦ₛ (r1 ++ unpack32 4#32 ++ r2))) := by
  rw [overPrevMovesSS_eq_cells_pl, ← ss320_bytes_eq_pl sp r1 r2 hr1]

private theorem pointsToBytes_320_entails_memRegion_pl (p : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 320) :
    (p ↦ₛ bs) ⊢ memRegion p 320 := by
  rw [← hbs]
  exact pointsToBytes_entails_memRegion p bs

set_option maxHeartbeats 1200000 in
/-- Proves `OverPrevMovesCliPlacedStmt` (`(blkPl_518).base + 0x2620 → (blkPl_518).base + 0x1fd4`). -/
theorem overPrevMoves_cli_placed_ok [LibsignalPlacement] : OverPrevMovesCliPlacedStmt := by
  intro ext hmemcpy s w0 w1 w2 u920 r1 r2 hw0 hr1 hr2 hpc hrun hsp_align hx21
  let bs := r1 ++ unpack32 4#32 ++ r2
  have hbs : bs.length = 320 := by
    simp only [bs, List.length_append, hr1, hr2, unpack32_length]
  have hcmn1 : (w0 + 1#64 == 0#64) = false := cmn_1_ne_zero_pl hw0
  have hcmn2 : (w0 + 2#64 == 0#64) = false := cmn_2_ne_zero_pl hw0
  rw [overPrevMovesSS_merge_eq_pl s.sp w0 w1 w2 r1 r2 hr1]
  change SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1fd4#64) s
    ((((s.sp + 0x930#64) ↦₆₄ w0) ∗ ((s.sp + 0x938#64) ↦₆₄ w1) ∗ ((s.sp + 0x940#64) ↦₆₄ w2) ∗
      ((s.sp + 0x948#64) ↦ₛ bs)) ∗
      memRegion (s.sp + 0x560#64) 320 ∗ memRegion (s.sp + 0x6a0#64) 320 ∗
      memRegion (s.sp + 0x7e0#64) 320 ∗ ((s.sp + 0x920#64) ↦₆₄ u920) ∗
      stackAt s.sp allocHookStack) _
  conv => arg 4; rw [← hbs]
  simp only [sepConj_assoc]
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x930#64 := hx21
  have h948 : s.sp + 0x930#64 + 0x18#64 = s.sp + 0x948#64 := by bv_omega
  have hlen_nat : (0x140#64).toNat = bs.length := hbs.symm
  wp_steps
  wp_call hmemcpy (s.sp + 0x7e0#64, s.sp + 0x948#64, bs)
  wp_steps
  wp_call hmemcpy (s.sp + 0x6a0#64, s.sp + 0x7e0#64, bs)
  wp_steps
  wp_call hmemcpy (s.sp + 0x560#64, s.sp + 0x6a0#64, bs)
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_entails_memRegion (s.sp + 0x7e0#64) bs)
      (by sep_focus) rfl) ?_
  wp_steps
  wp_call hmemcpy (s.sp + 0x7e0#64, s.sp + 0x560#64, bs)
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_entails_memRegion (s.sp + 0x948#64) bs)
      (by sep_focus) rfl) ?_
  wp_steps
  wp_call hmemcpy (s.sp + 0x948#64, s.sp + 0x7e0#64, bs)
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (Entails.of_eq (ss320_bytes_eq_pl s.sp r1 r2 hr1).symm)
      (by sep_focus) rfl) ?_
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x560#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x6a0#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x7e0#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, wp_norm, CalleeSavedPreserved]⟩
  rw [← ss320_bytes_eq_pl s.sp r1 r2 hr1]
  simp_all only [sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
