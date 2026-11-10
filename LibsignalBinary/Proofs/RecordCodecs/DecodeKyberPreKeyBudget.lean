/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Epilogue
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.EpilogueBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.FetchesBudget
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `signal_session::stores::decode_kyber_pre_key` Proof

Proves `decodeKyberPreKey_placed_ok_of_decode` (`decodeKyberPreKeyPlacedSpec`) under
`[LibsignalPlacement]` (Block `595`) over `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKeyBudget

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open ProofLib.ProgramReflection CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification.RecordCodecsBinary (sepWPp_of_sepWP_lscro signedDecodeResultAt signedDecodeStack)
open CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers (KpkSavedRegs kpkFrame32_unpack kpkSpAligned_sub128 kpkStack_smallRoot_split kpkSubStack)
open LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.EpilogueBudget (epilogue_err_placed_wp epilogue_ok_placed_wp kpkOff_retDec kpkOff_retDrop kpkPostPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.FetchesBudget (noPanicQp sepWPp_call_budget_lscro signedDecode_placed_call_ok)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SpkLoopEnv decodeKyberPreKeyPlacedSpec decodeKyberPreKeyRawSpec dropDecodeErrorBudgetSpec signedDecodePlacedSpec signedDecodeRawSpec)
attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] kpkOff_retDec kpkOff_retDrop

/-- Relocatable `decode_kyber_pre_key` (block `595`) meets `decodeKyberPreKeyPlacedSpec`,
given the relocatable inner decoder contract (block `562`) and `drop_glue::<DecodeError> [local#3]`
(block `555`). -/
theorem decodeKyberPreKey_placed_ok_of_decode [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hDecode : subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodePlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_551 H) (blkPl_551).base (dropDecodeErrorBudgetSpec M A lim)) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeKyberPreKeyPlacedSpec A lim) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp hL => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [decodeKyberPreKeyRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hne, hlt, hFit⟩, hmem⟩
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0) ∗ R := by
    ac_nf at hmem ⊢
  have hcall := signedDecode_placed_call_ok hDecode
  have hsp128 := kpkSpAligned_sub128 hsp
  have hfull : Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (kpkPostPlaced A lim st x s0)
      (noPanicQp s0) := by
    rw [kpkStack_smallRoot_split s0.sp]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (kpkFrame32_unpack (s0.sp - 128#64))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Wire.SepWPp.exists_pre fun c0 => Wire.SepWPp.exists_pre fun c1 =>
      Wire.SepWPp.exists_pre fun c2 => Wire.SepWPp.exists_pre fun c3 => ?_
    clear hDecode
    have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
    have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base) ?_
    wp_steps_sync_pool (blkPl_562).base
    refine Wire.SepWP.done (by simp [arm64_norm]; rfl)
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    have hsp120 : s0.sp - 120#64 = s0.sp - 128#64 + 8#64 := by bv_omega
    refine sepWPp_call_budget_lscro (⟨x.bytesA, x.bytes, s0.sp - 128#64 + 8#64⟩, st) hcall
      (by simp [arm64_norm]; rfl)
      (by simp [hrun, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp128) hcrl1
      (ret_pc := (blkPl_595).base + kpkOff_retDec) (by simp [arm64_norm])
      (by simp [arm64_norm])
      (T := (x.bytesA ↦ₛ x.bytes) ∗ memRegion (s0.sp - 128#64 + 8#64) 88 ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗ A.pool lim st _)
      (φ := (s0.readReg64 .x2).toNat = x.bytes.length ∧
        0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32 ∧
        FitsEnv M lim st (SpkLoopEnv (2 * x.bytes.length + 3) x.bytes.length))
      (by simp [signedDecodeRawSpec, h1, hsp120, arm64_norm]; rfl)
      ⟨hx2_nat, hne, hlt, hFit⟩
      (by simp only [hsp120, arm64_norm]
          change _ = _ ∗ _ ∗ _ ∗ _ ∗ (memRegion x.ret 88 ∗
            memRegion (s0.sp - 65536#64) (kpkSubStack - signedDecodeStack) ∗
            memRegion (s0.sp - 128#64) 8 ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
          ac_rfl)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [signedDecodeRawSpec]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun evs1 => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    refine Wire.SepWPp.pure_pre fun hevs1 => ?_
    have hsp2_eq : s2.sp = s0.sp - 128#64 := by simpa [arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [h0, arm64_norm] using hcs2.1
    have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hcs2
    have hasub : s0.sp - 128#64 - 65408#64 = s0.sp - 65536#64 := by bv_omega
    have ha96 : s0.sp - 128#64 + 96#64 = s0.sp - 32#64 := by bv_omega
    have ha104 : s0.sp - 128#64 + 104#64 = s0.sp - 24#64 := by bv_omega
    have ha112 : s0.sp - 128#64 + 112#64 = s0.sp - 16#64 := by bv_omega
    have ha120 : s0.sp - 128#64 + 120#64 = s0.sp - 8#64 := by bv_omega
    cases hdec : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.decode x.bytes with
    | none =>
      dsimp only [signedDecodeResultAt]
      have ha16 : s0.sp - 128#64 + 8#64 + 8#64 = s0.sp - 128#64 + 16#64 := by bv_omega
      have ha24 : s0.sp - 128#64 + 8#64 + 16#64 = s0.sp - 128#64 + 24#64 := by bv_omega
      rw [ha16, ha24]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Wire.SepWPp.exists_pre fun e => ?_
      have he := epilogue_err_placed_wp (A := A) (lim := lim) (st := st) hDrop hdec hevs1
        hpc2 hrun2 hsp2_eq hsp2_align hcrl2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2 (e := e)
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
    | some m =>
      dsimp only [signedDecodeResultAt]
      have he := epilogue_ok_placed_wp (A := A) (lim := lim) (st := st) (H := H) hdec hevs1
        hpc2 hrun2 hsp2_eq hsp2_align hcrl2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKeyBudget
