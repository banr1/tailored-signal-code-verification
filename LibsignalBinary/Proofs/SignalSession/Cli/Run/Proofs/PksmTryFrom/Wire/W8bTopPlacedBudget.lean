/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlaced
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup

/-!
# Budget-Threaded `PreKeySignalMessage::try_from` Contract (Placed)

Establishes the `[LibsignalPlacement]` budget-pool contract for `PreKeySignalMessage::try_from`
(Block `111`) under allocation envelope `PksmTryFromEnv` from `CodecHooksPlaced M A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyPlacedProg preKeyTryFromStack preKeyTryFromSubStack)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded lsLogOff smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Wire (entails_of_eq)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (pksmErrE pksmParse_decodeNone pksmParse_ver_ok_iff stackAt_preKeyTryFromSubStack_skipField)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced pksmCalleesPlaced_of_codecHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCPlacedBudget (err_epilogue_504_placed_wp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailWPlacedBudget (preKey_loopErr_460_placed_wpE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlacedBudget (PreKeyDecodeLoopF4OkWPlaced preKeyDecodeLoopF4W_of_callees_placed_ok preKey_earlyErr_to_504_placed_wpE preKey_valid_to_460_placed_wpW)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (PksmAfterLoopEnv PksmLoopEnv PksmPostEnv PksmTryFromEnv fitsEnv_pksmTryFrom_loop fitsEnv_pksmTryFrom_post w8bRetPost_prepend w8bRetPost_to_specPost w8b_errRetPost_noHeap_placed w8b_errRetPost_placed w8b_loopExit_regroup_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAux (PreKeyPostLoopOkNoPanicWPlaced preKeyNoPanicQp preKeyPostLoopOkNoPanicW_of_codecHooks w8b_bind_frame_noPanic)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget

open Arm64
open ProofLib hiding SepWPp
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget (
  pksmTryFromSpecPlaced SubsetA4PksmTryFromPlaced
)

/-- Whole-body execution of `PreKeySignalMessage::try_from` from `(blkPl_111).base` to return under
allocation envelope `PksmTryFromEnv`. -/
theorem preKey_entry_to_ret_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced M A lim H)
    (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced M A lim H)
    (hPost : PreKeyPostLoopOkNoPanicWPlaced M A lim H)
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {st : M.σ} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PksmTryFromEnv x))
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpecPlaced M A lim PksmTryFromEnv).post (x, st) s0 sf))
      preKeyNoPanicQp := by
  have hsplit : stackAt s0.sp preKeyTryFromStack =
      stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 :=
    CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split s0.sp
  rw [hsplit]
  by_cases hvalid : ∃ vb b1 bs1, x.bytes = vb :: b1 :: bs1 ∧
      ¬ (vb >>> 4) < 3#8 ∧ ¬ 4#8 < (vb >>> 4)
  · obtain ⟨vb, b1, bs1, hcons, hge3, hle4⟩ := hvalid
    have hv_ok : 0x30#8 ≤ vb ∧ vb ≤ 0x4f#8 :=
      (pksmParse_ver_ok_iff vb).mp (not_or.mpr ⟨hge3, hle4⟩)
    have hfitLoop : FitsEnv M lim st (PksmLoopEnv x) :=
      fitsEnv_pksmTryFrom_loop hcons hge3 hle4 hfit
    rw [stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96 ∗
          A.pool lim st s0 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
        (memRegion x.ret 248 ∗ lsLogOff ∗ memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
            (preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine w8b_bind_frame_noPanic
      (preKey_valid_to_460_placed_wpW (M := M) (A := A) (lim := lim) (st := st)
        hLoopF4 hfitLoop hcons hge3 hle4 hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, evsL, hevsL, hent1⟩
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (w8b_loopExit_regroup_placed A lim (M.stepEvents evsL st) x s0 s1 vb b1 bs1
        (s1.readReg64 .x24) (CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1)) hcons) ?_
    cases hdec : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) with
    | none =>
      have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none := by
        rw [hcons]; exact pksmParse_decodeNone hv_ok hdec
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun mErr => ?_
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx24_ne => ?_
      refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
        (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by apply entails_of_eq; sep_ac_rfl)
          (preKey_loopErr_460_placed_wpE (M := M) (A := A) (lim := lim)
            (st := M.stepEvents evsL st) (x := x) hC.deallocX hC.dropDecodeError
            hst1 hpc1 hrun1 rfl hx24_ne mErr)) ?_
      rintro sf Pf _ _ ⟨hsp_f, hcs_f, _hcl_f, _htr_f, evsF, hfreeF, hPf⟩
      have henv : PksmTryFromEnv x (evsL ++ evsF) :=
        .loopAfter hcons hge3 hle4 hevsL (by simp [PksmAfterLoopEnv, hdec]; exact hfreeF)
      rw [← M.stepEvents_append] at hPf
      exact w8bRetPost_to_specPost (Env := PksmTryFromEnv)
        (w8b_errRetPost_placed hparse henv ⟨hsp_f, hcs_f, hPf⟩)
    | some m =>
      simp only [sepConj_assoc]
      refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx24 => ?_
      have hfitPost : FitsEnv M lim (M.stepEvents evsL st) (PksmPostEnv vb x.bytes m) :=
        fitsEnv_pksmTryFrom_post hcons hge3 hle4 hdec hevsL hfit
      refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
        (hPost x (M.stepEvents evsL st) s0 s1 vb b1 bs1 m hfitPost hcons hge3 hle4 hlt hdec hst1
          hpc1 hrun1 hx24) ?_
      rintro sf Pf _ _ hret
      exact w8bRetPost_to_specPost (Env := PksmTryFromEnv)
        (w8bRetPost_prepend
          (fun _ h2 => .loopAfter hcons hge3 hle4 hevsL (by simp [PksmAfterLoopEnv, hdec]; exact h2))
          hret)
  · have herr : x.bytes = [] ∨ (∃ vb body, x.bytes = vb :: body ∧
        ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])) := by
      rcases hb : x.bytes with _ | ⟨vb, _ | ⟨b1, bs1⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨vb, [], rfl, Or.inr (Or.inr rfl)⟩
      · refine Or.inr ⟨vb, b1 :: bs1, rfl, ?_⟩
        by_cases h3 : (vb >>> 4) < 3#8
        · exact Or.inl h3
        · by_cases h4 : 4#8 < (vb >>> 4)
          · exact Or.inr (Or.inl h4)
          · exact absurd ⟨vb, b1, bs1, hb, h3, h4⟩ hvalid
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion x.ret 248 ∗
          memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96 ∗
          A.pool lim st s0) ∗
        (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗ lsLogOff))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine w8b_bind_frame_noPanic
      (preKey_earlyErr_to_504_placed_wpE (M := M) (A := A) (lim := lim) (st := st)
        herr hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, hparse, e, hent1⟩
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    have hsub_eq : preKeyTryFromSubStack = smallRootStack := rfl
    refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (by rw [hsub_eq]; apply entails_of_eq; sep_ac_rfl)
        (err_epilogue_504_placed_wp (M := M) (A := A) (lim := lim) (H := H) (x := x)
          (sretOut := pksmErrE A.repAlloc [] x.ret e) (st := st) hsp hst1 hpc1 hrun1)) ?_
    rintro sf Pf _ _ ⟨hsp_f, hcs_f, hPf⟩
    have henv : PksmTryFromEnv x [] := .nil
    exact w8bRetPost_to_specPost (Env := PksmTryFromEnv)
      (w8b_errRetPost_noHeap_placed hparse henv ⟨hsp_f, hcs_f, by simpa using hPf⟩)

/-- Reduces `subroutine_ok` for `PreKeySignalMessage::try_from` (Block `111`) to the protobuf
decode loop, post-loop continuation, and `PksmCalleesPlaced`. -/
theorem pksmTryFromPlaced_ok_of_postLoop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced M A lim H)
    (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced M A lim H)
    (hPost : PreKeyPostLoopOkNoPanicWPlaced M A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (pksmTryFromSpecPlaced M A lim PksmTryFromEnv) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  apply reaches_outcome.of_codeLoaded
  intro hL
  obtain ⟨hcl, hpre'⟩ := CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [pksmTryFromSpecPlaced] at hpre'
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hlt, hx8, _hsp_ge, hfit⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0) ∗ R := by
    change s0.mem ⊨ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
      stackAt s0.sp preKeyTryFromStack ∗ A.pool lim st s0 ∗ R at hmem
    ac_nf at hmem ⊢
  have hfull := preKey_entry_to_ret_placed_wpX hC hLoopF4 hPost
    hlt hfit hpc hrun hsp hcl hx0 hx1 hx8
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with
    ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hvregs_f⟩ |
    ⟨_, _, _, htr_f⟩ |
    ⟨_, hoom⟩
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hvregs_f⟩,
        Satisfies.mono (sepConj_mono_left hent_f) hmf⟩))
  · exact False.elim htr_f
  · exact (allowPanic_not_exited hoom).elim

/-- Budget-threaded `PreKeySignalMessage::try_from` contract (Block `111`) from `CodecHooksPlaced M A lim H`. -/
theorem pksmTryFromPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok ((CryptoVerification.blkPC_111).rebase (CryptoVerification.blkPl_111).base H)
      (CryptoVerification.blkPl_111).base
      (pksmTryFromSpecPlaced M A lim PksmTryFromEnv) := by
  have hC : PksmCalleesPlaced M A lim H := pksmCalleesPlaced_of_codecHooks hH
  exact pksmTryFromPlaced_ok_of_postLoop hC
    (preKeyDecodeLoopF4W_of_callees_placed_ok hC)
    (preKeyPostLoopOkNoPanicW_of_codecHooks hH hC)

theorem subsetA4PksmTryFromPlaced_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    SubsetA4PksmTryFromPlaced M A lim PksmTryFromEnv H :=
  ⟨pksmTryFromPlaced_ok hH⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bTopPlacedBudget
