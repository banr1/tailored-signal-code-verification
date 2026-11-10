/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErr
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P3 Version-Mismatch Path

Budget-threaded `[LibsignalPlacement]` and `[LibsignalFullPlacement]` proofs of the Stage P3
version-mismatch path (`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) over general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `StageP3VerNeM3Env`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState SignalProtocolError)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack vecAt vecBuf vecHeader)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (recordResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (SessionInline sessionHeap)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStack withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost dropSessionStructureLocal2Stack growOneSpeStack
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (words6At)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  cap_ne_noneCap_of_lt cell_join_head8 cell_split_head8 decryptPrekeySavedRegsAt_add_cd0
  dfPtr_words_eq_decryptionFailedStr errs48_144_join extractLsb0_8_of_unpack64_cons
  memRegion20_fold memRegion20_split_eq memRegion48_words6_split_eq memRegion_17_split_eq
  outPtr48_split_eq repack20_32_64_64_to_64_64_32 sessionStateAt_pack_head_tail
  sessionStateAt_unpack_head_tail sp370_36_err_fold sp370_36_err_split_eq
  words3_repack_w32_2w64_w32 words6At_preKey_decryptionFailed_entails_recordResultAt
  words6_entails_memRegion48
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  coro_e0_3w_344_entails_368 prevSessionsEmptyAt prevSessionsEmptyAt_unpack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (pqLogLevelCellPlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustAllocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (
  dropSpe2VerSpec drop_spe2_ver_placed_ok_at
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (
  VerNeS1Env overVerNe_1e04_to_1e78_cro_placed_at_gen
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv bind_sepWP_cro_frame_tail bind_sepWPp_nopanic_tail call_lscl_nopanic_tail
  call_lscl_ro_nopanic_tail drop_frame_tail fitsAlloc17_of_fitsEnv freeOnlyEvs_append
  freeOnlyEvs_dealloc_192_8 intro_lsro_decryptionFailed_tail_pl p3_alloc_33b0_tail_placed_ok
  sepWPp_add_cro_tail verNeTailEnv_of_freeSuffix weaken_frame_tail
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudgetAux (
  StageP3VerNeM3Env dpClosureEntryVerPlaced fitsS1_of_fitsM3 fitsTail_of_fitsM3
  freeOnlyEvs_dealloc_prev p3_err_tail_prev_dealloc_placed_wp p3_err_tail_prev_zero_placed_wp
  p3_err_ver_d_placed_wp p3_err_ver_e_placed_wp p3_err_ver_f_placed_wp
  stageP3ErrPostPrevEmptyM3Placed stageP3VerNeM3Env_of_parts
)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private theorem sp3e0_cell_336_entails_344 (sp val : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ val) ∗ memRegion (sp + 0x3e8#64) 336 ⊢
      memRegion (sp + 0x3e0#64) 344 := by
  rw [show (344 : Nat) = 8 + 336 from rfl,
      memRegion_split (sp + 0x3e0#64) 8 336 (by decide),
      show sp + 0x3e0#64 + 8#64 = sp + 0x3e8#64 by bv_omega,
      ProofLib.memRegion_eight (sp + 0x3e0#64)]
  exact sepConj_mono_left (Entails.sepExists_intro val)

/-! ## Common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded general-`prevCap` common error epilogue (`lsmpl.base 512 → s0.readReg64 .x30`)
under `[LibsignalPlacement]`, emitting `FreeOnlyEvs`. -/
theorem stageP3_err_tail_common_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ)
    (s0 s : State) (coroPtr outPtr errTag w0 w1 w2 w3 w4 : BitVec 64) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = lsmpl.base 512) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryVerPlaced + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s ∗ stackAt s.sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P_f ⊢ memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr errTag w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt s.sp dropSessionStructureLocal2Stack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      Qp := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscl_nopanic_tail
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st0))
    (φ := s.readReg64 .x0 = coroPtr + 0xf8#64 ∧ LsRetAddr624 (s.readReg64 .lr))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st0 s ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro hL hDropSS3 hpc hrun hsp_al hx30
    (by dsimp only [dropSessionStructureLocal2Spec])
    (And.intro hx0 (by
      change LsRetAddr624 (s.readReg64 .x30)
      rw [hx30]
      exact lsRetAddr624_blockPlacement_base_add 518 0x359c#64 (by decide) (by decide)))
    (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 hL1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => ?_
  refine SepWPp.pure_elim fun ⟨htr1_s, hfree_ss⟩ => ?_
  let st1 := M.stepEvents evs_ss st0
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  refine weaken_frame_tail (prevSessionsEmptyAt_unpack A.repAlloc coroPtr g) (by sep_focus) ?_
  refine weaken_frame_tail
    (T := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (T' := ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine weaken_frame_tail (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine weaken_frame_tail
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj, sepConj_emp]
    have hstep2 := p3_err_tail_prev_zero_placed_wp A lim ext st1 s1 coroPtr outPtr errTag g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_cro_frame_tail hcro1 hL1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hLf hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine weaken_frame_tail
      (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine weaken_frame_tail
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine weaken_frame_tail
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine weaken_frame_tail hout_words (by sep_focus) ?_
    refine SepWPp.done hpcf hrunf ?_
    refine ⟨⟨evs_ss, hfree_ss, Entails.of_eq (by sep_ac_rfl)⟩,
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
       True.intro⟩,
      hcrof, hLf, hvregs_f.trans hvregs_cs1⟩
  · simp only [hcap, ↓reduceIte]
    refine weaken_frame_tail
      (Entails.of_eq (show A.repAlloc.live g.prevPtr (g.prevCap.toNat * 24) 8 =
        A.live g.prevPtr (g.prevCap.toNat * 24) 8 from rfl))
      (by sep_focus) ?_
    have hstack_alloc :
        stackAt s.sp dropSessionStructureLocal2Stack =
          memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
      stackAt_split_bottom s.sp allocHookStack 96 (by decide)
    refine weaken_frame_tail (Entails.of_eq hstack_alloc) (by sep_focus) ?_
    have hstep2 := p3_err_tail_prev_dealloc_placed_wp ext hdealloc st1 s1 coroPtr outPtr errTag
      g.prevCap g.prevPtr
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
    rw [hsp1_s] at hstep2
    refine bind_sepWP_cro_frame_tail hcro1 hL1 hstep2 (by sep_focus)
      fun sf hpcf hrunf hcrof hLf hregsf => ?_
    rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine weaken_frame_tail (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
    refine weaken_frame_tail
      (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
    refine weaken_frame_tail
      (sp370_36_err_fold s.sp
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        w3 w4 (w2.extractLsb' 32 32))
      (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
    refine weaken_frame_tail (Entails.of_eq hrepack_out8) (by sep_focus) ?_
    refine weaken_frame_tail
      (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
    refine weaken_frame_tail hout_words (by sep_focus) ?_
    have hpool_eq :
        A.pool lim (M.stepEvents (rustDeallocEvents (g.prevCap.toNat * 24) 8) st1) sf =
          A.pool lim (M.stepEvents (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) st0) sf := by
      dsimp only [st1]
      rw [← M.stepEvents_append]
    have hfree_all : FreeOnlyEvs (evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8) :=
      freeOnlyEvs_append hfree_ss (freeOnlyEvs_dealloc_prev _)
    refine SepWPp.done hpcf hrunf ?_
    refine ⟨⟨evs_ss ++ rustDeallocEvents (g.prevCap.toNat * 24) 8, hfree_all, ?_⟩,
      hspf_s, htrf_1.trans (htr1_s.trans htr),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
       True.intro⟩,
      hcrof, hLf, hvregs_f.trans hvregs_cs1⟩
    rw [← hpool_eq]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## Version-mismatch tail (`+0x33b0 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded relocatable `[LibsignalPlacement]` Stage P3 version-mismatch tail
(`dpClosureEntryVerPlaced + 0x33b0 → s0.readReg64 .x30`) under `FitsEnv M lim st0 VerNeTailEnv`. -/
theorem stageP3_err_ver_tail_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 VerNeTailEnv)
    (s0 s s7 : State) (coroPtr outPtr errsPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro7 : LibsignalCodeRoLoaded lsmpl s7.mem)
    (hL7 : (lsProg_518 ext).CodeLoaded s7.mem)
    (hpc7 : s7.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace) (hx0_7 : s7.readReg64 .x0 = 17#64)
    (hx1_7 : s7.readReg64 .x1 = 1#64) (hx19_7 : s7.readReg64 .x19 = coroPtr)
    (hx24_7 : s7.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_7 : s7.readReg64 .x25 = s.sp + 0x210#64) (hx26_7 : s7.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
       memRegion (errsPtr + 12#64) 36 ∗ memRegion (errsPtr + 48#64) 144 ∗ A.live errsPtr 192 8 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st0 s7 ∗ stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, VerNeTailEnv evs ∧
          (P_f ⊢
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s.sp growOneSpeStack)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s7)
      Qp := by
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := sepWPp_add_cro_tail hcro7
    (p3_alloc_33b0_tail_placed_ok (M := M) (A := A) (lim := lim) (Qp := fun _ _ => False)
      ext halloc st0 (fitsAlloc17_of_fitsEnv hfits) s7 emp hL7 hpc7 hrun7 hsp7_align hx0_7 hx1_7)
  rw [sepConj_emp, hs7_sp] at halloc17
  refine bind_sepWPp_nopanic_tail halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨⟨hP8, hdf_ne, hsp8_7, htr8_7, hcs8, hL8⟩, hcro8⟩ => ?_
  rw [sepConj_emp] at hP8
  let st8 := M.stepEvents (rustAllocEvents 17 1) st0
  refine weaken_frame_tail hP8 (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 =>
    SepWPp.exists_elim fun u_df0 => ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine weaken_frame_tail (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3)) (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7
  refine intro_lsro_decryptionFailed_tail_pl hcro8 ?_
  have hstep9 := p3_err_ver_e_placed_wp A lim ext st8 s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64 u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10
    (w3.extractLsb' 0 8) hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine bind_sepWP_cro_frame_tail hcro8 hL8 hstep9 (by sep_focus)
    fun s9 hpc9 hrun9 hcro9 hL9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, _, hx28_9, _, hx30_9, hvregs_9⟩
  refine drop_frame_tail
    (P_drop := ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20") ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((lsρ "libsignal_cli_handshake:.rodata..Lanon.20" + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine weaken_frame_tail
    (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s8.readReg64 .x0))) (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine weaken_frame_tail (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_lscl_ro_nopanic_tail
    (spec := dropSpe2VerSpec M A lim) (x := (errsPtr, msgVer, st8))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool lim st8 s9 ∗ stackAt s.sp dropSpeStack)
    hcro9 hL9 (drop_spe2_ver_placed_ok_at (M := M) (A := A) (lim := lim)) hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpe2VerSpec]; rw [hsp9_s]) hx0_9 (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hcro10 hL10 => ?_)
  dsimp only [dropSpe2VerSpec]; rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  refine weaken_frame_tail (Entails.of_eq (errs48_144_join errsPtr)) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstack_spe.symm) (by sep_focus) ?_
  refine weaken_frame_tail
    (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine weaken_frame_tail
    (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 (s8.readReg64 .x0) 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine weaken_frame_tail (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine weaken_frame_tail (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  refine weaken_frame_tail (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, _, hx28_cs10, _, hvregs_cs10⟩
  have hstep11 := p3_err_ver_f_placed_wp ext hdealloc st8 s10 coroPtr errsPtr recG.localIk.cap
    ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc10 hrun10 hsp10_align
    (hx19_cs10.trans hx19_9) (hx21_cs10.trans hx21_9) (hx22_cs10.trans hx22_9)
    (hx23_cs10.trans hx23_9) (by rw [hx24_cs10, hx24_9, hx24_8, hsp10_s])
    (by rw [hx25_cs10, hx25_9, hx25_8, hsp10_s]) (hx28_cs10.trans hx28_9)
  rw [hsp10_s] at hstep11
  refine bind_sepWP_cro_frame_tail hcro10 hL10 hstep11 (by sep_focus)
    fun s11 hpc11 hrun11 hcro11 hL11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, hx22_11, _, hx25_11,
    hx26_11, _, hx28_11, _, hx30_11, hvregs_11⟩
  refine weaken_frame_tail (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
        sessionHeap A.repAlloc recG st ⊢
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  refine weaken_frame_tail hpack_ss (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine weaken_frame_tail
    (words6_entails_memRegion48 (s.sp + 0x270#64)
      0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄
        ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using memRegion20_fold (s.sp + 0x250#64)
      ((s8.readReg64 .x0).extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ (s8.readReg64 .x0).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 32 32)
  refine weaken_frame_tail hfold250 (by sep_focus) ?_
  let st11 := M.stepEvents (rustDeallocEvents 192 8) st8
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructureLocal2Stack :=
    stackAt_split_bottom s.sp dropSessionStructureLocal2Stack 416 (by decide)
  refine weaken_frame_tail (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11_10]; exact hsp_align
  have hcommon := stageP3_err_tail_common_prevEmpty_placed_ok (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False) ext hdealloc hDropSS3 st11
    s0 s11 coroPtr outPtr 0x8000000000000018#64 17#64 (s8.readReg64 .x0) 17#64 w3' w4
    b_2c0 g recG st
    hcro11 hL11 hpc11 hrun11 hsp11_align
    (htr11_10.trans (htr10_9.trans (htr9_8.trans (htr8_7.trans htr7))))
    hx0_11 hx19_11 hx22_11 (by rw [hx25_11, hsp11_10])
    (hx26_11.trans (hx26_cs10.trans (hx26_9.trans hx26_8)))
    hx28_11 hx30_11
  rw [hsp11_10] at hcommon
  refine bind_sepWPp_nopanic_tail hcommon (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨⟨evs_c, hfree_c, hP_c⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP_c) ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A.repAlloc
    outPtr (s8.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  rw [show A.repAlloc.live (s8.readReg64 .x0) 17 1 = A.live (s8.readReg64 .x0) 17 1 from rfl] at hrec
  refine weaken_frame_tail hrec (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  have hpool_eq :
      A.pool lim (M.stepEvents evs_c st11) sf =
        A.pool lim
          (M.stepEvents (rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c)) st0) sf := by
    dsimp only [st11, st8]
    rw [← M.stepEvents_append, ← M.stepEvents_append]
  have htail_env : VerNeTailEnv (rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c)) :=
    verNeTailEnv_of_freeSuffix (freeOnlyEvs_append freeOnlyEvs_dealloc_192_8 hfree_c)
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨rustAllocEvents 17 1 ++ (rustDeallocEvents 192 8 ++ evs_c), htail_env, ?_⟩,
    hspf, htrf, hcc, hcrof, hLf,
    by rw [hvregs_f, hvregs_11, hvregs_cs10, hvregs_9, hvregs_cs8]⟩
  rw [← hpool_eq]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Full Stage P3 version-mismatch path (`+0x1e04 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Stage P3 version-mismatch path
(`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) over general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `FitsEnv M lim st0 StageP3VerNeM3Env`. -/
theorem stageP3_ver_ne_prevEmpty_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 StageP3VerNeM3Env)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 7684#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace) (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      Qp := by
  have hs1 := overVerNe_1e04_to_1e78_cro_placed_at_gen (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False)
    ext hLogClosure hGrow hDropSS3 st0 (fitsS1_of_fitsM3 hfits)
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hcro1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  refine bind_sepWPp_nopanic_tail hs1 (by sep_focus)
    fun s6b P_m6b hpc6b hrun6b
      ⟨⟨errsPtr, evs1, hevs1, hP6b⟩, hsp6b_s, htr6b_0, hx19_6b, _, hvregs_6b, hcro6b, hL6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  let st6b := M.stepEvents evs1 st0
  have hfits_tail : FitsEnv M lim st6b VerNeTailEnv := fitsTail_of_fitsM3 hfits hevs1
  refine weaken_frame_tail
    (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine weaken_frame_tail
    (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
  have hprev_f0 : prevSessionsEmptyAt A.repAlloc coroPtr g =
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
       vecBuf A.repAlloc 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
    unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  refine weaken_frame_tail (Entails.of_eq hprev_f0) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hstep7 := p3_err_ver_d_placed_wp A lim ext hshim st6b s6b coroPtr outPtr ctxPtr
    recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
    hpc6b hrun6b hsp6b_align hx19_6b
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
    fun s7 hpc7 hrun7 hcro7 hL7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  refine weaken_frame_tail (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
        sessionHeap A.repAlloc recG st ⊢
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  refine weaken_frame_tail hpack_ss (by sep_focus) ?_
  refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
    (by sep_focus) ?_
  have htail := stageP3_err_ver_tail_prevEmpty_placed_ok (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False) ext halloc hdealloc hDropSS3 st6b hfits_tail
    s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
    hcro7 hL7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine bind_sepWPp_nopanic_tail htail (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨⟨evs2, hevs2, hP_t⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP_t) ?_
  have hpool_eq :
      A.pool lim (M.stepEvents evs2 st6b) sf =
        A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := by
    dsimp only [st6b]
    rw [← M.stepEvents_append]
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs1 ++ evs2, stageP3VerNeM3Env_of_parts hevs1 hevs2, ?_⟩,
    hspf, htrf, hcc, hcrof, hLf, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
  unfold stageP3ErrPostPrevEmptyM3Placed
  dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget.stageP3ErrPostPrevEmptyPlaced,
    SessionState.recordError]
  rw [← hpool_eq]
  have hexists_errs :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left hexists_errs)))))
  exact Entails.of_eq (by sep_ac_rfl)

/-- Packaged statement of the budget-threaded Stage P3 version-mismatch path over general
`prevSessionsEmptyAt A.repAlloc coroPtr g` under `[LibsignalPlacement]`. -/
def StageP3VerNePrevEmptyPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (st0 : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (_hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
    FitsEnv M lim st0 StageP3VerNeM3Env →
    LibsignalCodeRoLoaded lsmpl s1.mem →
    (lsProg_518 ext).CodeLoaded s1.mem →
    s1.pc = (blkPl_518).base + 7684#64 → s1.status = .Running →
    s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
    s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
    s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      Qp

/-- Discharges `StageP3VerNePrevEmptyPlacedStmt` from allocator, shim, `growOneSpe`,
`dropSessionStructureLocal2`, and `pqxdhLogClosurePlaced` subroutine contracts. -/
theorem stageP3_ver_ne_prevEmpty_cli_placed_ok [LibsignalPlacement]
    (hshim : ∀ ext, subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (rustCliDeallocBudgetSpec M A lim))
    (hGrow : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
        (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hLogClosure : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    StageP3VerNePrevEmptyPlacedStmt := by
  intro M A lim Qp ext st0 s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer b_2c0
    g G₁ recG st hfits hcro1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  exact stageP3_ver_ne_prevEmpty_placed_ok ext (hshim ext) (halloc A lim ext) (hdealloc A lim ext)
    (hGrow A lim ext) (hDropSS3 A lim ext) (hLogClosure ext) st0 hfits
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer b_2c0 g G₁ recG st
    hcro1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` variants -/

theorem lscro_of_frozen [LibsignalPlacement] {m : Memory}
    (hfr : CryptoVerification.LibsignalFrozen lsmpl m) :
    LibsignalCodeRoLoaded lsmpl m :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.lscro_of_frozen hfr

theorem pqxdh_log_closure_frozen_placed_ok [CryptoVerification.LibsignalFullPlacement]
    (H : CryptoVerification.LibsignalHooks) :
    subroutine_ok
      ((CryptoVerification.CliHandshake.Placed.blkPC_519).rebase
        (CryptoVerification.CliHandshake.Placed.blkPl_519).base H)
      (lsmpl.base 519)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdh_log_closure_frozen_placed_ok H

theorem pqxdh_log_closure_frozen_placed_ok_of_block [CryptoVerification.LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : CryptoVerification.LibsignalHooks}
    [CryptoVerification.IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 519)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl pqxdhLogClosurePlacedSpec) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.pqxdh_log_closure_frozen_placed_ok_of_block

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalFullPlacement]` Stage P3 version-mismatch path
(`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) over general
`prevSessionsEmptyAt A.repAlloc coroPtr g`, discharging Block `519` from `LibsignalFrozen`. -/
theorem stageP3_ver_ne_prevEmpty_full_placed_ok [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st0 : M.σ) (hfits : FitsEnv M lim st0 StageP3VerNeM3Env)
    (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 7684#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace) (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      Qp := by
  have hs1 := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget.overVerNe_1e04_to_1e78_frozen_placed_at_gen (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False)
    ext hGrow hDropSS3 st0 (fitsS1_of_fitsM3 hfits)
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  refine bind_sepWPp_nopanic_tail hs1 (by sep_focus)
    fun s6b P_m6b hpc6b hrun6b
      ⟨⟨errsPtr, evs1, hevs1, hP6b⟩, hsp6b_s, htr6b_0, hx19_6b, _, hvregs_6b, hcro6b, hL6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  let st6b := M.stepEvents evs1 st0
  have hfits_tail : FitsEnv M lim st6b VerNeTailEnv := fitsTail_of_fitsM3 hfits hevs1
  refine weaken_frame_tail
    (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine weaken_frame_tail
    (T := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (T' := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlog_eq : pqLogLevelCellPlaced = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine weaken_frame_tail (Entails.of_eq hlog_eq) (by sep_focus) ?_
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hsp6b_s]; exact hsp_align
  have hprev_f0 : prevSessionsEmptyAt A.repAlloc coroPtr g =
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
       vecBuf A.repAlloc 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []) := by
    unfold prevSessionsEmptyAt vecAt vecHeader; dsimp only [List.length_nil]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  refine weaken_frame_tail (Entails.of_eq hprev_f0) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hstep7 := p3_err_ver_d_placed_wp A lim ext hshim st6b s6b coroPtr outPtr ctxPtr
    recG.localIk.cap 0x8000000000000006#64 (cap_ne_noneCap_of_lt hcap_lt)
    hpc6b hrun6b hsp6b_align hx19_6b
  rw [hsp6b_s] at hstep7
  refine bind_sepWP_cro_frame_tail hcro6b hL6b hstep7 (by sep_focus)
    fun s7 hpc7 hrun7 hcro7 hL7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6b, htr7_6b, hx0_7, hx1_7, hx19_7, hx24_7, hx25_7, hx26_7, _, _, hvregs_7⟩
  refine weaken_frame_tail (Entails.of_eq hprev_f0.symm) (by sep_focus) ?_
  refine weaken_frame_tail (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
        sessionHeap A.repAlloc recG st ⊢
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG st hinl
  refine weaken_frame_tail hpack_ss (by sep_focus) ?_
  refine weaken_frame_tail (sp3e0_cell_336_entails_344 s.sp 0xffffffffffffffff#64)
    (by sep_focus) ?_
  have htail := stageP3_err_ver_tail_prevEmpty_placed_ok (M := M) (A := A) (lim := lim)
    (Qp := fun _ _ => False) ext halloc hdealloc hDropSS3 st6b hfits_tail
    s0 s s7 coroPtr outPtr errsPtr msgVer b_2c0 g recG st
    hcro7 hL7 hpc7 hrun7 hsp7_6b hsp_align (htr7_6b.trans htr6b_0)
    hx0_7 hx1_7 hx19_7 hx24_7 hx25_7 hx26_7
  refine bind_sepWPp_nopanic_tail htail (by sep_focus)
    fun sf P_mf hpcf hrunf ⟨⟨evs2, hevs2, hP_t⟩, hspf, htrf, hcc, hcrof, hLf, hvregs_f⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP_t) ?_
  have hpool_eq :
      A.pool lim (M.stepEvents evs2 st6b) sf =
        A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf := by
    dsimp only [st6b]
    rw [← M.stepEvents_append]
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨evs1 ++ evs2, stageP3VerNeM3Env_of_parts hevs1 hevs2, ?_⟩,
    hspf, htrf, hcc, hcrof, hLf, by rw [hvregs_f, hvregs_7, hvregs_6b]⟩
  unfold stageP3ErrPostPrevEmptyM3Placed
  dsimp only [LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget.stageP3ErrPostPrevEmptyPlaced,
    SessionState.recordError]
  rw [← hpool_eq]
  have hexists_errs :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 1#64 (Entails.refl _)))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left hexists_errs)))))
  exact Entails.of_eq (by sep_ac_rfl)

/-- Packaged statement of the budget-threaded `[LibsignalFullPlacement]` Stage P3
version-mismatch path over general `prevSessionsEmptyAt A.repAlloc coroPtr g`. -/
def StageP3VerNePrevEmptyFullPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (st0 : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64)
    (_hinit_ne : initErrsPtr ≠ 0#64) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
    FitsEnv M lim st0 StageP3VerNeM3Env →
    CryptoVerification.LibsignalFrozen lsmpl s1.mem →
    (lsProg_518 ext).CodeLoaded s1.mem →
    s1.pc = (blkPl_518).base + 7684#64 → s1.status = .Running →
    s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
    s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
    s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ pqLogLevelCellPlaced ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool lim st0 s1 ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP3VerNeM3Env evs ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs st0) s0 s sf coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed))) ∧
        sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
      Qp

/-- Discharges `StageP3VerNePrevEmptyFullPlacedStmt` from allocator, shim, `growOneSpe`,
`dropSessionStructureLocal2`, and `LibsignalFrozen` Block-`519` contracts. -/
theorem stageP3_ver_ne_prevEmpty_cli_full_placed_ok [CryptoVerification.LibsignalFullPlacement]
    (hshim : ∀ ext, subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec)
    (halloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
        (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext)
        (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (rustCliDeallocBudgetSpec M A lim))
    (hGrow : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
        (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hDropSS3 : ∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))) :
    StageP3VerNePrevEmptyFullPlacedStmt := by
  intro M A lim Qp ext st0 s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer b_2c0
    g G₁ recG st hfits hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
  exact stageP3_ver_ne_prevEmpty_full_placed_ok ext (hshim ext) (halloc A lim ext) (hdealloc A lim ext)
    (hGrow A lim ext) (hDropSS3 A lim ext) st0 hfits
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer b_2c0 g G₁ recG st
    hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevVerNePlacedBudget
