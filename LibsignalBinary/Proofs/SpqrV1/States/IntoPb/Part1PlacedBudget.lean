/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Part 1 Placed: Arm 0 (`keysUnsampled`) & Call Helpers

Relocatable (`[LibsignalPlacement]`) `RustCliAllocBudget M` proofs for Arm 0 (`States.keysUnsampled`,
`evs = []`), `SepWPp` exit bridges, and budget callee call helpers for `<PolyEncoder>::into_pb`
(Block `375`) and `<PolyDecoder>::into_pb` (Block `377`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded
   libsignalSessionCode lsmpl subroutine_ok_withLsCodeLoaded_of_plain
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysUnsampled)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderAt protoPolynomialDecoderSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap chunkedKeysUnsampled_expose
   epilogueStagingCells outWords28 outWords28_entails_keysUnsampled
   protoPolynomialDecoderHeap protoPolynomialDecoder_expose
   protoPolynomialEncoderHeap protoPolynomialEncoder_expose
   sp_sub_480_add_200 sp_sub_96_sub_168 sp_sub_96_sub_176
   sp_sub_96_sub_192 sp_sub_96_sub_208 stA_words8_and_864_entails_928
   stackAt_encoderIntoPb_eq_decoderIntoPb statesIntoPbJumpTableBytes
   statesIntoPbJumpTablePlacedAt statesIntoPbSavedCells statesIntoPbStack
   statesIntoPb_seq_sepWP statesIntoPb_seq_sepWP_cl)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (SpqrBoundedEvs sepWPp_of_states_into_pb_exit_cl_placed
   sepWPp_of_states_into_pb_exit_placed statesIntoPbVariantPlacedSpec
   statesIntoPbVariantPlacedSpecOfEnv states_into_pb_epilogue_placed
   states_into_pb_prologue_60_placed states_into_pb_prologue_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (KeysUnsampledEnv StatesIntoPbNoPanic)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168
  sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## 1. Re-Exports -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (SpqrBoundedEvs statesIntoPbVariantPlacedSpecOfEnv statesIntoPbVariantPlacedSpec
   states_into_pb_prologue_placed states_into_pb_prologue_60_placed
   states_into_pb_epilogue_placed sepWPp_of_states_into_pb_exit_placed
   sepWPp_of_states_into_pb_exit_cl_placed)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (KeysUnsampledEnv StatesIntoPbNoPanic)

export CryptoVerification.SpqrV1.States.IntoPb (statesIntoPb_seq_sepWP_cl)

abbrev statesIntoPb_seq_sepWP_placed := @statesIntoPb_seq_sepWP

/-! ## 2. Arm 0 (`States.keysUnsampled`, `+0 -> +60 -> +100 -> +1544 -> ret`, `evs = []`) -/

theorem states_into_pb_keysUnsampled_arm_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s1 : State) (out stA : BitVec 64)
    (s : KeysUnsampled (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_334).base + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 2#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1512#64) 1416 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A.repAlloc out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTablePlacedAt ∗
          A.pool lim st sf ∗ stackAt s0.sp statesIntoPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 880) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 176) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have h60_100 : ∀ Rest : SepProp,
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
        ((blkPl_334).base + 100#64) s1
        (statesIntoPbJumpTablePlacedAt ∗ Rest)
        (fun s1b P1b =>
          VmPreserved s1 s1b ∧
          (P1b ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest) ∧
          (s1b.sp = s0.sp - 1520#64 ∧
           s1b.readReg64 .x29 = s0.sp - 96#64 ∧
           s1b.readReg64 .x28 = s0.sp - 256#64 ∧
           s1b.readReg64 .x27 = s0.sp - 1360#64 ∧
           s1b.readReg64 .x26 = s0.sp - 480#64 ∧
           s1b.readReg64 .x20 = stA ∧
           s1b.readReg64 .x19 = out ∧
           TraceCalleeSaved s1b s0)) := by
    intro Rest
    dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    wp_steps
    wp_done
  have hstep1 : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) s1
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
       ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
       ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
       ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
       ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
       ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
       ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
       ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
       ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
       ((s0.sp - 1368#64) ↦₆₄ w184) ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       ((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
       ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
       ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5) ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 2#64) ∗
       ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 64#64) 864 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            a0 a1 a2 a3 a4 a5
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          A.pool lim st s2 ∗
          (authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           ((stA ↦₆₄ 2#64) ∗
            ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
            ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
            ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
            ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
            memRegion (stA + 64#64) 864) ∗
           statesIntoPbJumpTablePlacedAt)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x8000000000000000#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         TraceCalleeSaved s2 s0)) := by
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq (h60_100
        (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
         ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
         ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
         ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
         ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
         ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
         ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
         ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
         ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
         ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
         ((s0.sp - 1368#64) ↦₆₄ w184) ∗
         memRegion (s0.sp - 1360#64) 880 ∗
         memRegion (s0.sp - 480#64) 176 ∗
         ((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
         ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
         ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5) ∗
         memRegion (s0.sp - 256#64) 160 ∗
         statesIntoPbSavedCells s0 ∗
         (stA ↦₆₄ 2#64) ∗
         ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 64#64) 864 ∗
         memRegion out optProtoInnerStateSize ∗
         A.pool lim st s1))
      fun s1b P1b hpc1b hrun1b
        ⟨hvm1b, hP1b, hsp1b, hx29_1b, hx28_1b, hx27_1b, hx26_1b, hx20_1b, hx19_1b, htr1b, hvregs1b⟩ => ?_)
    refine SepWP.weaken_pre hP1b ?_
    have h100_1544 : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
        ((blkPl_334).base + 1544#64) s1b
        (statesIntoPbJumpTablePlacedAt ∗
         stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
         ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
         ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
         ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
         ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
         ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
         ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
         ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
         ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
         ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
         ((s0.sp - 1368#64) ↦₆₄ w184) ∗
         memRegion (s0.sp - 1360#64) 880 ∗
         memRegion (s0.sp - 480#64) 176 ∗
         ((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
         ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
         ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5) ∗
         memRegion (s0.sp - 256#64) 160 ∗
         statesIntoPbSavedCells s0 ∗
         (stA ↦₆₄ 2#64) ∗
         ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 64#64) 864 ∗
         memRegion out optProtoInnerStateSize ∗
         A.pool lim st s1)
        (fun s2 P2 =>
          VmPreserved s1b s2 ∧
          (P2 ⊢
            stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
            epilogueStagingCells s0.sp
              a0 a1 a2 a3 a4 a5
              w64 w72 w80 w88 w96 w104 w112 w120
              w128 w136 w144 w152 w160 w168 w176 w184
              0#64 w200 w208 w216 ∗
            memRegion (s0.sp - 1360#64) 880 ∗
            memRegion (s0.sp - 480#64) 176 ∗
            memRegion (s0.sp - 256#64) 160 ∗
            statesIntoPbSavedCells s0 ∗
            memRegion out optProtoInnerStateSize ∗
            A.pool lim st s1 ∗
            (authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
             ((stA ↦₆₄ 2#64) ∗
              ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
              ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
              ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
              ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
              memRegion (stA + 64#64) 864) ∗
             statesIntoPbJumpTablePlacedAt)) ∧
          (s2.sp = s0.sp - 1520#64 ∧
           s2.readReg64 .x29 = s0.sp - 96#64 ∧
           s2.readReg64 .x19 = out ∧
           s2.readReg64 .x22 = 0x8000000000000000#64 ∧
           s2.readReg64 .x21 = s.uc.epoch ∧
           TraceCalleeSaved s2 s0)) := by
      dsimp only [epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpc1b ⊢
      by_vm_steps (
        wp_steps
        refine align_entails_vm (s0 := s1b) ?_ ?_
        · exact Entails.of_eq (by sep_ac_rfl)
        · wp_done)
    exact SepWP.mono h100_1544 fun s2 _P2 _ _ ⟨hvm2, hP2, hregs⟩ =>
      ⟨by rw [A.pool_of_vmPreserved (hvm1b.trans hvm2)]; exact hP2, hregs⟩
  refine seq_clean_wp hstep1 fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  have hep := states_into_pb_epilogue_placed (ext := ext) A lim st s0 s2 out
    a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     ((stA ↦₆₄ 2#64) ∗
      ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (stA + 64#64) 864) ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf, _⟩ => ⟨?_, hspf, hcsf, htrf⟩
  refine Entails.trans hPf ?_
  have hout := outWords28_entails_keysUnsampled A.repAlloc out a0 a1 a2 a3 a4 a5
    w64 w72 w80 w88 w96 w104 w112 w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216 s
  have hstA := stA_words8_and_864_entails_928 stA 2#64 a0 a1 a2 a3 a4 a5 s.uc.epoch
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000000#64
      a0 a1 a2 a3 a4 a5
      s.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w120
      w128 w136 w144 w152 w160 w168 w176 w184
      0#64 w200 w208 w216 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    ((stA ↦₆₄ 2#64) ∗
     ((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     memRegion (stA + 64#64) 864) ∗
    statesIntoPbJumpTablePlacedAt ∗ A.pool lim st sf ∗ stackAt s0.sp statesIntoPbStack by sep_ac_rfl)) ?_
  exact sepConj_mono hout (sepConj_mono_left hstA)

/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` (Block `334`) on Arm 0
    (`States.keysUnsampled`), valid for any `Env` containing `[]`. -/
theorem states_into_pb_keysUnsampled_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (s : KeysUnsampled (spqrAuthApi F))
    (hEnv : Env []) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysUnsampled s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, _hfit⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.keysUnsampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA (.keysUnsampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedKeysUnsampled_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 2#64
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 64#64) 864 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre ?_ (seq_clean_wp hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  · exact Entails.of_eq (by dsimp only [authenticatorHeap]; sep_ac_rfl)
  · have harm := states_into_pb_keysUnsampled_arm_placed (A := A) (lim := lim) (ext := ext)
      st s0 s1 out stA s a0 a1 a2 a3 a4 a5
      hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    refine SepWP.weaken_pre ?_ (SepWP.mono harm fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨⟨[], hEnv, hPf⟩, hspf, hcsf, htrf⟩)
    exact Entails.of_eq (by dsimp only [authenticatorHeap]; sep_ac_rfl)

/-- Tight `KeysUnsampledEnv` (`evs = []`) `subroutine_ok` for Arm 0 (`States.keysUnsampled`). -/
theorem states_into_pb_keysUnsampled_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysUnsampled s) KeysUnsampledEnv) :=
  states_into_pb_keysUnsampled_of_env_placed s rfl

/-- Default `statesIntoPbVariantPlacedSpec` `subroutine_ok` for Arm 0 (`States.keysUnsampled`). -/
theorem states_into_pb_keysUnsampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F (.keysUnsampled s)) :=
  states_into_pb_keysUnsampled_of_env_placed s (SpqrBoundedEvs.nil 64 _)

theorem states_into_pb_keysUnsampled_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (s : KeysUnsampled (spqrAuthApi F))
    (hEnv : Env []) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysUnsampled s) Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (states_into_pb_keysUnsampled_of_env_placed s hEnv)

theorem states_into_pb_keysUnsampled_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysUnsampled s) KeysUnsampledEnv)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (states_into_pb_keysUnsampled_env_placed s)

theorem states_into_pb_keysUnsampled_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (.keysUnsampled s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain (states_into_pb_keysUnsampled_placed s)

/-! ## 3. Shared Relocatable `SepWPp` Postconditions and Exit Bridges -/

/-- Envelope-parametric return postcondition of relocatable `<States>::into_pb` (Block `334`)
    for `SepWPp`. -/
def StatesIntoPbPlacedPostOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {F : ShaCompress}
    (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent, Env evs ∧
      (Pf ⊢
        optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
        memRegion stA chunkedStatesSize ∗
        statesIntoPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

/-- Default-envelope return postcondition of relocatable `<States>::into_pb` (Block `334`)
    for `SepWPp`. -/
abbrev StatesIntoPbPlacedPost [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {F : ShaCompress}
    (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  StatesIntoPbPlacedPostOfEnv A lim st s0 out stA stateVal
    (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024))

abbrev StatesIntoPbPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {F : ShaCompress}
    (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  StatesIntoPbPlacedPost A lim st s0 out stA stateVal

/-- Bridge from `SepWPp` with `StatesIntoPbPlacedPostOfEnv` / `StatesIntoPbNoPanic` to the
    `subroutine_ok_of_sepWPp` goal for `statesIntoPbVariantPlacedSpecOfEnv`. -/
theorem sepWPp_of_states_into_pb_wpp_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (hwpp : SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (StatesIntoPbPlacedPostOfEnv A lim st s0 out stA stateVal Env)
      (StatesIntoPbNoPanic R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, henv, hent⟩, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    dsimp only [statesIntoPbVariantPlacedSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by sep_ac_rfl))) hmR⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR
    exact hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_states_into_pb_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (hwpp : SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (StatesIntoPbPlacedPost A lim st s0 out stA stateVal)
      (StatesIntoPbNoPanic R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpec M A lim F stateVal).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpec M A lim F stateVal).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_wpp_of_env_placed st s0 s out stA stateVal _ P R hwpp

theorem sepWPp_of_states_into_pb_wpp_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (hwpp : SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (StatesIntoPbPlacedPostOfEnv A lim st s0 out stA stateVal Env)
      (StatesIntoPbNoPanic R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env)).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env)).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_wpp_of_env_placed st s0 s out stA stateVal Env P R hwpp

theorem sepWPp_of_states_into_pb_wpp_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (hwpp : SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (StatesIntoPbPlacedPost A lim st s0 out stA stateVal)
      (StatesIntoPbNoPanic R)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F stateVal)).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F stateVal)).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_wpp_placed st s0 s out stA stateVal P R hwpp

/-! ## 4. Relocatable Budget Callee Call Helpers (`encoderIntoPb` at `lsmpl.base 375`, `decoderIntoPb` at `lsmpl.base 377`) -/

/-- Total-correctness (`SepWP`) call helper for budget `<PolyEncoder>::into_pb` (`lsmpl.base 375`),
    threading `M.stepEvents evs st`, `AllocCallPreserved`, and `EncoderIntoPbEnv enc evs`, and
    exposing `e0..e6` + `protoPolynomialEncoderHeap`. -/
theorem call_encoderIntoPb_expose_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (encoderIntoPbSpec M A lim))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hfit : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc encA enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      EncoderIntoPbEnv enc evs →
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc s P post := by
  refine SepWP.call_subroutine_frame henc_raw (x := (⟨outEncA, encA, enc⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [encoderIntoPbSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [encoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [encoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [encoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ EncoderIntoPbEnv enc evs⌝ ∗
      ((protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
        memRegion encA polyEncoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
          Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialEncoder_expose A.repAlloc outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 (Entails.of_eq (by sep_ac_rfl))))))))
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e1 =>
      SepWP.exists_elim fun e2 => SepWP.exists_elim fun e3 =>
      SepWP.exists_elim fun e4 => SepWP.exists_elim fun e5 =>
      SepWP.exists_elim fun e6 => ?_
    exact hnext sm evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm (hspm.trans hsp) hcsm hacp
      ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ henv
  · intro _ _ _ ho
    dsimp only [encoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-- Call budget `<PolyEncoder>::into_pb` (`lsmpl.base 375`) inside `SepWPp`, parametric in
    `{Q Qp : State → SepProp → Prop}`. -/
theorem call_encoderIntoPb_expose_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (encoderIntoPbSpec M A lim))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hfit : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc encA enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      EncoderIntoPbEnv enc evs →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  refine call_encoderIntoPb_expose_wp_placed henc_raw st outEncA encA enc
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hfit hsplit ?_
  intro sf evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspf hcsm hacp htrf henv
  exact SepWP.done hpcm hrunm fun _ =>
    hnext sf evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspf hcsm hacp htrf henv

/-- `withLsCodeLoaded` call helper for budget `<PolyEncoder>::into_pb` (`lsmpl.base 375`),
    threading `LibsignalCodeLoaded lsmpl sf.mem` to `hnext` and parametric in `{Q Qp}`. -/
theorem call_encoderIntoPb_expose_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375)
      (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 375)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hfit : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc encA enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      EncoderIntoPbEnv enc evs →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc)
    (Φ := fun sm => LibsignalCodeLoaded lsmpl sm)
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame henc_cl (x := (⟨outEncA, encA, enc⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp]
    refine Satisfies.mono
      (P := ⌜s.readReg64 .x0 = outEncA ∧ s.readReg64 .x1 = encA ∧
          FitsEnv M lim st (EncoderIntoPbAllocEnv enc)⌝ ∗
        (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
          (((memRegion outEncA protoPolynomialEncoderSize ∗
              polyEncoderAt A.repAlloc encA enc ∗
              A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) ∗ R')))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ EncoderIntoPbEnv enc evs⌝ ∗
      ((protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
        memRegion encA polyEncoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       Frame) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
          Frame ⊢
        ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
          (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
            ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
            ((outEncA + 48#64) ↦₆₄ e6) ∗
            protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
            memRegion encA polyEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialEncoder_expose A.repAlloc outEncA enc.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro e0
      apply Entails.sepExists_elim; intro e1
      apply Entails.sepExists_elim; intro e2
      apply Entails.sepExists_elim; intro e3
      apply Entails.sepExists_elim; intro e4
      apply Entails.sepExists_elim; intro e5
      apply Entails.sepExists_elim; intro e6
      refine Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 (Entails.of_eq (by sep_ac_rfl))))))))
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e1 =>
      SepWP.exists_elim fun e2 => SepWP.exists_elim fun e3 =>
      SepWP.exists_elim fun e4 => SepWP.exists_elim fun e5 =>
      SepWP.exists_elim fun e6 => ?_
    exact SepWP.done hpcm hrunm fun hcl_sm =>
      hnext sm evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm (hspm.trans hsp) hcsm hacp
        ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sm henv
  · intro _ _ _ ho
    dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-- Total-correctness (`SepWP`) call helper for budget `<PolyDecoder>::into_pb` (`lsmpl.base 377`),
    splitting/restoring `stackAt (s0.sp - 1520#64) encoderIntoPbStack`, threading
    `M.stepEvents evs st`, `AllocCallPreserved`, and `DecoderIntoPbEnv dec evs`, and exposing
    `d0..d4` + `protoPolynomialDecoderHeap`. -/
theorem call_decoderIntoPb_expose_wp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (decoderIntoPbSpec M A lim))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hfit : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      DecoderIntoPbEnv dec evs →
      SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) target_pc s P post := by
  refine SepWP.call_subroutine_frame hdec_raw (x := (⟨outDecA, decA, dec⟩, st))
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [decoderIntoPbSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [decoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [decoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [decoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ DecoderIntoPbEnv dec evs⌝ ∗
      ((protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
        memRegion decA polyDecoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
       (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialDecoder_expose A.repAlloc outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
      SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
      SepWP.exists_elim fun d4 => ?_
    exact hnext sm evs d0 d1 d2 d3 d4 hpcm hrunm (hspm.trans hsp) hcsm hacp
      ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ henv
  · intro _ _ _ ho
    dsimp only [decoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

/-- Call budget `<PolyDecoder>::into_pb` (`lsmpl.base 377`) inside `SepWPp`, parametric in
    `{Q Qp : State → SepProp → Prop}`. -/
theorem call_decoderIntoPb_expose_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (decoderIntoPbSpec M A lim))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hfit : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      DecoderIntoPbEnv dec evs →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  refine call_decoderIntoPb_expose_wp_placed hdec_raw st outDecA decA dec
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hfit hsplit ?_
  intro sf evs d0 d1 d2 d3 d4 hpcm hrunm hspf hcsm hacp htrf henv
  exact SepWP.done hpcm hrunm fun _ =>
    hnext sf evs d0 d1 d2 d3 d4 hpcm hrunm hspf hcsm hacp htrf henv

/-- `withLsCodeLoaded` call helper for budget `<PolyDecoder>::into_pb` (`lsmpl.base 377`),
    splitting/restoring `stackAt (s0.sp - 1520#64) encoderIntoPbStack`, threading
    `LibsignalCodeLoaded lsmpl sf.mem` to `hnext`, and parametric in `{Q Qp}`. -/
theorem call_decoderIntoPb_expose_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 377)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hfit : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      AllocCallPreserved s sf →
      TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      DecoderIntoPbEnv dec evs →
      SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc)
    (Φ := fun sm => LibsignalCodeLoaded lsmpl sm)
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl ?_
  refine SepWP.call_subroutine_frame hdec_cl (x := (⟨outDecA, decA, dec⟩, st))
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit, stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)] at hm
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp]
    refine Satisfies.mono
      (P := ⌜s.readReg64 .x0 = outDecA ∧ s.readReg64 .x1 = decA ∧
          FitsEnv M lim st (DecoderIntoPbAllocEnv dec)⌝ ∗
        (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
          (((memRegion outDecA protoPolynomialDecoderSize ∗
              polyDecoderAt A.repAlloc decA dec ∗
              A.pool lim st s ∗
              (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗
                stackAt (s0.sp - 1520#64) decoderIntoPbStack)) ∗ Frame) ∗ R')))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hpan
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at hpan
    exact not_satisfies_false_sepConj hpan
  · intro _ _ _ _ hex
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at hex
    exact not_satisfies_false_sepConj hex
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec]
    rw [hsp, sepExists_sepConj_left]
    refine SepWP.exists_elim fun evs => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜sm.trace = s.trace ∧ AllocCallPreserved s sm ∧ DecoderIntoPbEnv dec evs⌝ ∗
      ((protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
        memRegion decA polyDecoderSize ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
       (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)) by sep_ac_rfl)) ?_
    refine SepWP.pure_elim fun ⟨htrm, hacp, henv⟩ => ?_
    have hexp :
        (protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame) ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
          (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
            ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
            protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
            memRegion decA polyDecoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
           Frame) := by
      refine Entails.trans (sepConj_mono_left (sepConj_mono_left
        (protoPolynomialDecoder_expose A.repAlloc outDecA dec.intoPb))) ?_
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d0
      apply Entails.sepExists_elim; intro d1
      apply Entails.sepExists_elim; intro d2
      apply Entails.sepExists_elim; intro d3
      apply Entails.sepExists_elim; intro d4
      refine Entails.sepExists_right d0 (Entails.sepExists_right d1
        (Entails.sepExists_right d2 (Entails.sepExists_right d3
          (Entails.sepExists_right d4 ?_))))
      rw [stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hexp ?_
    refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
      SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
      SepWP.exists_elim fun d4 => ?_
    exact SepWP.done hpcm hrunm fun hcl_sm =>
      hnext sm evs d0 d1 d2 d3 d4 hpcm hrunm (hspm.trans hsp) hcsm hacp
        ⟨htrm.trans htrace.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sm henv
  · intro _ _ _ ho
    dsimp only [withLsCodeLoaded, decoderIntoPbSpec] at ho
    exact (not_satisfies_false_sepConj ho).elim

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
