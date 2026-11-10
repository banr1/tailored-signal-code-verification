/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Placed
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 4d Placed: Arm 2 (`States.headerSent`)

Relocatable `[LibsignalPlacement]` verification of Arm 2 (`States.headerSent`, tag `4`)
on Block `334` under `RustCliAllocBudget M` and `HeaderSentEnv`, in plain and
`withLsCodeLoaded` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (HeaderSent)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedHeaderSent_expose epilogueStagingCells outWords28
   outWords28_entails_headerSent protoPolynomialDecoderHeap
   protoPolynomialEncoderHeap stA_headerSent_entails_928
   stack_1416_split_headerSent statesIntoPbJumpTableBytes
   statesIntoPbJumpTablePlacedAt statesIntoPbSavedCells statesIntoPbStack
   vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv decoderIntoPbSpec
   fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv encoderIntoPbSpec
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_placed statesIntoPbVariantPlacedSpecOfEnv
   states_into_pb_epilogue_placed states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
  (call_decoderIntoPb_expose_cl_placed call_encoderIntoPb_expose_cl_placed
   sepWPp_of_states_into_pb_wpp_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (call_decoderIntoPb_expose_wp_placed call_encoderIntoPb_expose_wp_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
  (call_memcpy_keep_relocate_cl_placed call_memcpy_keep_relocate_wp_placed
   statesIntoPb_seq_sepWP_cl_vm)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dBudget
  (HeaderSentEnv headerSentEnv_of_parts)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
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

/-! ## 1. Envelope & Relocatable Spec for Arm 2 (`States.headerSent`) -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dBudget
  (HeaderSentEnv headerSentEnv_of_parts)

abbrev statesIntoPbHeaderSentPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F (.headerSent s) (HeaderSentEnv s)

/-! ## 2. Step Lemmas for Arm 2 (`States.headerSent`, tag `4`) -/

/-- Step 1 of Arm 2 (`+60 -> +96 -> +472 -> +496 -> lsρ "memcpy"`) with `VmPreserved` pool transport. -/
theorem states_into_pb_headerSent_pre1_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
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
    (hx8 : s1.readReg64 .x8 = 4#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s1
      (statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s2 ∗ Rest) ∧ s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (blkPl_334).base + 500#64 ∧ s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧ (s2.readReg64 .x2).toNat = 880 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧ s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧ s2.readReg64 .x22 = 0x8000000000000002#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧ s2.readReg64 .x20 = stA ∧ s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0 ∧ VmPreserved s1 s2) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  let Rest' : SepProp := A.pool lim st s1 ∗ Rest
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s1
      (statesIntoPbJumpTablePlacedAt ∗ Rest')
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧ (P2 ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest') ∧
        (s2.sp = s0.sp - 1520#64 ∧ s2.readReg64 .x30 = (blkPl_334).base + 500#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧ s2.readReg64 .x1 = stA + 8#64 ∧
         (s2.readReg64 .x2).toNat = 880 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x28 = s0.sp - 256#64 ∧ s2.readReg64 .x26 = s0.sp - 480#64 ∧
         s2.readReg64 .x22 = 0x8000000000000002#64 ∧ s2.readReg64 .x21 = s0.sp - 1360#64 ∧
         s2.readReg64 .x20 = stA ∧ s2.readReg64 .x19 = out ∧ TraceCalleeSaved s2 s0)) := by
    dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    wp_steps
    wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun s2 P2 _ _
    ⟨hvm2, hP2, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx22_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_
  refine ⟨?_, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx22_2, hx21_2, hx20_2, hx19_2, htr2, hvm2⟩
  rw [A.pool_of_vmPreserved hvm2]
  exact hP2

/-- Step 2 of Arm 2 (`+500 -> +588 -> lsmpl.base 375`) with `VmPreserved` pool transport. -/
theorem states_into_pb_headerSent_pre2_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (blkPl_334).base + 500#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx22 : s2.readReg64 .x22 = 0x8000000000000002#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr2 : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s2
      (cells (s0.sp - 256#64) 9 ∗ cells (s0.sp - 160#64) 6 ∗ ((s0.sp - 888#64) ↦₆₄ epoch) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
       A.pool lim st s2 ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
           ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
           ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗ ((s0.sp - 888#64) ↦₆₄ epoch) ∗
          (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
          A.pool lim st s3 ∗ Rest) ∧ s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (blkPl_334).base + 592#64 ∧ s3.readReg64 .x0 = s0.sp - 400#64 ∧
        s3.readReg64 .x1 = stA + 8#64 ∧ s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧ s3.readReg64 .x24 = s0.sp - 480#64 ∧
        s3.readReg64 .x23 = epoch ∧ s3.readReg64 .x22 = 0x8000000000000002#64 ∧
        s3.readReg64 .x21 = s0.sp - 1360#64 ∧ s3.readReg64 .x19 = out ∧ TraceCalleeSaved s3 s0 ∧
        VmPreserved s2 s3) := by
  rcases htr2 with ⟨htr2, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hrejoin48 :
      ((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
      ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
      ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5) ⊢
      memRegion (s0.sp - 160#64) 48 := by
    rw [ProofLib.memRegion_cells (s0.sp - 160#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  cells_unfold
  wp_pull_exists
  rename_i q0 q1 q2 q3 q4 q5 m0 m1 m2 m3 m4 m5 m6 m7 m8
  let Rest' : SepProp := A.pool lim st s2 ∗ Rest
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s2
      ((((s0.sp - 256#64) ↦₆₄ m0) ∗ ((s0.sp - 248#64) ↦₆₄ m1) ∗
        ((s0.sp - 240#64) ↦₆₄ m2) ∗ ((s0.sp - 232#64) ↦₆₄ m3) ∗
        ((s0.sp - 224#64) ↦₆₄ m4) ∗ ((s0.sp - 216#64) ↦₆₄ m5) ∗
        ((s0.sp - 208#64) ↦₆₄ m6) ∗ ((s0.sp - 200#64) ↦₆₄ m7) ∗ ((s0.sp - 192#64) ↦₆₄ m8)) ∗
       (((s0.sp - 160#64) ↦₆₄ q0) ∗ ((s0.sp - 152#64) ↦₆₄ q1) ∗
        ((s0.sp - 144#64) ↦₆₄ q2) ∗ ((s0.sp - 136#64) ↦₆₄ q3) ∗
        ((s0.sp - 128#64) ↦₆₄ q4) ∗ ((s0.sp - 120#64) ↦₆₄ q5)) ∗ ((s0.sp - 888#64) ↦₆₄ epoch) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗ Rest')
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧ (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
           ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
           ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗ ((s0.sp - 888#64) ↦₆₄ epoch) ∗
          (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗ Rest') ∧
        (s3.sp = s0.sp - 1520#64 ∧ s3.readReg64 .x30 = (blkPl_334).base + 592#64 ∧
         s3.readReg64 .x0 = s0.sp - 400#64 ∧ s3.readReg64 .x1 = stA + 8#64 ∧
         s3.readReg64 .x29 = s0.sp - 96#64 ∧ s3.readReg64 .x26 = s0.sp - 480#64 ∧
         s3.readReg64 .x24 = s0.sp - 480#64 ∧ s3.readReg64 .x23 = epoch ∧
         s3.readReg64 .x22 = 0x8000000000000002#64 ∧ s3.readReg64 .x21 = s0.sp - 1360#64 ∧
         s3.readReg64 .x19 = out ∧ TraceCalleeSaved s3 s0)) := by
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := s2)
        (Entails.trans (Entails.of_eq (show _ =
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
           ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
           ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
          (((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
           ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
           ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5)) ∗ ((s0.sp - 888#64) ↦₆₄ epoch) ∗
          (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
           ((stA + 472#64) ↦₆₄ k2)) ∗ Rest' by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_left hrejoin48))) ?_
      wp_done)
  dsimp only [Rest'] at hwp
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono hwp fun s3 P3 _ _
      ⟨hvm3, hP3, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx24_3, hx23_3, hx22_3, hx21_3, hx19_3, htr3⟩ => ?_)
  refine ⟨?_, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx24_3, hx23_3, hx22_3, hx21_3, hx19_3, htr3, hvm3⟩
  rw [A.pool_of_vmPreserved hvm3]
  exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))

/-- Step 3 of Arm 2 (`+592 -> +600 -> lsmpl.base 377`) with `VmPreserved` pool transport. -/
theorem states_into_pb_headerSent_pre3_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s4 : State) (out epoch : BitVec 64)
    (hpc4 : s4.pc = (blkPl_334).base + 592#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 1520#64)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s4.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s4.readReg64 .x24 = s0.sp - 480#64)
    (hx23 : s4.readReg64 .x23 = epoch)
    (hx22 : s4.readReg64 .x22 = 0x8000000000000002#64)
    (hx21 : s4.readReg64 .x21 = s0.sp - 1360#64)
    (hx19 : s4.readReg64 .x19 = out)
    (htr4 : TraceCalleeSaved s4 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s4
      (A.pool lim st s4 ∗ Rest)
      (fun s5 P5 =>
        (P5 ⊢ A.pool lim st s5 ∗ Rest) ∧ s5.sp = s0.sp - 1520#64 ∧
        s5.readReg64 .x30 = (blkPl_334).base + 604#64 ∧ s5.readReg64 .x0 = s0.sp - 344#64 ∧
        s5.readReg64 .x1 = s0.sp - 880#64 ∧ s5.readReg64 .x29 = s0.sp - 96#64 ∧
        s5.readReg64 .x26 = s0.sp - 480#64 ∧ s5.readReg64 .x23 = epoch ∧
        s5.readReg64 .x22 = 0x8000000000000002#64 ∧ s5.readReg64 .x19 = out ∧
        TraceCalleeSaved s5 s0 ∧ VmPreserved s4 s5) := by
  rcases htr4 with ⟨htr4, hvregs⟩
  let Rest' : SepProp := A.pool lim st s4 ∗ Rest
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s4
      Rest'
      (fun s5 P5 =>
        VmPreserved s4 s5 ∧ (P5 ⊢ Rest') ∧ (s5.sp = s0.sp - 1520#64 ∧
         s5.readReg64 .x30 = (blkPl_334).base + 604#64 ∧ s5.readReg64 .x0 = s0.sp - 344#64 ∧
         s5.readReg64 .x1 = s0.sp - 880#64 ∧ s5.readReg64 .x29 = s0.sp - 96#64 ∧
         s5.readReg64 .x26 = s0.sp - 480#64 ∧ s5.readReg64 .x23 = epoch ∧
         s5.readReg64 .x22 = 0x8000000000000002#64 ∧ s5.readReg64 .x19 = out ∧
         TraceCalleeSaved s5 s0)) := by
    wp_steps
    wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun s5 P5 _ _
    ⟨hvm5, hP5, hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx26_5, hx23_5, hx22_5, hx19_5, htr5⟩ => ?_
  refine ⟨?_, hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx26_5, hx23_5, hx22_5, hx19_5, htr5, hvm5⟩
  rw [A.pool_of_vmPreserved hvm5]
  exact hP5

/-- Step 4 of Arm 2 (`+604 -> +704 -> +1544 -> ret`) with `VmPreserved` pool transport
    and `states_into_pb_epilogue_placed`. -/
theorem states_into_pb_headerSent_post_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (F : ShaCompress)
    {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (blkPl_334).base + 604#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx23 : sf.readReg64 .x23 = s.uc.epoch)
    (hx22 : sf.readReg64 .x22 = 0x8000000000000002#64)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗ cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 344#64) ↦₆₄ d0) ∗ ((s0.sp - 336#64) ↦₆₄ d1) ∗
        ((s0.sp - 328#64) ↦₆₄ d2) ∗ ((s0.sp - 320#64) ↦₆₄ d3) ∗ ((s0.sp - 312#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
        memRegion (s0.sp - 880#64) polyDecoderSize ∗
        A.pool lim st sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
        ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
        ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗ ((s0.sp - 352#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
       memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
      (fun s_ret P_ret =>
        (P_ret ⊢
          optProtoInnerStateAt A.repAlloc out (States.headerSent s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) ∧ s_ret.sp = s0.sp ∧
        CalleeSavedPreserved s0 s_ret ∧ s_ret.trace = s0.trace) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hrejoin880 :
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 880#64) polyDecoderSize ⊢
      memRegion (s0.sp - 1360#64) 880 := by
    change memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 880#64) 400 ⊢
      memRegion (s0.sp - 1360#64) 880
    rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 472) (k := 408)
          (b' := s0.sp - 888#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 888#64) (n := 8) (k := 400)
          (b' := s0.sp - 880#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have hrejoin176 :
      ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
      ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
      ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
      ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
      ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
      ((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
      ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
      ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
      ((s0.sp - 352#64) ↦₆₄ e6) ∗ ((s0.sp - 344#64) ↦₆₄ d0) ∗
      ((s0.sp - 336#64) ↦₆₄ d1) ∗ ((s0.sp - 328#64) ↦₆₄ d2) ∗
      ((s0.sp - 320#64) ↦₆₄ d3) ∗ ((s0.sp - 312#64) ↦₆₄ d4) ⊢
      memRegion (s0.sp - 480#64) 176 := by
    rw [ProofLib.memRegion_cells (s0.sp - 480#64) 22 (by decide)]
    cells_unfold
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1
      (Entails.sepExists_right k2 (Entails.sepExists_right a0
        (Entails.sepExists_right a1 (Entails.sepExists_right a2
          (Entails.sepExists_right a3 (Entails.sepExists_right a4
            (Entails.sepExists_right a5 (Entails.sepExists_right s.uc.epoch
              (Entails.sepExists_right e0 (Entails.sepExists_right e1
                (Entails.sepExists_right e2 (Entails.sepExists_right e3
                  (Entails.sepExists_right e4 (Entails.sepExists_right e5
                    (Entails.sepExists_right e6 (Entails.sepExists_right d0
                      (Entails.sepExists_right d1 (Entails.sepExists_right d2
                        (Entails.sepExists_right d3 (Entails.sepExists_right d4
                          (Entails.refl _))))))))))))))))))))))
  have hrejoin160 :
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
       ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
       ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ⊢
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 72) (k := 88)
          (b' := s0.sp - 184#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 184#64) (n := 24) (k := 64)
          (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 48) (k := 16)
          (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 256#64) 9 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1
      (Entails.sepExists_right k2 (Entails.sepExists_right a0
        (Entails.sepExists_right a1 (Entails.sepExists_right a2
          (Entails.sepExists_right a3 (Entails.sepExists_right a4
            (Entails.sepExists_right a5 (Entails.refl _)))))))))
  have hstA := stA_headerSent_entails_928 stA a0 a1 a2 a3 a4 a5 k0 k1 k2
  have hrejoin_all :
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ epilogueStagingCells s0.sp
        k0 k1 k2 a0 a1 a2
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗ (memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 880#64) polyDecoderSize) ∗
      (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
       ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
       ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
       ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
       ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
       ((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
       ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
       ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
       ((s0.sp - 352#64) ↦₆₄ e6) ∗ ((s0.sp - 344#64) ↦₆₄ d0) ∗
       ((s0.sp - 336#64) ↦₆₄ d1) ∗ ((s0.sp - 328#64) ↦₆₄ d2) ∗
       ((s0.sp - 320#64) ↦₆₄ d3) ∗ ((s0.sp - 312#64) ↦₆₄ d4)) ∗
      ((((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗ statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ A.pool lim st sf ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ ((stA ↦₆₄ 4#64) ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
        memRegion (stA + 480#64) 408 ∗ memRegion (stA + 888#64) 40) ∗
       statesIntoPbJumpTablePlacedAt) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ epilogueStagingCells s0.sp
        k0 k1 k2 a0 a1 a2
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗ memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗ statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ A.pool lim st sf ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hrejoin880
        (sepConj_mono hrejoin176
          (sepConj_mono hrejoin160
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_left hstA))))))))))))
  refine seq_clean_wp
    (mid := (blkPl_334).base + 1544#64)
    (P_mid := fun s2 =>
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ epilogueStagingCells s0.sp
        k0 k1 k2 a0 a1 a2
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗ memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗ statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ A.pool lim st s2 ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt))
    (Q := fun s2 =>
      s2.sp = s0.sp - 1520#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
      s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = 0x8000000000000002#64 ∧
      s2.readReg64 .x21 = a3 ∧ TraceCalleeSaved s2 s0)
    ?_
    fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  · refine SepWP.mono
      (post := fun s2 P2 =>
        VmPreserved sf s2 ∧ (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ epilogueStagingCells s0.sp
            k0 k1 k2 a0 a1 a2
            a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
            0#64 w200 w208 w216 ∗ memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗ statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗ A.pool lim st sf ∗
          (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
           protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
           memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt)) ∧
        (s2.sp = s0.sp - 1520#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = 0x8000000000000002#64 ∧
         s2.readReg64 .x21 = a3 ∧ TraceCalleeSaved s2 s0))
      ?_
      fun s2 P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := sf) (Entails.trans ?_ hrejoin_all) ?_
      · dsimp only [epilogueStagingCells]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  · have hep := states_into_pb_epilogue_placed (ext := ext) A lim st s0 s2 out
      k0 k1 k2 a0 a1 a2
      a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
      0#64 w200 w208 w216
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
    rw [hx22_2, hx21_2] at hep
    refine SepWP.mono hep fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret, _⟩ =>
      ⟨?_, hsp_ret, hcs_ret, htr_ret⟩
    refine Entails.trans hPf ?_
    have hout := outWords28_entails_headerSent A.repAlloc out
      k0 k1 k2 a0 a1 a2 a3 a4 a5 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
      w184 0#64 w200 w208 w216 s
    refine Entails.trans (Entails.of_eq (show _ =
      (outWords28 out 0x8000000000000002#64
        k0 k1 k2 a0 a1 a2 a3
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk) ∗ (memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Top-Level `subroutine_ok` Theorems for Arm 2 (`States.headerSent`) -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`)
    on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, HeaderSentEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.headerSent s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit_outer⟩, hmem⟩
  have hfit_seq : FitsEnv M lim st (HeaderSentEnv s) :=
    FitsEnv.mono hEnv hfit_outer
  have hfit_enc : FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_ek) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv hfit_seq.seq_left
  refine ⟨memRegion out optProtoInnerStateSize ∗ chunkedStatesAt A.repAlloc stA (.headerSent s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA (.headerSent s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedHeaderSent_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5 k0 k1 k2
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 4#64
    (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  rw [stack_1416_split_headerSent s0.sp]
  have hpre1 := states_into_pb_headerSent_pre1_placed (ext := ext) A lim st s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 1360#64) 880 ∗
     cells (s0.sp - 480#64) 10 ∗ memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 9 ∗ memRegion (s0.sp - 184#64) 24 ∗
     cells (s0.sp - 160#64) 6 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx22_2, hx21_2, hx20_2, hx19_2, htr2, _⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_enc_words : BitVec 64 → SepProp := fun a =>
    polyEncoderAt A.repAlloc a s.sending_ek ∗
    (((a + 400#64) ↦₆₄ a0) ∗ ((a + 408#64) ↦₆₄ a1) ∗ ((a + 416#64) ↦₆₄ a2) ∗
     ((a + 424#64) ↦₆₄ a3) ∗ ((a + 432#64) ↦₆₄ a4) ∗ ((a + 440#64) ↦₆₄ a5) ∗
     ((a + 448#64) ↦₆₄ k0) ∗ ((a + 456#64) ↦₆₄ k1) ∗ ((a + 464#64) ↦₆₄ k2))
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 8#64) s.receiving_ct1
  have hF_src : F_enc_words (stA + 8#64) =
      (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2))) := by
    dsimp only [F_enc_words]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 472#64) =
      (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) := by
    dsimp only [G_dec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 472#64) =
      (((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1) := by
    dsimp only [G_dec]; simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 472#64 = stA + 480#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_wp_placed A lim st hmemcpy_raw
    (k := 472) (m := 408) (n := 880) (off := 472#64)
    (F := F_enc_words) (G := G_dec) rfl rfl
    (Relocatable.polyEncoder_words9 A.repAlloc s.sending_ek a0 a1 a2 a3 a4 a5 k0 k1 k2)
    (Relocatable.epoch_polyDecoderAt A.repAlloc s.uc.epoch s.receiving_ct1)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 9 ∗
      memRegion (s0.sp - 184#64) 24 ∗ cells (s0.sp - 160#64) 6 ∗
      memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx22_3 : s3.readReg64 .x22 = 0x8000000000000002#64 := hcs3.2.2.2.1.trans hx22_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_headerSent_pre2_placed (ext := ext) A lim st s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx22_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 472 ∗ polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗ memRegion (stA + 480#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
     memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 304#64) 6 ∗ memRegion (s0.sp - 184#64) 24 ∗
     memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx24_4, hx23_4, hx22_4, hx21_4, hx19_4, htr4, _⟩ => ?_)
  refine call_encoderIntoPb_expose_wp_placed henc_raw st (s0.sp - 400#64) (stA + 8#64) s.sending_ek
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4 hfit_enc (by sep_ac_rfl)
    fun s5 evs_enc e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hcs5 _hacp5 htr5 henv_enc => ?_
  have hfit_dec : FitsEnv M lim (M.stepEvents evs_enc st) (DecoderIntoPbAllocEnv s.receiving_ct1) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (hfit_seq.seq_right henv_enc)
  have hx19_5 : s5.readReg64 .x19 = out := hcs5.1.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = s0.sp - 1360#64 := hcs5.2.2.1.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = 0x8000000000000002#64 := hcs5.2.2.2.1.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = s.uc.epoch := hcs5.2.2.2.2.1.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = s0.sp - 480#64 := hcs5.2.2.2.2.2.1.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = s0.sp - 480#64 := hcs5.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_5 : s5.readReg64 .x29 = s0.sp - 96#64 := hcs5.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpre3 := states_into_pb_headerSent_pre3_placed (ext := ext)
    A lim (M.stepEvents evs_enc st) s0 s5 out s.uc.epoch
    hpc5 hrun5 hsp5 hx29_5 hx26_5 hx24_5 hx23_5 hx22_5 hx21_5 hx19_5 htr5
    ((((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
      ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
      ((s0.sp - 352#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
      memRegion (stA + 8#64) polyEncoderSize ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
     (cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt))
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (seq_clean_wp hpre3 fun s6 hpc6 hrun6
      ⟨hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx26_6, hx23_6, hx22_6, hx19_6, htr6, _⟩ => ?_)
  · simp only [arm64_norm]; sep_ac_rfl
  refine call_decoderIntoPb_expose_wp_placed hdec_raw (M.stepEvents evs_enc st)
    (s0.sp - 344#64) (s0.sp - 880#64) s.receiving_ct1
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
       ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
       ((s0.sp - 352#64) ↦₆₄ e6) ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize) ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6 hfit_dec (by sep_ac_rfl)
    fun sf evs_dec d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf _hacpf htrf henv_dec => ?_
  rw [← M.stepEvents_append evs_enc evs_dec st]
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_6
  have hx22_f : sf.readReg64 .x22 = 0x8000000000000002#64 := hcsf.2.2.2.1.trans hx22_6
  have hx23_f : sf.readReg64 .x23 = s.uc.epoch := hcsf.2.2.2.2.1.trans hx23_6
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_6
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  have hpost_step := states_into_pb_headerSent_post_placed (ext := ext)
    A lim (M.stepEvents (evs_enc ++ evs_dec) st) F
    s0 sf out stA s a0 a1 a2 a3 a4 a5 k0 k1 k2 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx23_f hx22_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono hpost_step fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret⟩ =>
      ⟨⟨evs_enc ++ evs_dec, hEnv _ (headerSentEnv_of_parts henv_enc henv_dec), hPf⟩,
       hsp_ret, hcs_ret, htr_ret⟩)
  simp only [arm64_norm]
  sep_ac_rfl

/-- Tight `HeaderSentEnv` relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`)
    on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbHeaderSentPlacedSpec M A lim F s) :=
  states_into_pb_headerSent_of_env_placed henc_raw hdec_raw hmemcpy_raw s (fun _ h => h)

/-- Verifies `<States>::into_pb` (Block `334`) on
    `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbHeaderSentPlacedSpec M A lim F s) :=
  states_into_pb_headerSent_env_placed henc_raw hdec_raw hmemcpy_raw s

set_option maxHeartbeats 800000 in
/-- Envelope-parametric `withLsCodeLoaded` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, HeaderSentEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.headerSent s) Env)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [withLsCodeLoaded, statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit_outer⟩, hmem0⟩
  have hmem1 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
      ((memRegion out optProtoInnerStateSize ∗ chunkedStatesAt A.repAlloc stA (.headerSent s) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem0
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hcl0, hmem⟩
  have hfit_seq : FitsEnv M lim st (HeaderSentEnv s) :=
    FitsEnv.mono hEnv hfit_outer
  have hfit_enc : FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_ek) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv hfit_seq.seq_left
  refine ⟨memRegion out optProtoInnerStateSize ∗ chunkedStatesAt A.repAlloc stA (.headerSent s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, hmem, ?_⟩
  refine sepWPp_of_states_into_pb_wpp_of_env_cl_placed st s0 s0 out stA (.headerSent s) Env _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedHeaderSent_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 =>
    SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
    SepWPp.exists_elim fun k2 => ?_
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 4#64
    (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl0 hpro fun s1 hpc1 hrun1 hcl1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  · sep_ac_rfl
  rw [stack_1416_split_headerSent s0.sp]
  have hpre1 := states_into_pb_headerSent_pre1_placed (ext := ext) A lim st s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 1360#64) 880 ∗
     cells (s0.sp - 480#64) 10 ∗ memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 9 ∗ memRegion (s0.sp - 184#64) 24 ∗
     cells (s0.sp - 160#64) 6 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize)
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl1 hpre1 fun s2 hpc2 hrun2 hcl2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx22_2, hx21_2, hx20_2, hx19_2, htr2, _⟩ => ?_)
  · sep_ac_rfl
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_enc_words : BitVec 64 → SepProp := fun a =>
    polyEncoderAt A.repAlloc a s.sending_ek ∗
    (((a + 400#64) ↦₆₄ a0) ∗ ((a + 408#64) ↦₆₄ a1) ∗ ((a + 416#64) ↦₆₄ a2) ∗
     ((a + 424#64) ↦₆₄ a3) ∗ ((a + 432#64) ↦₆₄ a4) ∗ ((a + 440#64) ↦₆₄ a5) ∗
     ((a + 448#64) ↦₆₄ k0) ∗ ((a + 456#64) ↦₆₄ k1) ∗ ((a + 464#64) ↦₆₄ k2))
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 8#64) s.receiving_ct1
  have hF_src : F_enc_words (stA + 8#64) =
      (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2))) := by
    dsimp only [F_enc_words]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 472#64) =
      (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 488#64) s.receiving_ct1) := by
    dsimp only [G_dec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 472#64) =
      (((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1) := by
    dsimp only [G_dec]; simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 472#64 = stA + 480#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_cl_placed A lim st hmemcpy_raw
    (k := 472) (m := 408) (n := 880) (off := 472#64)
    (F := F_enc_words) (G := G_dec) rfl rfl
    (Relocatable.polyEncoder_words9 A.repAlloc s.sending_ek a0 a1 a2 a3 a4 a5 k0 k1 k2)
    (Relocatable.epoch_polyDecoderAt A.repAlloc s.uc.epoch s.receiving_ct1)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 9 ∗
      memRegion (s0.sp - 184#64) 24 ∗ cells (s0.sp - 160#64) 6 ∗
      memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hcl2 hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 hcl3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx22_3 : s3.readReg64 .x22 = 0x8000000000000002#64 := hcs3.2.2.2.1.trans hx22_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_headerSent_pre2_placed (ext := ext) A lim st s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx22_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 472 ∗ polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ek ∗ memRegion (stA + 480#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
     memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 304#64) 6 ∗ memRegion (s0.sp - 184#64) 24 ∗
     memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl3 hpre2 fun s4 hpc4 hrun4 hcl4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx24_4, hx23_4, hx22_4, hx21_4, hx19_4, htr4, _⟩ => ?_)
  · sep_ac_rfl
  refine call_encoderIntoPb_expose_cl_placed henc_cl st (s0.sp - 400#64) (stA + 8#64) s.sending_ek
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hcl4 hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4 hfit_enc (by sep_ac_rfl)
    fun s5 evs_enc e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hcs5 _hacp5 htr5 hcl5 henv_enc => ?_
  have hfit_dec : FitsEnv M lim (M.stepEvents evs_enc st) (DecoderIntoPbAllocEnv s.receiving_ct1) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (hfit_seq.seq_right henv_enc)
  have hx19_5 : s5.readReg64 .x19 = out := hcs5.1.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = s0.sp - 1360#64 := hcs5.2.2.1.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = 0x8000000000000002#64 := hcs5.2.2.2.1.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = s.uc.epoch := hcs5.2.2.2.2.1.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = s0.sp - 480#64 := hcs5.2.2.2.2.2.1.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = s0.sp - 480#64 := hcs5.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_5 : s5.readReg64 .x29 = s0.sp - 96#64 := hcs5.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpre3 := states_into_pb_headerSent_pre3_placed (ext := ext)
    A lim (M.stepEvents evs_enc st) s0 s5 out s.uc.epoch
    hpc5 hrun5 hsp5 hx29_5 hx26_5 hx24_5 hx23_5 hx22_5 hx21_5 hx19_5 htr5
    ((((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
      ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
      ((s0.sp - 352#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
      memRegion (stA + 8#64) polyEncoderSize ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
     (cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A.repAlloc (s0.sp - 880#64) s.receiving_ct1 ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt))
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl5 hpre3 fun s6 hpc6 hrun6 hcl6
      ⟨hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx26_6, hx23_6, hx22_6, hx19_6, htr6, _⟩ => ?_)
  · simp only [arm64_norm]; sep_ac_rfl
  refine call_decoderIntoPb_expose_cl_placed hdec_cl (M.stepEvents evs_enc st)
    (s0.sp - 344#64) (s0.sp - 880#64) s.receiving_ct1
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
       ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
       ((s0.sp - 352#64) ↦₆₄ e6) ∗
       protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize) ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hcl6 hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6 hfit_dec (by sep_ac_rfl)
    fun sf evs_dec d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf _hacpf htrf _hclf henv_dec => ?_
  rw [← M.stepEvents_append evs_enc evs_dec st]
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_6
  have hx22_f : sf.readReg64 .x22 = 0x8000000000000002#64 := hcsf.2.2.2.1.trans hx22_6
  have hx23_f : sf.readReg64 .x23 = s.uc.epoch := hcsf.2.2.2.2.1.trans hx23_6
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_6
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_headerSent_post_placed (ext := ext)
    A lim (M.stepEvents (evs_enc ++ evs_dec) st) F
    s0 sf out stA s a0 a1 a2 a3 a4 a5 k0 k1 k2 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx23_f hx22_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono hpost_step fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret⟩ =>
      ⟨⟨evs_enc ++ evs_dec, hEnv _ (headerSentEnv_of_parts henv_enc henv_dec), hPf⟩,
       hsp_ret, hcs_ret, htr_ret⟩)
  simp only [arm64_norm]
  sep_ac_rfl

/-- Tight `HeaderSentEnv` `withLsCodeLoaded` relocatable `subroutine_ok` for
    `<States>::into_pb` (Block `334`) on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbHeaderSentPlacedSpec M A lim F s)) :=
  states_into_pb_headerSent_of_env_cl_placed henc_cl hdec_cl hmemcpy_raw s (fun _ h => h)

/-- Verifies `<States>::into_pb`
    (Block `334`) on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbHeaderSentPlacedSpec M A lim F s)) :=
  states_into_pb_headerSent_env_cl_placed henc_cl hdec_cl hmemcpy_raw s

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget
