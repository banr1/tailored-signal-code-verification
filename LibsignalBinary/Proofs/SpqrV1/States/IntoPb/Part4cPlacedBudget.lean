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
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Placed
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 4c Placed: Arm 4 (`States.ekSentCt1Received`)

Relocatable `[LibsignalPlacement]` verification of Arm 4 (`States.ekSentCt1Received`, tag `6`)
on Block `334` under `RustCliAllocBudget M` and `EkSentCt1ReceivedEnv`, in plain and
`withLsCodeLoaded` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement libsignalSessionCode lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (Relocatable TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   chunkedEkSentCt1Received_expose epilogueStagingCells outWords28
   outWords28_entails_ekSentCt1Received protoPolynomialDecoderHeap
   stA_ekSentCt1Received_entails_928 stack_1416_split_ekSentCt1Received
   statesIntoPbJumpTableBytes statesIntoPbJumpTablePlacedAt
   statesIntoPbSavedCells statesIntoPbStack vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv decoderIntoPbSpec
   fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_placed statesIntoPbVariantPlacedSpecOfEnv
   states_into_pb_epilogue_placed states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
  (call_decoderIntoPb_expose_cl_placed sepWPp_of_states_into_pb_wpp_of_env_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (call_decoderIntoPb_expose_wp_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
  (call_memcpy_keep_relocate_cl_placed call_memcpy_keep_relocate_wp_placed
   statesIntoPb_seq_sepWP_cl_vm)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget (EkSentCt1ReceivedEnv)
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

/-! ## 1. Envelope & Relocatable Spec for Arm 4 (`States.ekSentCt1Received`) -/

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cBudget (EkSentCt1ReceivedEnv)

abbrev statesIntoPbEkSentCt1ReceivedPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekSentCt1Received s) (EkSentCt1ReceivedEnv s)

/-! ## 2. Step Lemmas for Arm 4 (`States.ekSentCt1Received`, tag `6`) -/

/-- Step 1 of Arm 4 (`+60 -> +96 -> +140 -> +156 -> lsρ "memcpy"`) with `VmPreserved` pool transport. -/
theorem states_into_pb_ekSentCt1Received_pre1_placed [LibsignalPlacement]
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
    (hx8 : s1.readReg64 .x8 = 6#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s1
      (statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s2 ∗ Rest) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (blkPl_334).base + 160#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        (s2.readReg64 .x2).toNat = 504 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧
        s2.readReg64 .x20 = stA ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0 ∧
        VmPreserved s1 s2) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  let Rest' : SepProp := A.pool lim st s1 ∗ Rest
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") s1
      (statesIntoPbJumpTablePlacedAt ∗ Rest')
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢ statesIntoPbJumpTablePlacedAt ∗ Rest') ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (blkPl_334).base + 160#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         (s2.readReg64 .x2).toNat = 504 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x28 = s0.sp - 256#64 ∧
         s2.readReg64 .x26 = s0.sp - 480#64 ∧
         s2.readReg64 .x21 = s0.sp - 1360#64 ∧
         s2.readReg64 .x20 = stA ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) := by
    dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    wp_steps
    wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun s2 P2 _ _
    ⟨hvm2, hP2, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_
  refine ⟨?_, hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2, hvm2⟩
  rw [A.pool_of_vmPreserved hvm2]
  exact hP2

/-- Step 2 of Arm 4 (`+160 -> +248 -> lsmpl.base 377`) with `VmPreserved` pool transport. -/
theorem states_into_pb_ekSentCt1Received_pre2_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (blkPl_334).base + 160#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr2 : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s2
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
       cells (s0.sp - 256#64) 18 ∗
       A.pool lim st s2 ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
           ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
           ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
          ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
           ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
           ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
           ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
           ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗
          A.pool lim st s3 ∗ Rest) ∧
        s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (blkPl_334).base + 252#64 ∧
        s3.readReg64 .x0 = s0.sp - 376#64 ∧
        s3.readReg64 .x1 = s0.sp - 1256#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧
        s3.readReg64 .x20 = epoch ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0 ∧
        VmPreserved s2 s3) := by
  rcases htr2 with ⟨htr2, hvregs⟩
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have h160_48 :
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
  rename_i m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17
  let Rest' : SepProp := A.pool lim st s2 ∗ Rest
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) s2
      ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
       (((s0.sp - 256#64) ↦₆₄ m0) ∗ ((s0.sp - 248#64) ↦₆₄ m1) ∗
        ((s0.sp - 240#64) ↦₆₄ m2) ∗ ((s0.sp - 232#64) ↦₆₄ m3) ∗
        ((s0.sp - 224#64) ↦₆₄ m4) ∗ ((s0.sp - 216#64) ↦₆₄ m5) ∗
        ((s0.sp - 208#64) ↦₆₄ m6) ∗ ((s0.sp - 200#64) ↦₆₄ m7) ∗
        ((s0.sp - 192#64) ↦₆₄ m8) ∗ ((s0.sp - 184#64) ↦₆₄ m9) ∗
        ((s0.sp - 176#64) ↦₆₄ m10) ∗ ((s0.sp - 168#64) ↦₆₄ m11) ∗
        ((s0.sp - 160#64) ↦₆₄ m12) ∗ ((s0.sp - 152#64) ↦₆₄ m13) ∗
        ((s0.sp - 144#64) ↦₆₄ m14) ∗ ((s0.sp - 136#64) ↦₆₄ m15) ∗
        ((s0.sp - 128#64) ↦₆₄ m16) ∗ ((s0.sp - 120#64) ↦₆₄ m17)) ∗
       Rest')
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧
        (P3 ⊢
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
           ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
           ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
          ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
           ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
           ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
           ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
           ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗
          Rest') ∧
        (s3.sp = s0.sp - 1520#64 ∧
         s3.readReg64 .x30 = (blkPl_334).base + 252#64 ∧
         s3.readReg64 .x0 = s0.sp - 376#64 ∧
         s3.readReg64 .x1 = s0.sp - 1256#64 ∧
         s3.readReg64 .x29 = s0.sp - 96#64 ∧
         s3.readReg64 .x26 = s0.sp - 480#64 ∧
         s3.readReg64 .x20 = epoch ∧
         s3.readReg64 .x19 = out ∧
         TraceCalleeSaved s3 s0)) := by
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := s2)
        (Entails.trans (Entails.of_eq (show _ =
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
           ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
           ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
          ((s0.sp - 1264#64) ↦₆₄ epoch) ∗
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
           ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
           ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
           ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
           ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
          (((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
           ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
           ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5)) ∗ Rest' by sep_ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h160_48))))) ?_
      wp_done)
  dsimp only [Rest'] at hwp
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono hwp fun s3 P3 _ _
      ⟨hvm3, hP3, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx20_3, hx19_3, htr3⟩ => ?_)
  refine ⟨?_, hsp3, hlr3, hx0_3, hx1_3, hx29_3, hx26_3, hx20_3, hx19_3, htr3, hvm3⟩
  rw [A.pool_of_vmPreserved hvm3]
  exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))

/-- Step 3 of Arm 4 (`+252 -> +356 -> +1544 -> ret`) with `VmPreserved` pool transport
    and `states_into_pb_epilogue_placed`. -/
theorem states_into_pb_ekSentCt1Received_post_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (F : ShaCompress)
    {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 dec0 dec1 dec2 dec3 dec4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (blkPl_334).base + 252#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29_f : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26_f : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx20_f : sf.readReg64 .x20 = s.uc.epoch)
    (hx19_f : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       cells (s0.sp - 480#64) 13 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
        ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
        ((s0.sp - 344#64) ↦₆₄ dec4) ∗
        protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
        memRegion (s0.sp - 1256#64) polyDecoderSize ∗
        A.pool lim st sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
        ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
        ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
        ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
        ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 96 ∗
       ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 856#64) 376 ∗
       memRegion (s0.sp - 336#64) 32 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 6#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
        ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
        ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
       memRegion (stA + 104#64) 408 ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
       memRegion (stA + 512#64) 416 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (fun s_ret P_ret =>
        (P_ret ⊢
          optProtoInnerStateAt A.repAlloc out (States.ekSentCt1Received s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTablePlacedAt ∗
          A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) ∧
        s_ret.sp = s0.sp ∧
        CalleeSavedPreserved s0 s_ret ∧
        s_ret.trace = s0.trace) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hrejoin880 :
      memRegion (s0.sp - 1360#64) 96 ∗
      ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 1256#64) polyDecoderSize ∗
      memRegion (s0.sp - 856#64) 376 ⊢
      memRegion (s0.sp - 1360#64) 880 := by
    change memRegion (s0.sp - 1360#64) 96 ∗
      ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 1256#64) 400 ∗
      memRegion (s0.sp - 856#64) 376 ⊢
      memRegion (s0.sp - 1360#64) 880
    rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 96) (k := 784)
          (b' := s0.sp - 1264#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1264#64) (n := 8) (k := 776)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1256#64) (n := 400) (k := 376)
          (b' := s0.sp - 856#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have hrejoin176 :
      (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
       ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
       ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
       ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
       ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
       ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
       ((s0.sp - 384#64) ↦₆₄ s.uc.epoch) ∗
       ((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
       ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
       ((s0.sp - 344#64) ↦₆₄ dec4)) ∗
      memRegion (s0.sp - 336#64) 32 ⊢
      memRegion (s0.sp - 480#64) 176 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 144) (k := 32)
          (b' := s0.sp - 336#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 480#64) 18 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1
      (Entails.sepExists_right k2 (Entails.sepExists_right d0
        (Entails.sepExists_right d1 (Entails.sepExists_right d2
          (Entails.sepExists_right a0 (Entails.sepExists_right a1
            (Entails.sepExists_right a2 (Entails.sepExists_right a3
              (Entails.sepExists_right a4 (Entails.sepExists_right a5
                (Entails.sepExists_right s.uc.epoch (Entails.sepExists_right dec0
                  (Entails.sepExists_right dec1 (Entails.sepExists_right dec2
                    (Entails.sepExists_right dec3 (Entails.sepExists_right dec4
                      (Entails.refl _))))))))))))))))))
  have hrejoin160 :
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
       ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
       ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
       ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
       ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
       ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ⊢
      memRegion (s0.sp - 256#64) 160 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 96) (k := 64)
          (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 48) (k := 16)
          (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 256#64) 12 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right k0 (Entails.sepExists_right k1
      (Entails.sepExists_right k2 (Entails.sepExists_right d0
        (Entails.sepExists_right d1 (Entails.sepExists_right d2
          (Entails.sepExists_right a0 (Entails.sepExists_right a1
            (Entails.sepExists_right a2 (Entails.sepExists_right a3
              (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))))))))
  have hstA := stA_ekSentCt1Received_entails_928 stA a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2
  have hrejoin_all :
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 d0 d1 d2 a1 a2 a3 a4 a5 s.uc.epoch
        dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 96 ∗ ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1256#64) polyDecoderSize ∗ memRegion (s0.sp - 856#64) 376) ∗
      ((((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
        ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
        ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
        ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
        ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
        ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
        ((s0.sp - 384#64) ↦₆₄ s.uc.epoch) ∗
        ((s0.sp - 376#64) ↦₆₄ dec0) ∗ ((s0.sp - 368#64) ↦₆₄ dec1) ∗
        ((s0.sp - 360#64) ↦₆₄ dec2) ∗ ((s0.sp - 352#64) ↦₆₄ dec3) ∗
        ((s0.sp - 344#64) ↦₆₄ dec4)) ∗
       memRegion (s0.sp - 336#64) 32) ∗
      ((((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ d0) ∗
        ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
        ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗
        ((s0.sp - 192#64) ↦₆₄ a2) ∗ ((s0.sp - 184#64) ↦₆₄ a3) ∗
        ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 160#64) 48 ∗ memRegion (s0.sp - 112#64) 16) ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim st sf ∗
      (protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
       ((stA ↦₆₄ 6#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗
         ((stA + 72#64) ↦₆₄ k2) ∗ ((stA + 80#64) ↦₆₄ d0) ∗
         ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
        memRegion (stA + 104#64) 408 ∗ memRegion (stA + 512#64) 416) ∗
       statesIntoPbJumpTablePlacedAt) ⊢
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 d0 d1 d2 a1 a2 a3 a4 a5 s.uc.epoch
        dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗
      memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      A.pool lim st sf ∗
      (protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗
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
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 d0 d1 d2 a1 a2 a3 a4 a5 s.uc.epoch
        dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
      memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 176 ∗
      memRegion (s0.sp - 256#64) 160 ∗ statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ A.pool lim st s2 ∗
      (protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt))
    (Q := fun s2 =>
      s2.sp = s0.sp - 1520#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
      s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = 0x8000000000000004#64 ∧
      s2.readReg64 .x21 = a0 ∧ TraceCalleeSaved s2 s0)
    ?_
    fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  · refine SepWP.mono
      (post := fun s2 P2 =>
        VmPreserved sf s2 ∧
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            k0 k1 k2 d0 d1 d2 a1 a2 a3 a4 a5 s.uc.epoch
            dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗ statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗ A.pool lim st sf ∗
          (protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
           vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
           memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt)) ∧
        (s2.sp = s0.sp - 1520#64 ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧ s2.readReg64 .x22 = 0x8000000000000004#64 ∧
         s2.readReg64 .x21 = a0 ∧ TraceCalleeSaved s2 s0))
      ?_
      fun s2 P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := sf) (Entails.trans ?_ hrejoin_all) ?_
      · dsimp only [epilogueStagingCells]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  · have hep := states_into_pb_epilogue_placed (ext := ext) A lim st s0 s2 out
      k0 k1 k2 d0 d1 d2 a1 a2 a3 a4 a5 s.uc.epoch
      dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216
      (protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
       memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
    rw [hx22_2, hx21_2] at hep
    refine SepWP.mono hep fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret, _⟩ =>
      ⟨?_, hsp_ret, hcs_ret, htr_ret⟩
    refine Entails.trans hPf ?_
    have hout := outWords28_entails_ekSentCt1Received A.repAlloc out
      k0 k1 k2 d0 d1 d2 a0 a1 a2 a3 a4 a5 dec0 dec1 dec2 dec3 dec4
      w152 w160 w168 w176 w184 0#64 w200 w208 w216 s
    refine Entails.trans (Entails.of_eq (show _ =
      (outWords28 out 0x8000000000000004#64 k0 k1 k2 d0 d1 d2 a0 a1 a2 a3 a4 a5 s.uc.epoch
        dec0 dec1 dec2 dec3 dec4 w152 w160 w168 w176 w184 0#64 w200 w208 w216 ∗
       protoPolynomialDecoderHeap A.repAlloc dec0 dec1 dec2 dec3 dec4 s.receiving_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
       vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1) ∗
      (memRegion stA chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim st s_ret ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Top-Level `subroutine_ok` Theorems for Arm 4 (`States.ekSentCt1Received`) -/

set_option maxHeartbeats 800000 in
/-- Envelope-parametric relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`)
    on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, EkSentCt1ReceivedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekSentCt1Received s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit_outer⟩, hmem⟩
  have hfit_dec : FitsEnv M lim st (DecoderIntoPbAllocEnv s.receiving_ct2) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (FitsEnv.mono hEnv hfit_outer)
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ekSentCt1Received s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA (.ekSentCt1Received s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkSentCt1Received_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 6#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
      ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  rw [stack_1416_split_ekSentCt1Received s0.sp]
  have hpre1 := states_into_pb_ekSentCt1Received_pre1_placed (ext := ext) A lim st s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 1360#64) 504 ∗
     memRegion (s0.sp - 856#64) 376 ∗ cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗ memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 18 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
      ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2, _⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ k0) ∗ ((a + 56#64) ↦₆₄ k1) ∗ ((a + 64#64) ↦₆₄ k2) ∗
    ((a + 72#64) ↦₆₄ d0) ∗ ((a + 80#64) ↦₆₄ d1) ∗ ((a + 88#64) ↦₆₄ d2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 8#64) s.receiving_ct2
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
       ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) := by
    dsimp only [F_words]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) := by
    dsimp only [G_dec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (s0.sp - 1256#64) s.receiving_ct2) := by
    dsimp only [G_dec]; simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_wp_placed A lim st hmemcpy_raw
    (k := 96) (m := 408) (n := 504) (off := 96#64) (F := F_words) (G := G_dec) rfl rfl
    (Relocatable.words12 a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2)
    (Relocatable.epoch_polyDecoderAt A.repAlloc s.uc.epoch s.receiving_ct2)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 856#64) 376 ∗
      cells (s0.sp - 480#64) 13 ∗ memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗
      memRegion (s0.sp - 336#64) 32 ∗ cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 18 ∗
      memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_ekSentCt1Received_pre2_placed (ext := ext) A lim st s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 96 ∗ polyDecoderAt A.repAlloc (s0.sp - 1256#64) s.receiving_ct2 ∗
     memRegion (stA + 104#64) 408 ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 856#64) 376 ∗ cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗ memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4, _⟩ => ?_)
  refine call_decoderIntoPb_expose_wp_placed hdec_raw st
    (s0.sp - 376#64) (s0.sp - 1256#64) s.receiving_ct2
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 13 ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ d0) ∗ ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
       ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗ ((s0.sp - 192#64) ↦₆₄ a2) ∗
       ((s0.sp - 184#64) ↦₆₄ a3) ∗ ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 160#64) 48 ∗ memRegion (s0.sp - 112#64) 16 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1360#64) 96 ∗
      ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗ memRegion (s0.sp - 856#64) 376 ∗
      memRegion (s0.sp - 336#64) 32 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
       ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
      memRegion (stA + 104#64) 408 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4 hfit_dec (by sep_ac_rfl)
    fun sf evs dec0 dec1 dec2 dec3 dec4 hpcf hrunf hspf hcsf _hacpf htrf henv_dec => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpost_step := states_into_pb_ekSentCt1Received_post_placed (ext := ext)
    A lim (M.stepEvents evs st) F
    s0 sf out stA s a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 dec0 dec1 dec2 dec3 dec4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono hpost_step fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret⟩ =>
      ⟨⟨evs, hEnv evs henv_dec, hPf⟩, hsp_ret, hcs_ret, htr_ret⟩)
  simp only [arm64_norm]
  sep_ac_rfl

/-- Tight `EkSentCt1ReceivedEnv` relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`)
    on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbEkSentCt1ReceivedPlacedSpec M A lim F s) :=
  states_into_pb_ekSentCt1Received_of_env_placed hdec_raw hmemcpy_raw s (fun _ h => h)

/-- Verifies `<States>::into_pb` (Block `334`) on
    `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbEkSentCt1ReceivedPlacedSpec M A lim F s) :=
  states_into_pb_ekSentCt1Received_env_placed hdec_raw hmemcpy_raw s

set_option maxHeartbeats 800000 in
/-- Envelope-parametric `withLsCodeLoaded` relocatable `subroutine_ok` for `<States>::into_pb`
    (Block `334`) on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, EkSentCt1ReceivedEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ekSentCt1Received s) Env)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [withLsCodeLoaded, statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit_outer⟩, hmem0⟩
  have hmem1 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
      ((memRegion out optProtoInnerStateSize ∗
        chunkedStatesAt A.repAlloc stA (.ekSentCt1Received s) ∗
        statesIntoPbJumpTablePlacedAt ∗
        A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem0
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨hcl0, hmem⟩
  have hfit_dec : FitsEnv M lim st (DecoderIntoPbAllocEnv s.receiving_ct2) :=
    fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv (FitsEnv.mono hEnv hfit_outer)
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ekSentCt1Received s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, hmem, ?_⟩
  refine sepWPp_of_states_into_pb_wpp_of_env_cl_placed st s0 s0 out stA (.ekSentCt1Received s) Env _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedEkSentCt1Received_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 =>
    SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
    SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun d0 =>
    SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 => ?_
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 6#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
      ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl0 hpro fun s1 hpc1 hrun1 hcl1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  · sep_ac_rfl
  rw [stack_1416_split_ekSentCt1Received s0.sp]
  have hpre1 := states_into_pb_ekSentCt1Received_pre1_placed (ext := ext) A lim st s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 1360#64) 504 ∗
     memRegion (s0.sp - 856#64) 376 ∗ cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗ memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 18 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
      ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
      ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
     (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize)
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl1 hpre1 fun s2 hpc2 hrun2 hcl2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2, _⟩ => ?_)
  · sep_ac_rfl
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ k0) ∗ ((a + 56#64) ↦₆₄ k1) ∗ ((a + 64#64) ↦₆₄ k2) ∗
    ((a + 72#64) ↦₆₄ d0) ∗ ((a + 80#64) ↦₆₄ d1) ∗ ((a + 88#64) ↦₆₄ d2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (a + 8#64) s.receiving_ct2
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
       ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) := by
    dsimp only [F_words]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 96#64) =
      (((stA + 104#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A.repAlloc (stA + 112#64) s.receiving_ct2) := by
    dsimp only [G_dec]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 96#64) =
      (((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A.repAlloc (s0.sp - 1256#64) s.receiving_ct2) := by
    dsimp only [G_dec]; simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 96#64 = stA + 104#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate_cl_placed A lim st hmemcpy_raw
    (k := 96) (m := 408) (n := 504) (off := 96#64) (F := F_words) (G := G_dec) rfl rfl
    (Relocatable.words12 a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2)
    (Relocatable.epoch_polyDecoderAt A.repAlloc s.uc.epoch s.receiving_ct2)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 856#64) 376 ∗
      cells (s0.sp - 480#64) 13 ∗ memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗
      memRegion (s0.sp - 336#64) 32 ∗ cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 18 ∗
      memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hcl2 hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; sep_ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 _hvm3 htr3 hcl3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_ekSentCt1Received_pre2_placed (ext := ext) A lim st s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 96 ∗ polyDecoderAt A.repAlloc (s0.sp - 1256#64) s.receiving_ct2 ∗
     memRegion (stA + 104#64) 408 ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 856#64) 376 ∗ cells (s0.sp - 480#64) 13 ∗
     memRegion (s0.sp - 376#64) protoPolynomialDecoderSize ∗ memRegion (s0.sp - 336#64) 32 ∗
     cells (s0.sp - 304#64) 6 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
     memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (statesIntoPb_seq_sepWP_cl_vm hcl3 hpre2 fun s4 hpc4 hrun4 hcl4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4, _⟩ => ?_)
  · sep_ac_rfl
  refine call_decoderIntoPb_expose_cl_placed hdec_cl st
    (s0.sp - 376#64) (s0.sp - 1256#64) s.receiving_ct2
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 13 ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ d0) ∗ ((s0.sp - 224#64) ↦₆₄ d1) ∗ ((s0.sp - 216#64) ↦₆₄ d2) ∗
       ((s0.sp - 208#64) ↦₆₄ a0) ∗ ((s0.sp - 200#64) ↦₆₄ a1) ∗ ((s0.sp - 192#64) ↦₆₄ a2) ∗
       ((s0.sp - 184#64) ↦₆₄ a3) ∗ ((s0.sp - 176#64) ↦₆₄ a4) ∗ ((s0.sp - 168#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 160#64) 48 ∗ memRegion (s0.sp - 112#64) 16 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 1360#64) 96 ∗
      ((s0.sp - 1264#64) ↦₆₄ s.uc.epoch) ∗ memRegion (s0.sp - 856#64) 376 ∗
      memRegion (s0.sp - 336#64) 32 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 6#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗ ((stA + 24#64) ↦₆₄ a2) ∗
       ((stA + 32#64) ↦₆₄ a3) ∗ ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ k0) ∗ ((stA + 64#64) ↦₆₄ k1) ∗ ((stA + 72#64) ↦₆₄ k2) ∗
       ((stA + 80#64) ↦₆₄ d0) ∗ ((stA + 88#64) ↦₆₄ d1) ∗ ((stA + 96#64) ↦₆₄ d2)) ∗
      memRegion (stA + 104#64) 408 ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.dk ∗
      vecU8Heap A.repAlloc d0 d1 d2 s.uc.ct1 ∗
      memRegion (stA + 512#64) 416 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    hcl4 hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4 hfit_dec (by sep_ac_rfl)
    fun sf evs dec0 dec1 dec2 dec3 dec4 hpcf hrunf hspf hcsf _hacpf htrf _hclf henv_dec => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_ekSentCt1Received_post_placed (ext := ext)
    A lim (M.stepEvents evs st) F
    s0 sf out stA s a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 dec0 dec1 dec2 dec3 dec4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (SepWP.mono hpost_step fun s_ret P_ret _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret⟩ =>
      ⟨⟨evs, hEnv evs henv_dec, hPf⟩, hsp_ret, hcs_ret, htr_ret⟩)
  simp only [arm64_norm]
  sep_ac_rfl

/-- Tight `EkSentCt1ReceivedEnv` `withLsCodeLoaded` relocatable `subroutine_ok` for
    `<States>::into_pb` (Block `334`) on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbEkSentCt1ReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_ekSentCt1Received_of_env_cl_placed hdec_cl hmemcpy_raw s (fun _ h => h)

/-- Verifies `<States>::into_pb`
    (Block `334`) on `.ekSentCt1Received s` (Arm 4, tag `6`). -/
theorem states_into_pb_ekSentCt1Received_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbEkSentCt1ReceivedPlacedSpec M A lim F s)) :=
  states_into_pb_ekSentCt1Received_env_cl_placed hdec_cl hmemcpy_raw s

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget
