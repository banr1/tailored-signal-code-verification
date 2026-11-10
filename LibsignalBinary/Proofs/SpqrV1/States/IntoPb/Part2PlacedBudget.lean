/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Part 2 Placed: Arm 10 (`States.ct2Sampled`)

Relocatable (`[LibsignalPlacement]`) `VmPreserved` pre/post steppers and `RustCliAllocBudget M`
contracts for Arm 10 (`States.ct2Sampled`, tag `12`, Block `334`) under `Ct2SampledEnv` and
`StatesIntoPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement libsignalSessionCode lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit bv_sub_sub_lit
   chunkedCt2Sampled_expose epilogueStagingCells outWords28
   outWords28_entails_ct2Sampled protoPolynomialEncoderHeap
   stA_ct2Sampled_entails_928 statesIntoPbJumpTableBytes
   statesIntoPbJumpTablePlacedAt statesIntoPbSavedCells statesIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec encoderIntoPbVecs
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (SpqrBoundedEvs sepWPp_of_states_into_pb_exit_placed
   statesIntoPbVariantPlacedSpec statesIntoPbVariantPlacedSpecOfEnv
   states_into_pb_epilogue_placed states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
  (call_encoderIntoPb_expose_wp_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget
  (Ct2SampledEnv encoderIntoPbEnv_imp_spqrBoundedEvs
   nonFreeCount_encoderIntoPbEnv_le spqrBoundedEvs_encoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget
  (Ct2SampledEnv nonFreeCount_encoderIntoPbEnv_le
   encoderIntoPbEnv_imp_spqrBoundedEvs spqrBoundedEvs_encoderIntoPbSlotEvents)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_add_lit
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

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

private theorem seq_vm_step {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Allocator Event Envelope Bridges for Arm 10 (`States.ct2Sampled`) -/

theorem fitsEnv_encoder_of_ct2SampledEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {s : Ct2Sampled spqrPolyApi (spqrAuthApi F)}
    {Env : List AllocEvent → Prop}
    (hEnv : ∀ evs, Ct2SampledEnv s evs → Env evs)
    (hfit : FitsEnv M lim st Env) :
    FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_ct2) :=
  fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv (FitsEnv.mono hEnv hfit)

theorem ct2SampledEnv_imp_spqrBoundedEvs {F : ShaCompress}
    {s : Ct2Sampled spqrPolyApi (spqrAuthApi F)}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + (encoderIntoPbVecs s.sending_ct2).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : Ct2SampledEnv s evs) :
    SpqrBoundedEvs maxAllocs maxReq evs :=
  encoderIntoPbEnv_imp_spqrBoundedEvs hcnt h384 hslots henv

/-! ## 2. Relocatable `VmPreserved` Step Lemmas for Arm 10 (`+60 -> +1432 -> +1480 -> +1544 -> ret`) -/

/-- Pre-call step (`+60 -> +1432 -> lsmpl.base 375` in Block `334`) for Arm 10 (`States.ct2Sampled`,
    tag `12`, jump table index `10`), preserving `VmPreserved s1 s2`. -/
theorem states_into_pb_ct2Sampled_pre_vm_placed [LibsignalPlacement] {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
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
    (hx8 : s1.readReg64 .x8 = 12#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s1
      (memRegion (s0.sp - 480#64) 48 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbJumpTablePlacedAt ∗
       Rest)
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
           ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
           ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
           (stA ↦₆₄ 12#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
           statesIntoPbJumpTablePlacedAt ∗
           Rest)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (blkPl_334).base + 1480#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x27 = s0.sp - 1360#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  rw [ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
  cells_unfold
  wp_pull_exists
  rename_i m0 m1 m2 m3 m4 m5
  refine seq_vm_step
    (mid := (blkPl_334).base + 1432#64)
    (P_mid :=
      (((s0.sp - 480#64) ↦₆₄ m0) ∗ ((s0.sp - 472#64) ↦₆₄ m1) ∗
       ((s0.sp - 464#64) ↦₆₄ m2) ∗ ((s0.sp - 456#64) ↦₆₄ m3) ∗
       ((s0.sp - 448#64) ↦₆₄ m4) ∗ ((s0.sp - 440#64) ↦₆₄ m5)) ∗
      (stA ↦₆₄ 12#64) ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
      statesIntoPbJumpTablePlacedAt ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp - 1520#64 ∧
      sc.readReg64 .x29 = s0.sp - 96#64 ∧
      sc.readReg64 .x28 = s0.sp - 256#64 ∧
      sc.readReg64 .x27 = s0.sp - 1360#64 ∧
      sc.readReg64 .x26 = s0.sp - 480#64 ∧
      sc.readReg64 .x20 = stA ∧
      sc.readReg64 .x19 = out ∧
      TraceCalleeSaved sc s0)
    ?_ ?_
  · dsimp only [statesIntoPbJumpTablePlacedAt, statesIntoPbJumpTableBytes,
      BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  · intro sc hpcc hrunc hvmc ⟨hspc, hx29c, hx28c, hx27c, hx26c, hx20c, hx19c, htrc, hvregsc⟩
    refine SepWP.mono
      (post := fun s2 P2 =>
        VmPreserved sc s2 ∧
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
           ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
           ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
           (stA ↦₆₄ 12#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
           statesIntoPbJumpTablePlacedAt ∗
           Rest)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (blkPl_334).base + 1480#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x27 = s0.sp - 1360#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0))
      ?_
      (fun s2 _P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨hvmc.trans hvm2, hP2, hregs⟩)
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := sc) (Entails.of_eq (by sep_ac_rfl)) ?_
      wp_done)

/-- Post-call step (`+1480 -> +1544 -> ret` in Block `334`) for Arm 10 (`States.ct2Sampled`),
    transporting `A.pool lim st_enc sf` across the straight-line staging block via `VmPreserved`
    and composing with `states_into_pb_epilogue_placed`. -/
theorem states_into_pb_ct2Sampled_post_vm_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_enc : M.σ)
    (F : ShaCompress) {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (blkPl_334).base + 1480#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : sf.readReg64 .x27 = s0.sp - 1360#64)
    (hx21 : sf.readReg64 .x21 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool lim st_enc sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
       ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
       ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 432#64) 128 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       cells (s0.sp - 1512#64) 19 ∗
       memRegion (s0.sp - 1304#64) 824 ∗
       cells (s0.sp - 304#64) 6 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (fun sr Pr =>
        (Pr ⊢
          optProtoInnerStateAt A.repAlloc out (States.ct2Sampled (P := spqrPolyApi) s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTablePlacedAt ∗
          A.pool lim st_enc sr ∗ stackAt s0.sp statesIntoPbStack) ∧
        sr.sp = s0.sp ∧
        CalleeSavedPreserved s0 sr ∧
        sr.trace = s0.trace) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h824 : memRegion (s0.sp - 1304#64) 824 =
      cells (s0.sp - 1304#64) 6 ∗ memRegion (s0.sp - 1256#64) 776 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1304#64) (n := 48) (k := 776)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1304#64) 6 (by decide)]
  rw [h824]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    t0 t1 t2 t3 t4 t5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hrejoin880 :
      (((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
       ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
       ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
       ((s0.sp - 1312#64) ↦₆₄ e6) ∗
       ((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
       ((s0.sp - 1288#64) ↦₆₄ a2) ∗ ((s0.sp - 1280#64) ↦₆₄ a3) ∗
       ((s0.sp - 1272#64) ↦₆₄ a4) ∗ ((s0.sp - 1264#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 1256#64) 776 ⊢
      memRegion (s0.sp - 1360#64) 880 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 104) (k := 776)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1360#64) 13 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right e0 (Entails.sepExists_right e1
      (Entails.sepExists_right e2 (Entails.sepExists_right e3
        (Entails.sepExists_right e4 (Entails.sepExists_right e5
          (Entails.sepExists_right e6 (Entails.sepExists_right t0
            (Entails.sepExists_right t1 (Entails.sepExists_right a2
              (Entails.sepExists_right a3 (Entails.sepExists_right a4
                (Entails.sepExists_right a5 (Entails.refl _)))))))))))))
  have hrejoin176 :
      (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
       ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
       ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 432#64) 128 ⊢
      memRegion (s0.sp - 480#64) 176 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 48) (k := 128)
          (b' := s0.sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  have hstA := stA_ct2Sampled_entails_928 stA a0 a1 a2 a3 a4 a5 s.uc.epoch
  have h1480_1544 : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool lim st_enc sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
       ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
       ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 432#64) 128 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       (((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
        ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
        ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
        ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
        ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
        ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
        ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
        ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
        ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
        ((s0.sp - 1368#64) ↦₆₄ w184)) ∗
       ((((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
         ((s0.sp - 1288#64) ↦₆₄ t2) ∗ ((s0.sp - 1280#64) ↦₆₄ t3) ∗
         ((s0.sp - 1272#64) ↦₆₄ t4) ∗ ((s0.sp - 1264#64) ↦₆₄ t5)) ∗
        memRegion (s0.sp - 1256#64) 776) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt)
      (fun s2 P2 =>
        VmPreserved sf s2 ∧
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            e0 e1 e2 e3 e4 e5
            a0 a1 a2 a3 a4 a5 s.uc.epoch w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          A.pool lim st_enc sf ∗
          (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTablePlacedAt)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x800000000000000a#64 ∧
         s2.readReg64 .x21 = e6 ∧
         TraceCalleeSaved s2 s0)) := by
    have hent_post :
        stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
        epilogueStagingCells s0.sp
          e0 e1 e2 e3 e4 e5
          a0 a1 a2 a3 a4 a5 s.uc.epoch w120
          w128 w136 w144 w152 w160 w168 w176 w184
          0#64 w200 w208 w216 ∗
        ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
          ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
          ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
          ((s0.sp - 1312#64) ↦₆₄ e6) ∗
          ((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
          ((s0.sp - 1288#64) ↦₆₄ a2) ∗ ((s0.sp - 1280#64) ↦₆₄ a3) ∗
          ((s0.sp - 1272#64) ↦₆₄ a4) ∗ ((s0.sp - 1264#64) ↦₆₄ a5)) ∗
         memRegion (s0.sp - 1256#64) 776) ∗
        ((((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
          ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
          ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5)) ∗
         memRegion (s0.sp - 432#64) 128) ∗
        memRegion (s0.sp - 256#64) 160 ∗
        statesIntoPbSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗
        A.pool lim st_enc sf ∗
        (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         ((stA ↦₆₄ 12#64) ∗
          memRegion (stA + 8#64) polyEncoderSize ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
          ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
          ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
          memRegion (stA + 464#64) 464) ∗
         statesIntoPbJumpTablePlacedAt) ⊢
        stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
        epilogueStagingCells s0.sp
          e0 e1 e2 e3 e4 e5
          a0 a1 a2 a3 a4 a5 s.uc.epoch w120
          w128 w136 w144 w152 w160 w168 w176 w184
          0#64 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160 ∗
        statesIntoPbSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗
        A.pool lim st_enc sf ∗
        (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion stA chunkedStatesSize ∗
         statesIntoPbJumpTablePlacedAt) :=
      sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left hstA))))))))))
    dsimp only [epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpcf hent_post ⊢
    by_vm_steps (
      wp_steps
      refine align_entails_vm (s0 := sf) (Entails.trans (Entails.of_eq (by sep_ac_rfl)) hent_post) ?_
      wp_done)
  have hstep : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 1544#64) sf _
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            e0 e1 e2 e3 e4 e5
            a0 a1 a2 a3 a4 a5 s.uc.epoch w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          A.pool lim st_enc s2 ∗
          (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTablePlacedAt)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x800000000000000a#64 ∧
         s2.readReg64 .x21 = e6 ∧
         TraceCalleeSaved s2 s0)) :=
    SepWP.mono h1480_1544 fun s2 _P2 _ _ ⟨hvm2, hP2, hregs⟩ =>
      ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue_placed (ext := ext) A lim st_enc s0 s2 out
    e0 e1 e2 e3 e4 e5
    a0 a1 a2 a3 a4 a5 s.uc.epoch w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.mono hep fun sr Pr _ _ ⟨hPr, hspr, hcsr, htrr, _⟩ => ⟨?_, hspr, hcsr, htrr⟩
  refine Entails.trans hPr ?_
  have hout := outWords28_entails_ct2Sampled A.repAlloc out
    e0 e1 e2 e3 e4 e5 e6
    a0 a1 a2 a3 a4 a5
    w120 w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x800000000000000a#64
      e0 e1 e2 e3 e4 e5 e6
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      w120 w128 w136 w144 w152 w160 w168 w176 w184
      0#64 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool lim st_enc sr ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-! ## 3. Arm 10 (`States.ct2Sampled`, tag `12`) Relocatable Main Theorems -/

/-- Envelope-parametric relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`) on Arm 10
    (`States.ct2Sampled`, tag `12`, `+0 -> +60 -> +1432 -> +1480 -> +1544 -> ret`), valid for any
    `Env` containing `Ct2SampledEnv s`. -/
theorem states_into_pb_ct2Sampled_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct2SampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit⟩, hmem⟩
  have hfit_enc : FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_ct2) :=
    fitsEnv_encoder_of_ct2SampledEnv hEnv hfit
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ct2Sampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_placed st s0 s0 out stA (.ct2Sampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt2Sampled_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 12#64
    (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpro fun s1 hpc1 hrun1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 1304#64) 824 ∗
      memRegion (s0.sp - 480#64) 48 ∗
      memRegion (s0.sp - 432#64) 128 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    change memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 56 ∗
      memRegion (s0.sp - 1304#64) 824 ∗
      memRegion (s0.sp - 480#64) 48 ∗
      memRegion (s0.sp - 432#64) 128 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 56) (k := 1208)
          (b' := s0.sp - 1304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1304#64) (n := 824) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 48) (k := 336)
          (b' := s0.sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 432#64) (n := 128) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  have hpre_raw := states_into_pb_ct2Sampled_pre_vm_placed (ext := ext) s0 s1 out stA s
    a0 a1 a2 a3 a4 a5
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 1304#64) 824 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 256#64) 160 ∗
     statesIntoPbSavedCells s0 ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool lim st s1)
  have hpre_step : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s1 _
      (fun s2 P2 =>
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
           ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
           ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
           (stA ↦₆₄ 12#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
           statesIntoPbJumpTablePlacedAt ∗
           (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
            ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
            cells (s0.sp - 1512#64) 19 ∗
            memRegion (s0.sp - 1360#64) protoPolynomialEncoderSize ∗
            memRegion (s0.sp - 1304#64) 824 ∗
            memRegion (s0.sp - 432#64) 128 ∗
            cells (s0.sp - 304#64) 6 ∗
            memRegion (s0.sp - 256#64) 160 ∗
            statesIntoPbSavedCells s0 ∗
            polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
            authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
            memRegion (stA + 464#64) 464 ∗
            memRegion out optProtoInnerStateSize ∗
            A.pool lim st s2))) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (blkPl_334).base + 1480#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x27 = s0.sp - 1360#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) :=
    SepWP.mono hpre_raw fun s2 _P2 _ _ ⟨hvm2, hP2, hregs⟩ =>
      ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre_step fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine call_encoderIntoPb_expose_wp_placed henc_raw st (s0.sp - 1360#64) (stA + 8#64) s.sending_ct2
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hfit_enc
    (Frame :=
      ((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
      ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
      ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
      memRegion (s0.sp - 432#64) 128 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1304#64) 824 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 12#64) ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    (by sep_ac_rfl)
    (fun sf evs e0 e1 e2 e3 e4 e5 e6 hpcf hrunf hspf hcsf _hacp htrf henv => ?_)
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_2
  have hx21_f : sf.readReg64 .x21 = s.uc.epoch := hcsf.2.2.1.trans hx21_2
  have hx27_f : sf.readReg64 .x27 = s0.sp - 1360#64 := hcsf.2.2.2.2.2.2.2.2.1.trans hx27_2
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpost_step := states_into_pb_ct2Sampled_post_vm_placed (ext := ext)
    A lim (M.stepEvents evs st) F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 e0 e1 e2 e3 e4 e5 e6
    hsp0_align hpcf hrunf hspf hx29_f hx27_f hx21_f hx19_f htrf
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq ?_) hpost_step)
    (fun sr Pr _ _ ⟨hPr, hspr, hcsr, htrr⟩ =>
      ⟨⟨evs, hEnv evs henv, hPr⟩, hspr, hcsr, htrr⟩)
  simp only [arm64_norm]

/-- Tight `Ct2SampledEnv` relocatable `subroutine_ok` for Arm 10 (`States.ct2Sampled`). -/
theorem states_into_pb_ct2Sampled_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) (Ct2SampledEnv s)) :=
  states_into_pb_ct2Sampled_of_env_placed henc_raw s (fun _ h => h)

theorem states_into_pb_ct2Sampled_env_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (_hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) (Ct2SampledEnv s)) :=
  states_into_pb_ct2Sampled_env_placed henc_raw s

/-- Default `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`)
    relocatable `subroutine_ok` for Arm 10 (`States.ct2Sampled`) under explicit slot size bounds. -/
theorem states_into_pb_ct2Sampled_of_bounds_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + (encoderIntoPbVecs s.sending_ct2).length ≤ 64)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ct2Sampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (statesIntoPbVariantPlacedSpec M A lim F (.ct2Sampled s)) :=
  states_into_pb_ct2Sampled_of_env_placed henc_raw s
    (fun _ => ct2SampledEnv_imp_spqrBoundedEvs hcnt (by omega) hslots)

theorem states_into_pb_ct2Sampled_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct2SampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct2Sampled_of_env_placed henc_raw s hEnv)

theorem states_into_pb_ct2Sampled_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) (Ct2SampledEnv s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct2Sampled_env_placed henc_raw s)

theorem states_into_pb_ct2Sampled_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.ct2Sampled s) (Ct2SampledEnv s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct2Sampled_env_of_alloc_placed hA henc_raw s)

theorem states_into_pb_ct2Sampled_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + (encoderIntoPbVecs s.sending_ct2).length ≤ 64)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ct2Sampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.ct2Sampled s))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (states_into_pb_ct2Sampled_of_bounds_placed henc_raw s hcnt hslots)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget
