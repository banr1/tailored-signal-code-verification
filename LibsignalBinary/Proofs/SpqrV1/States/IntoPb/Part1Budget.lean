/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` — Part 1: Prologue, Epilogue, Arm 0 (`keysUnsampled`), and Call Helpers

Fixed-offset `RustCliAllocBudget M` prologue/epilogue lemmas, Arm 0 (`States.keysUnsampled`, tag `2`,
`evs = []`) contracts under `KeysUnsampledEnv`, and budget-threaded call helpers for
`<PolyEncoder>::into_pb` and `<PolyDecoder>::into_pb`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet (memcpyName tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderAt protoPolynomialDecoderSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbName decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbName encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved chunkedKeysUnsampled_expose epilogueStagingCells
   epilogueStagingCells_entails_memRegion fnAddr_adrp_5ce6c fnAddr_fwd_eq
   libsignalSessionCode_fnOff_decoderIntoPb libsignalSessionCode_fnOff_encoderIntoPb
   libsignalSessionCode_fnOff_memcpy memRegion_out_224_eq outWords28
   outWords28_entails_keysUnsampled protoPolynomialDecoderHeap
   protoPolynomialDecoder_expose protoPolynomialEncoderHeap
   protoPolynomialEncoder_expose sp_sub_1520_add_1424 sp_sub_480_add_200
   sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
   sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168
   sp_sub_96_sub_176 sp_sub_96_sub_192 sp_sub_96_sub_208
   stA_words8_and_864_entails_928 stackAt_encoderIntoPb_eq_decoderIntoPb
   stackAt_statesIntoPb_split_96 stackAt_statesIntoPb_split_fsp
   stack_restore_statesIntoPb statesIntoPbJumpTableAt statesIntoPbJumpTableBytes
   statesIntoPbName statesIntoPbSavedCells statesIntoPbStack statesIntoPb_fnOff)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbOkExt decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv EncoderIntoPbOkExt encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (SpqrBoundedEvs statesIntoPbVariantSpec statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

private theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

local macro "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| (
      code_fetches_range CryptoVerification.libsignalSessionCode
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbBin
        $b $H CryptoVerification.SpqrV1.States.IntoPb.statesIntoPb_fnOff
        (ls_off% "<spqr::v1::chunked::states::States>::into_pb") $k0 $len
      lift_fetches_withSvc))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160
  sp_sub_1520_add_1424
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

/-! ## 1. Re-Exports of `RustAlloc`-Generic `Part1` Helpers -/

abbrev vecU8Payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Payload
abbrev vecU8At_eq_header_payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8At_eq_header_payload
abbrev vecU8_of_header_payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_of_header_payload
abbrev authenticatorHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorHeap
abbrev authenticatorAt_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorAt_expose
abbrev authenticatorAt_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorAt_of_words_heap
abbrev vecU8Heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Heap
abbrev vecU8_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_expose
abbrev vecU8_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_of_words_heap
abbrev protoPolynomialEncoderHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoderHeap
abbrev protoPolynomialEncoder_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoder_expose
abbrev protoPolynomialEncoder_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoder_of_words_heap
abbrev protoPolynomialDecoderHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoderHeap
abbrev protoPolynomialDecoder_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoder_expose
abbrev protoPolynomialDecoder_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoder_of_words_heap
abbrev chunkedKeysUnsampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedKeysUnsampled_expose
abbrev stA_words8_and_864_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_words8_and_864_entails_928
abbrev outWords28_entails_keysUnsampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_keysUnsampled
abbrev libsignalSessionCode_fnOff_encoderIntoPb :=
  @CryptoVerification.SpqrV1.States.IntoPb.libsignalSessionCode_fnOff_encoderIntoPb
abbrev libsignalSessionCode_fnOff_decoderIntoPb :=
  @CryptoVerification.SpqrV1.States.IntoPb.libsignalSessionCode_fnOff_decoderIntoPb
abbrev libsignalSessionCode_fnOff_memcpy :=
  @CryptoVerification.SpqrV1.States.IntoPb.libsignalSessionCode_fnOff_memcpy
abbrev fnAddr_fwd_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.fnAddr_fwd_eq
abbrev statesIntoPb_seq_sepWP :=
  @CryptoVerification.SpqrV1.States.IntoPb.statesIntoPb_seq_sepWP

/-! ## 2. Pool-Synchronized Fixed-Offset Prologue, Extended Prologue, Epilogue, and Exit Bridges -/

/-- Pool-synchronized fixed-offset prologue (`+0 -> +44`, `0x5ce20 -> 0x5ce4c`). -/
theorem states_into_pb_prologue
    {M : AllocCostModel} {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (out stA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 44#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗ A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 1520#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x28 = s0.sp - 256#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x0 = stA ∧
        s1.trace = s0.trace ∧
        VmPreserved s0 s1) := by
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      cells (s0.sp - 1520#64) 1 ∗
      memRegion (s0.sp - 1512#64) 1416 := by
    have h0 : memRegion (s0.sp - 1520#64) 1424 =
        memRegion (s0.sp - 1520#64) 8 ∗ memRegion (s0.sp - 1512#64) 1416 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [h0, ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 44#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗ A.pool lim st s0 ∗ Rest) ∧
        (s1.sp = s0.sp - 1520#64 ∧
         s1.readReg64 .x29 = s0.sp - 96#64 ∧
         s1.readReg64 .x28 = s0.sp - 256#64 ∧
         s1.readReg64 .x19 = out ∧
         s1.readReg64 .x0 = stA ∧
         s1.trace = s0.trace)) := by
    rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp]
    nth_rw 1 [hsplit_1424]
    cells_unfold
    wp_pull_exists
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [hfn_eq] at hpc
    conv => enter [2]; rw [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 0 44
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm ?_ ?_
    · unfold statesIntoPbSavedCells
      dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hvm1, hP1, hsp1, hx29, hx28, hx19, hx0_1, htr1⟩ => ?_
  refine ⟨?_, hsp1, hx29, hx28, hx19, hx0_1, htr1, hvm1⟩
  rw [A.pool_of_vmPreserved hvm1]
  exact hP1

/-- Pool-synchronized fixed-offset extended prologue (`+0 -> +60`, `0x5ce20 -> 0x5ce5c`). -/
theorem states_into_pb_prologue_60
    {M : AllocCostModel} {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (out stA tag : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ tag) ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ tag) ∗ A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 1520#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x28 = s0.sp - 256#64 ∧
        s1.readReg64 .x27 = s0.sp - 1360#64 ∧
        s1.readReg64 .x26 = s0.sp - 480#64 ∧
        s1.readReg64 .x20 = stA ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x8 = tag ∧
        TraceCalleeSaved s1 s0 ∧
        VmPreserved s0 s1) := by
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      cells (s0.sp - 1520#64) 1 ∗
      memRegion (s0.sp - 1512#64) 1416 := by
    have h0 : memRegion (s0.sp - 1520#64) 1424 =
        memRegion (s0.sp - 1520#64) 8 ∗ memRegion (s0.sp - 1512#64) 1416 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [h0, ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ tag) ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ tag) ∗ A.pool lim st s0 ∗ Rest) ∧
        (s1.sp = s0.sp - 1520#64 ∧
         s1.readReg64 .x29 = s0.sp - 96#64 ∧
         s1.readReg64 .x28 = s0.sp - 256#64 ∧
         s1.readReg64 .x27 = s0.sp - 1360#64 ∧
         s1.readReg64 .x26 = s0.sp - 480#64 ∧
         s1.readReg64 .x20 = stA ∧
         s1.readReg64 .x19 = out ∧
         s1.readReg64 .x8 = tag ∧
         TraceCalleeSaved s1 s0)) := by
    rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp]
    nth_rw 1 [hsplit_1424]
    cells_unfold
    wp_pull_exists
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [hfn_eq] at hpc
    conv => enter [2]; rw [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 0 60
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm ?_ ?_
    · unfold statesIntoPbSavedCells
      dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  refine SepWP.mono hwp
    fun s1 P1 _ _ ⟨hvm1, hP1, hsp1, hx29, hx28, hx27, hx26, hx20, hx19, hx8_1, htr1⟩ => ?_
  refine ⟨?_, hsp1, hx29, hx28, hx27, hx26, hx20, hx19, hx8_1, htr1, hvm1⟩
  rw [A.pool_of_vmPreserved hvm1]
  exact hP1

/-- Pool-synchronized fixed-offset common epilogue (`+1544 -> s0.readReg64 .x30`). -/
theorem states_into_pb_epilogue
    {M : AllocCostModel} {b : BitVec 64} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       A.pool lim st s ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          outWords28 out
            (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            w192 w200 w208 w216 ∗
          stackAt s0.sp statesIntoPbStack ∗
          A.pool lim st sf ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace ∧
        VmPreserved s sf) := by
  rcases htr with ⟨htr, hvregs⟩
  let Rest' : SepProp := A.pool lim st s ∗ Rest
  have hrestore :
      outWords28 out
        (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216 ∗
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       (epilogueStagingCells s0.sp
          w8 w16 w24 w32 w40 w48
          w64 w72 w80 w88 w96 w104 w112 w120
          w128 w136 w144 w152 w160 w168 w176 w184
          w192 w200 w208 w216 ∗
        memRegion (s0.sp - 1360#64) 880 ∗
        memRegion (s0.sp - 480#64) 176 ∗
        memRegion (s0.sp - 256#64) 160) ∗
       statesIntoPbSavedCells s0) ∗
      Rest' ⊢
      outWords28 out
        (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216 ∗
      stackAt s0.sp statesIntoPbStack ∗
      Rest' := by
    refine sepConj_mono_right (sepConj_mono_left ?_)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (epilogueStagingCells_entails_memRegion s0.sp
        w8 w16 w24 w32 w40 w48
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216))) ?_
    exact stack_restore_statesIntoPb s0
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
       epilogueStagingCells s0.sp
         w8 w16 w24 w32 w40 w48
         w64 w72 w80 w88 w96 w104 w112 w120
         w128 w136 w144 w152 w160 w168 w176 w184
         w192 w200 w208 w216 ∗
       memRegion (s0.sp - 1360#64) 880 ∗
       memRegion (s0.sp - 480#64) 176 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗
       Rest')
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          outWords28 out
            (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            w192 w200 w208 w216 ∗
          stackAt s0.sp statesIntoPbStack ∗
          Rest') ∧
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace)) := by
    rw [memRegion_out_224_eq out]
    wp_pull_exists
    conv => arg 4; dsimp only [outWords28, epilogueStagingCells, statesIntoPbSavedCells]
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [hfn_eq] at hpc
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 1544 100
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (Entails.trans ?_ hrestore) ?_
    · dsimp only [outWords28, epilogueStagingCells, statesIntoPbSavedCells,
        Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hvm_f, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
  refine ⟨?_, hsp_f, hcs_f, htr_f, hvm_f⟩
  rw [A.pool_of_vmPreserved hvm_f]
  exact hPf

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` (with existential `evs` satisfying `Env`)
    into a `SepWPp` for `statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env`. -/
theorem sepWPp_of_states_into_pb_exit_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
            memRegion stA chunkedStatesSize ∗
            statesIntoPbJumpTableAt b ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).post ((out, stA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).onPanic ((out, stA), st) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨⟨evs, henv, hPf⟩, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesIntoPbVariantSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

theorem sepWPp_of_states_into_pb_exit
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (h : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024) evs ∧
          (Pf ⊢
            optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
            memRegion stA chunkedStatesSize ∗
            statesIntoPbJumpTableAt b ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantSpec M A lim F b stateVal).post ((out, stA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec M A lim F b stateVal).onPanic ((out, stA), st) s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_exit_of_env st s0 s out stA stateVal _ P R h

/-- Envelope-parametric return postcondition of `<States>::into_pb` for `SepWPp`. -/
def StatesIntoPbPostOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {F : ShaCompress} (b : BitVec 64) (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent, Env evs ∧
      (Pf ⊢
        optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
        memRegion stA chunkedStatesSize ∗
        statesIntoPbJumpTableAt b ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

/-- Default-envelope return postcondition of `<States>::into_pb` for `SepWPp`. -/
abbrev StatesIntoPbPost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {F : ShaCompress} (b : BitVec 64) (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  StatesIntoPbPostOfEnv A lim b st s0 out stA stateVal
    (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024))

/-- Non-panicking (`onPanic = ⌜False⌝`) panic postcondition of budget `<States>::into_pb` for `SepWPp`. -/
def StatesIntoPbNoPanic (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)

/-- Bridge from `SepWPp` with `StatesIntoPbPostOfEnv` / `StatesIntoPbNoPanic` to the
    `subroutine_ok_of_sepWPp` goal for `statesIntoPbVariantSpecOfEnv`. -/
theorem sepWPp_of_states_into_pb_wpp_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (hwpp : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (StatesIntoPbPostOfEnv A lim b st s0 out stA stateVal Env)
      (StatesIntoPbNoPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpecOfEnv M A lim F b stateVal Env).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, henv, hent⟩, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    dsimp only [statesIntoPbVariantSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hent) (Entails.of_eq (by sep_ac_rfl))) hmR⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR
    exact hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_states_into_pb_wpp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (P R : SepProp)
    (hwpp : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (StatesIntoPbPost A lim b st s0 out stA stateVal)
      (StatesIntoPbNoPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec M A lim F b stateVal).post ⟨(out, stA), st⟩ s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantSpec M A lim F b stateVal).onPanic ⟨(out, stA), st⟩ s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_wpp_of_env st s0 s out stA stateVal _ P R hwpp

/-! ## 3. Arm 0: `States.keysUnsampled` (`+0 -> +60 -> +100 -> +1544 -> ret`, `evs = []`) -/

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 0 (`States.keysUnsampled`):
    zero heap allocations or deallocations (`evs = []`). -/
def KeysUnsampledEnv (evs : List AllocEvent) : Prop :=
  evs = []

theorem states_into_pb_keysUnsampled_arm
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s1 : State) (out stA : BitVec 64)
    (s : KeysUnsampled (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
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
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
       statesIntoPbJumpTableAt b ∗
       A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          optProtoInnerStateAt A.repAlloc out (States.keysUnsampled (P := spqrPolyApi) s).into_pb.innerState ∗
          memRegion stA chunkedStatesSize ∗
          statesIntoPbJumpTableAt b ∗
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
    have h1 : memRegion (s0.sp - 1512#64) 1416 =
        memRegion (s0.sp - 1512#64) 152 ∗ memRegion (s0.sp - 1360#64) 1264 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have h2 : memRegion (s0.sp - 1360#64) 1264 =
        memRegion (s0.sp - 1360#64) 880 ∗ memRegion (s0.sp - 480#64) 384 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have h3 : memRegion (s0.sp - 480#64) 384 =
        memRegion (s0.sp - 480#64) 176 ∗ memRegion (s0.sp - 304#64) 208 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have h4 : memRegion (s0.sp - 304#64) 208 =
        memRegion (s0.sp - 304#64) 48 ∗ memRegion (s0.sp - 256#64) 160 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [h1, h2, h3, h4,
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hstep1_vm : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) s1
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
       statesIntoPbJumpTableAt b ∗
       A.pool lim st s1)
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
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
           statesIntoPbJumpTableAt b)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x8000000000000000#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         TraceCalleeSaved s2 s0)) := by
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [hfn_eq] at hpc1
    conv => enter [2]; rw [hfn_eq]
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    have hadrp := fnAddr_adrp_5ce6c (H := trapHooks) hb
    dsimp only [statesIntoPbName] at hadrp
    into_pb_fetches_range b trapHooks 60 80
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (s0 := s1) ?_ ?_
    · dsimp only [epilogueStagingCells]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  have hstep1 := SepWP.mono
    (post' := fun s2 P2 =>
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
         statesIntoPbJumpTableAt b)) ∧
      (s2.sp = s0.sp - 1520#64 ∧
       s2.readReg64 .x29 = s0.sp - 96#64 ∧
       s2.readReg64 .x19 = out ∧
       s2.readReg64 .x22 = 0x8000000000000000#64 ∧
       s2.readReg64 .x21 = s.uc.epoch ∧
       TraceCalleeSaved s2 s0))
    hstep1_vm
    fun s2 P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine seq_clean_wp hstep1 fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_
  have hep := states_into_pb_epilogue A lim st s0 s2 out
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
     statesIntoPbJumpTableAt b)
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
    statesIntoPbJumpTableAt b ∗ A.pool lim st sf ∗ stackAt s0.sp statesIntoPbStack by sep_ac_rfl)) ?_
  exact sepConj_mono hout (sepConj_mono_left hstA)

/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` on Arm 0 (`States.keysUnsampled`),
    valid for any `Env` containing `[]`. -/
theorem states_into_pb_keysUnsampled_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (s : KeysUnsampled (spqrAuthApi F))
    (hEnv : Env []) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.keysUnsampled s) Env) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb, _hfit⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.keysUnsampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_of_env st s0 s0 out stA (.keysUnsampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedKeysUnsampled_expose A.repAlloc stA s))) ?_
  wp_pull_exists
  rename_i a0 a1 a2 a3 a4 a5
  have hpro := states_into_pb_prologue_60 A lim st s0 out stA 2#64
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 64#64) 864 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre ?_ (seq_clean_wp hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  · exact Entails.of_eq (by dsimp only [authenticatorHeap]; sep_ac_rfl)
  · have harm := states_into_pb_keysUnsampled_arm (A := A) (lim := lim)
      st s0 s1 out stA s a0 a1 a2 a3 a4 a5
      hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    refine SepWP.weaken_pre ?_ (SepWP.mono harm fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨⟨[], hEnv, hPf⟩, hspf, hcsf, htrf⟩)
    exact Entails.of_eq (by dsimp only [authenticatorHeap]; sep_ac_rfl)

/-- Tight `KeysUnsampledEnv` (`evs = []`) `subroutine_ok` for Arm 0 (`States.keysUnsampled`). -/
theorem states_into_pb_keysUnsampled_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.keysUnsampled s) KeysUnsampledEnv) :=
  states_into_pb_keysUnsampled_of_env s rfl

/-- Default `statesIntoPbVariantSpec` `subroutine_ok` for Arm 0 (`States.keysUnsampled`). -/
theorem states_into_pb_keysUnsampled
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (.keysUnsampled s)) :=
  states_into_pb_keysUnsampled_of_env s (SpqrBoundedEvs.nil 64 _)

/-! ## 4. Budget Callee Call Helpers (`encoderIntoPb`, `decoderIntoPb`, `memcpy`) -/

theorem sub_ok_of_addr_eq {α : Type} {P : Program} {a1 a2 : BitVec 64} {S : Spec α}
    (heq : a1 = a2) (h : subroutine_ok P a1 S) : subroutine_ok P a2 S :=
  heq ▸ h

theorem sub_ok_encoderIntoPb_raw
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec M A lim) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 23100) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_encoderIntoPb (by decide)).symm
    henc

theorem sub_ok_decoderIntoPb_raw
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec M A lim) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 25104) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_decoderIntoPb (by decide)).symm
    hdec

theorem sub_ok_memcpy_raw {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      sessionMemcpyRegionBudgetSpec :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq
      (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_memcpy (by decide)).symm
    hmemcpy

/-- Total-correctness (`SepWP`) call helper for budget `<PolyEncoder>::into_pb` (`+23100#64`),
    threading `M.stepEvents evs st`, `AllocCallPreserved`, and `EncoderIntoPbEnv enc evs`, and
    exposing `e0..e6` + `protoPolynomialEncoderHeap`. -/
theorem call_encoderIntoPb_expose_wp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec M A lim))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
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
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
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

/-- Call budget `<PolyEncoder>::into_pb` (`+23100#64`) inside `SepWPp`, threading `M.stepEvents evs st`,
    `AllocCallPreserved`, and `EncoderIntoPbEnv enc evs`, and exposing `e0..e6` +
    `protoPolynomialEncoderHeap`. Parametric in `{Q Qp : State → SepProp → Prop}`. -/
theorem call_encoderIntoPb_expose
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec M A lim))
    (st : M.σ) (outEncA encA : BitVec 64) (enc : PolyEncoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  refine call_encoderIntoPb_expose_wp henc_raw st outEncA encA enc
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hfit hsplit ?_
  intro sf evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspf hcsm hacp htrf henv
  exact SepWP.done hpcm hrunm fun _ =>
    hnext sf evs e0 e1 e2 e3 e4 e5 e6 hpcm hrunm hspf hcsm hacp htrf henv

/-- Total-correctness (`SepWP`) call helper for budget `<PolyDecoder>::into_pb` (`+25104#64`),
    splitting/restoring `stackAt (s0.sp - 1520#64) encoderIntoPbStack`, threading
    `M.stepEvents evs st`, `AllocCallPreserved`, and `DecoderIntoPbEnv dec evs`, and exposing
    `d0..d4` + `protoPolynomialDecoderHeap`. -/
theorem call_decoderIntoPb_expose_wp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec M A lim))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
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
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
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

/-- Call budget `<PolyDecoder>::into_pb` (`+25104#64`) inside `SepWPp`, splitting/restoring
    `stackAt (s0.sp - 1520#64) encoderIntoPbStack`, threading `M.stepEvents evs st`,
    `AllocCallPreserved`, and `DecoderIntoPbEnv dec evs`, and exposing `d0..d4` +
    `protoPolynomialDecoderHeap`. Parametric in `{Q Qp : State → SepProp → Prop}`. -/
theorem call_decoderIntoPb_expose
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec M A lim))
    (st : M.σ) (outDecA decA : BitVec 64) (dec : PolyDecoder)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q Qp := by
  refine SepWPp.seq_frozen (mid := ret_pc) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  refine call_decoderIntoPb_expose_wp hdec_raw st outDecA decA dec
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hfit hsplit ?_
  intro sf evs d0 d1 d2 d3 d4 hpcm hrunm hspf hcsm hacp htrf henv
  exact SepWP.done hpcm hrunm fun _ =>
    hnext sf evs d0 d1 d2 d3 d4 hpcm hrunm hspf hcsm hacp htrf henv

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
