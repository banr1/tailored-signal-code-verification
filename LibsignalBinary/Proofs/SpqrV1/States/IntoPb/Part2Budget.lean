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
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` — Part 2: Arm 10 (`States.ct2Sampled`)

Proves `EncoderIntoPbEnv` non-free count and `SpqrBoundedEvs` bounds, defines the tight envelope
`Ct2SampledEnv`, and proves fixed-offset `RustCliAllocBudget M` contracts for Arm 10
(`States.ct2Sampled`, tag `12`, `+0 -> +60 -> +1432 -> +1480 -> +1544 -> ret`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1
  (GF16 PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit bv_sub_sub_lit
   chunkedCt2Sampled_expose epilogueStagingCells fnAddr_adrp_5ce6c
   outWords28 outWords28_entails_ct2Sampled protoPolynomialEncoderHeap
   stA_ct2Sampled_entails_928 statesIntoPbJumpTableAt
   statesIntoPbJumpTableBytes statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack statesIntoPb_fnOff)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv EncoderIntoPbOkExt
   encoderIntoPbAllocEvents encoderIntoPbSlotEvents encoderIntoPbVecs
   fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbVariantSpec statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
  (StatesIntoPbPostOfEnv call_encoderIntoPb_expose_wp
   sepWPp_of_states_into_pb_exit_of_env states_into_pb_epilogue
   states_into_pb_prologue_60 sub_ok_encoderIntoPb_raw)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

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
  bv_sub_sub_lit bv_add_add_lit
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

/-! ## 1. Re-Exports of `RustAlloc`-Generic `Part2` Helpers -/

abbrev bv_sub_sub_lit_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.bv_sub_sub_lit
abbrev bv_add_add_lit_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.bv_add_add_lit
abbrev chunkedCt2Sampled_expose_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedCt2Sampled_expose
abbrev stA_ct2Sampled_entails_928_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ct2Sampled_entails_928
abbrev outWords28_entails_ct2Sampled_generic :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ct2Sampled

/-! ## 2. Shared `EncoderIntoPbEnv` Non-Free Count & `SpqrBoundedEvs` Lemmas -/

private theorem nonFreeCount_rustAllocEvents (sz al : Nat) :
    nonFreeCount (rustAllocEvents sz al) = 1 := by
  unfold rustAllocEvents
  by_cases hc : al ≤ 16 ∧ al ≤ sz
  · simp [hc, nonFreeCount]
  · simp [hc, nonFreeCount]

private theorem spqrBoundedEvs_rustAllocEvents_384_8 :
    SpqrBoundedEvs 1 384 (rustAllocEvents 384 8) := by
  have hcond : (8 ≤ 16 ∧ 8 ≤ 384) := ⟨by decide, by decide⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, Nat.le_refl 384, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_encoderIntoPbSlotEvents (cs : List GF16) {maxReq : Nat}
    (hmax : 2 * cs.length ≤ MallocngMaxAllocSize)
    (hreq : 2 * cs.length ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (encoderIntoPbSlotEvents cs) := by
  unfold encoderIntoPbSlotEvents
  cases cs with
  | nil =>
    exact SpqrBoundedEvs.nil 1 maxReq
  | cons c rest =>
    have h1 : 1 ≤ 2 * (c :: rest).length := by simp only [List.length_cons]; omega
    have hcond : (1 ≤ 16 ∧ 1 ≤ 2 * (c :: rest).length) := ⟨by decide, h1⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      rustAllocEvents, hcond, and_self]
    refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_encoderSlots {maxReq : Nat} :
    ∀ (xss : List (List GF16)),
      (∀ cs ∈ xss, 2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq) →
      SpqrBoundedEvs xss.length maxReq (xss.flatMap encoderIntoPbSlotEvents)
  | [], _ => SpqrBoundedEvs.nil 0 maxReq
  | cs :: xss, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hcs := h cs List.mem_cons_self
    have htl := spqrBoundedEvs_flatMap_encoderSlots xss
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h1 := spqrBoundedEvs_encoderIntoPbSlotEvents cs hcs.1 hcs.2
    have happ := SpqrBoundedEvs.append h1 htl
    exact SpqrBoundedEvs.mono (by omega) (Nat.le_of_eq (Nat.max_self maxReq)) happ

private theorem nonFreeCount_encoderIntoPbSlotEvents_le (cs : List GF16) :
    nonFreeCount (encoderIntoPbSlotEvents cs) ≤ 1 := by
  unfold encoderIntoPbSlotEvents
  cases cs with
  | nil => simp [nonFreeCount]
  | cons _ _ => simp [nonFreeCount_rustAllocEvents]

private theorem nonFreeCount_flatMap_encoderSlots_le :
    ∀ (xss : List (List GF16)),
      nonFreeCount (xss.flatMap encoderIntoPbSlotEvents) ≤ xss.length
  | [] => Nat.le_refl 0
  | cs :: xss => by
    simp only [List.flatMap_cons, List.length_cons, nonFreeCount_append]
    have h1 := nonFreeCount_encoderIntoPbSlotEvents_le cs
    have h2 := nonFreeCount_flatMap_encoderSlots_le xss
    omega

theorem nonFreeCount_encoderIntoPbEnv_le {enc : PolyEncoder} {evs : List AllocEvent}
    (henv : EncoderIntoPbEnv enc evs) :
    nonFreeCount evs ≤ 2 + (encoderIntoPbVecs enc).length := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, henc_alloc, hfree⟩
  unfold EncoderIntoPbAllocEnv at henc_alloc
  subst henc_alloc
  simp only [encoderIntoPbAllocEvents, nonFreeCount_append,
    nonFreeCount_eq_zero_of_freeOnly hfree, nonFreeCount_rustAllocEvents]
  have hslots := nonFreeCount_flatMap_encoderSlots_le (encoderIntoPbVecs enc)
  omega

theorem encoderIntoPbEnv_imp_spqrBoundedEvs {enc : PolyEncoder}
    {maxAllocs maxReq : Nat} {evs : List AllocEvent}
    (hcnt : 2 + (encoderIntoPbVecs enc).length ≤ maxAllocs)
    (h384 : 384 ≤ maxReq)
    (hslots : ∀ cs ∈ encoderIntoPbVecs enc,
      2 * cs.length ≤ MallocngMaxAllocSize ∧ 2 * cs.length ≤ maxReq)
    (henv : EncoderIntoPbEnv enc evs) :
    SpqrBoundedEvs maxAllocs maxReq evs := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, henc_alloc, hfree⟩
  unfold EncoderIntoPbAllocEnv at henc_alloc
  subst henc_alloc
  have hout1 : SpqrBoundedEvs 1 maxReq (rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 1) h384 spqrBoundedEvs_rustAllocEvents_384_8
  have hout12 : SpqrBoundedEvs 2 maxReq (rustAllocEvents 384 8 ++ rustAllocEvents 384 8) :=
    SpqrBoundedEvs.mono (Nat.le_refl 2) (Nat.le_of_eq (Nat.max_self maxReq))
      (SpqrBoundedEvs.append hout1 hout1)
  have hsl : SpqrBoundedEvs (encoderIntoPbVecs enc).length maxReq
      ((encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents) :=
    spqrBoundedEvs_flatMap_encoderSlots (encoderIntoPbVecs enc) hslots
  have hfr : SpqrBoundedEvs 0 maxReq evs_free :=
    SpqrBoundedEvs.mono (Nat.le_refl 0) (Nat.zero_le maxReq) (SpqrBoundedEvs.of_freeOnly hfree)
  have halloc := SpqrBoundedEvs.append hout12 hsl
  have htot := SpqrBoundedEvs.append halloc hfr
  exact SpqrBoundedEvs.mono (by omega) (by omega) htot

/-! ## 3. Arm 10 (`States.ct2Sampled`, tag `12`) Envelope, Steppers, and Main Theorems -/

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 10 (`States.ct2Sampled`, tag `12`):
    delegates solely to `<PolyEncoder>::into_pb` on `s.sending_ct2`. -/
abbrev Ct2SampledEnv {F : ShaCompress}
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  EncoderIntoPbEnv s.sending_ct2

/-- Pool-preserving pre-call stepper (`+60 -> +1432 -> +23100`) for Arm 10 (`States.ct2Sampled`). -/
theorem states_into_pb_ct2Sampled_pre {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
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
    (hx8 : s1.readReg64 .x8 = 12#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64) s1
      (memRegion (s0.sp - 480#64) 48 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbJumpTableAt b ∗
       Rest)
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
           statesIntoPbJumpTableAt b ∗
           Rest)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1480#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x27 = s0.sp - 1360#64 ∧
        s2.readReg64 .x21 = s.uc.epoch ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0 ∧
        VmPreserved s1 s2) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hwp : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64) s1
      (memRegion (s0.sp - 480#64) 48 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbJumpTableAt b ∗
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
           statesIntoPbJumpTableAt b ∗
           Rest)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1480#64 ∧
         s2.readReg64 .x0 = s0.sp - 1360#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x27 = s0.sp - 1360#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) := by
    rw [ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
    cells_unfold
    wp_pull_exists
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [hfn_eq] at hpc1 ⊢
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    have hadrp := fnAddr_adrp_5ce6c (H := trapHooks) hb
    dsimp only [statesIntoPbName] at hadrp
    into_pb_fetches_range b trapHooks 60 80
    into_pb_fetches_range b trapHooks 1432 48
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (s0 := s1) ?_ ?_
    · exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  refine SepWP.mono hwp
    fun s2 P2 _ _ ⟨hvm2, hP2, hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2⟩ =>
      ⟨hP2, hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2, hvm2⟩

/-- Pool-synchronized post-call stepper (`+1480 -> +1544 -> ret`) for Arm 10 (`States.ct2Sampled`). -/
theorem states_into_pb_ct2Sampled_post
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (st : M.σ) (evs : List AllocEvent) (hEnv : Env evs)
    (s0 sf : State) (out stA : BitVec 64)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1480#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : sf.readReg64 .x27 = s0.sp - 1360#64)
    (hx21 : sf.readReg64 .x21 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
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
       statesIntoPbJumpTableAt b)
      (StatesIntoPbPostOfEnv A lim b st s0 out stA (.ct2Sampled s) Env) := by
  rcases htrf with ⟨htrf, hvregs⟩
  let st' : M.σ := M.stepEvents evs st
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h824 : memRegion (s0.sp - 1304#64) 824 =
      cells (s0.sp - 1304#64) 6 ∗ memRegion (s0.sp - 1256#64) 776 := by
    have hsplit : memRegion (s0.sp - 1304#64) 824 =
        memRegion (s0.sp - 1304#64) 48 ∗ memRegion (s0.sp - 1256#64) 776 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [hsplit, ProofLib.memRegion_cells (s0.sp - 1304#64) 6 (by decide)]
  rw [h824]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    t0 t1 t2 t3 t4 t5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
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
    have hsplit : memRegion (s0.sp - 1360#64) 880 =
        memRegion (s0.sp - 1360#64) 104 ∗ memRegion (s0.sp - 1256#64) 776 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [hsplit, ProofLib.memRegion_cells (s0.sp - 1360#64) 13 (by decide)]
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
    have hsplit : memRegion (s0.sp - 480#64) 176 =
        memRegion (s0.sp - 480#64) 48 ∗ memRegion (s0.sp - 432#64) 128 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [hsplit, ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
    refine sepConj_mono_left ?_
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  have hstA := stA_ct2Sampled_entails_928 stA a0 a1 a2 a3 a4 a5 s.uc.epoch
  have hcombine :
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
      A.pool lim st' sf ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       ((stA ↦₆₄ 12#64) ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (stA + 464#64) 464) ∗
       statesIntoPbJumpTableAt b) ⊢
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
      A.pool lim st' sf ∗
      (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
       authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hrejoin880
        (sepConj_mono hrejoin176
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left hstA))))))))))
  have hstep_vm : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool lim st' sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
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
       statesIntoPbJumpTableAt b)
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
          A.pool lim st' sf ∗
          (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
           authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTableAt b)) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x19 = out ∧
         s2.readReg64 .x22 = 0x800000000000000a#64 ∧
         s2.readReg64 .x21 = e6 ∧
         TraceCalleeSaved s2 s0)) := by
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpcf ⊢
    rw [hfn_eq] at hpcf ⊢
    apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
    into_pb_fetches_range b trapHooks 1480 64
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_entails_vm (s0 := sf) (Entails.trans ?_ hcombine) ?_
    · dsimp only [epilogueStagingCells]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  have hstep := SepWP.mono
    (post' := fun s2 P2 =>
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
        A.pool lim st' s2 ∗
        (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion stA chunkedStatesSize ∗
         statesIntoPbJumpTableAt b)) ∧
      (s2.sp = s0.sp - 1520#64 ∧
       s2.readReg64 .x29 = s0.sp - 96#64 ∧
       s2.readReg64 .x19 = out ∧
       s2.readReg64 .x22 = 0x800000000000000a#64 ∧
       s2.readReg64 .x21 = e6 ∧
       TraceCalleeSaved s2 s0))
    hstep_vm
    fun s2 P2 _ _ ⟨hvm2, hP2, hregs⟩ => ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue A lim st' s0 s2 out
    e0 e1 e2 e3 e4 e5
    a0 a1 a2 a3 a4 a5 s.uc.epoch w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  refine SepWP.mono hep fun s_ret Pf _ _ ⟨hPf, hsp_ret, hcs_ret, htr_ret, _⟩ => ?_
  refine ⟨⟨evs, hEnv, Entails.trans hPf ?_⟩, hsp_ret, hcs_ret, htr_ret⟩
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
     statesIntoPbJumpTableAt b ∗ A.pool lim st' s_ret ∗ stackAt s0.sp statesIntoPbStack) by sep_ac_rfl)) ?_
  exact sepConj_mono_left hout

/-- Envelope-parametric `subroutine_ok` for `<States>::into_pb` on Arm 10 (`States.ct2Sampled`, tag `12`),
    valid for any `Env` containing `Ct2SampledEnv s` (`EncoderIntoPbEnv s.sending_ct2`). -/
theorem states_into_pb_ct2Sampled_of_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, Ct2SampledEnv s evs → Env evs) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct2Sampled s) Env) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb, hfit⟩, hmem⟩
  have hfit_enc : FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_ct2) :=
    fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv (FitsEnv.mono hEnv hfit)
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.ct2Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_of_env st s0 s0 out stA (.ct2Sampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedCt2Sampled_expose A.repAlloc stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
          (stA ↦₆₄ 12#64) ∗
          polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
          ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
          ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          memRegion (stA + 464#64) 464) ∗
        statesIntoPbJumpTableAt b ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 12#64) ∗
        A.pool lim st s0 ∗
        (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
         ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
         authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 464#64) 464 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTableAt b) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpull ?_
  refine SepWP.exists_elim fun a0 => SepWP.exists_elim fun a1 =>
    SepWP.exists_elim fun a2 => SepWP.exists_elim fun a3 =>
    SepWP.exists_elim fun a4 => SepWP.exists_elim fun a5 => ?_
  have hpro := states_into_pb_prologue_60 A lim st s0 out stA 12#64
    (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_ct2 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b)
    hsp0_align hpc hrun hx8 hx0
  refine seq_clean_wp hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_
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
    have hs1 : memRegion (s0.sp - 1512#64) 1416 =
        memRegion (s0.sp - 1512#64) 152 ∗ memRegion (s0.sp - 1360#64) 1264 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have hs2 : memRegion (s0.sp - 1360#64) 1264 =
        memRegion (s0.sp - 1360#64) 56 ∗ memRegion (s0.sp - 1304#64) 1208 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have hs3 : memRegion (s0.sp - 1304#64) 1208 =
        memRegion (s0.sp - 1304#64) 824 ∗ memRegion (s0.sp - 480#64) 384 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have hs4 : memRegion (s0.sp - 480#64) 384 =
        memRegion (s0.sp - 480#64) 48 ∗ memRegion (s0.sp - 432#64) 336 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have hs5 : memRegion (s0.sp - 432#64) 336 =
        memRegion (s0.sp - 432#64) 128 ∗ memRegion (s0.sp - 304#64) 208 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    have hs6 : memRegion (s0.sp - 304#64) 208 =
        memRegion (s0.sp - 304#64) 48 ∗ memRegion (s0.sp - 256#64) 160 :=
      ProofLib.memRegion_split' rfl (by bv_omega) (by decide)
    rw [hs1, hs2, hs3, hs4, hs5, hs6,
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  have hpre_step := states_into_pb_ct2Sampled_pre s0 s1 out stA s a0 a1 a2 a3 a4 a5
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
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
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp hpre_step fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2, hvm12⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine call_encoderIntoPb_expose_wp henc_raw st (s0.sp - 1360#64) (stA + 8#64) s.sending_ct2
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hfit_enc
    (by dsimp only [spqrPolyApi]; rw [A.pool_of_vmPreserved hvm12]; sep_focus)
    (fun sf evs e0 e1 e2 e3 e4 e5 e6 hpcf hrunf hspf hcsf _hacpf htrf henv_enc => ?_)
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_2
  have hx21_f : sf.readReg64 .x21 = s.uc.epoch := hcsf.2.2.1.trans hx21_2
  have hx27_f : sf.readReg64 .x27 = s0.sp - 1360#64 := hcsf.2.2.2.2.2.2.2.2.1.trans hx27_2
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpost_step := states_into_pb_ct2Sampled_post A lim F st evs (hEnv evs henv_enc)
    s0 sf out stA s a0 a1 a2 a3 a4 a5 e0 e1 e2 e3 e4 e5 e6
    hsp0_align hpcf hrunf hspf hx29_f hx27_f hx21_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  sep_ac_rfl

/-- Tight `Ct2SampledEnv` `subroutine_ok` for Arm 10 (`States.ct2Sampled`). -/
theorem states_into_pb_ct2Sampled_env
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct2Sampled s) (Ct2SampledEnv s)) :=
  states_into_pb_ct2Sampled_of_env henc s (fun _ h => h)

theorem states_into_pb_ct2Sampled_env_of_alloc
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (_hA : AllocContractsBudget b M A lim ext)
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpecOfEnv M A lim F b (.ct2Sampled s) (Ct2SampledEnv s)) :=
  states_into_pb_ct2Sampled_env henc s

/-- Default `statesIntoPbVariantSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`) `subroutine_ok`
    for Arm 10 (`States.ct2Sampled`) under explicit slot size bounds. -/
theorem states_into_pb_ct2Sampled_of_bounds
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b M A lim ext)
    (s : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + (encoderIntoPbVecs s.sending_ct2).length ≤ 64)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_ct2,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.ct2Sampled s).into_pb).length + 1024) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (.ct2Sampled s)) :=
  states_into_pb_ct2Sampled_of_env henc s
    (fun _ => encoderIntoPbEnv_imp_spqrBoundedEvs hcnt (by omega) hslots)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2Budget
