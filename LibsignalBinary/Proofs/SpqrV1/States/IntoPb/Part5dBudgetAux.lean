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
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5d
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Shared `RustCliAllocBudget` Helpers for Arms 7 & 8

Shared allocator envelopes (`Ct1CloneAllocEnv`, `Ct1CloneAndDropEnv`, `Ct1SampledEnv`,
`EkReceivedCt1SampledEnv`), `VmPreserved` prologue/epilogue wrappers, and `<PolyEncoder>::into_pb` /
`<PolyDecoder>::into_pb` call-and-expose helpers for Arms 7 (`States.ct1Sampled`) and 8
(`States.ekReceivedCt1Sampled`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalSpqrV1 (
  PolyDecoder PolyEncoder States spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled EkReceivedCt1Sampled)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoInnerStateAt optProtoInnerStateSize sub_ok_of_addr_eq vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
  protoPolynomialDecoderAt protoPolynomialDecoderSize
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb (
  StatesIntoPbGhost StatesIntoPbPanic TraceCalleeSaved
  bv_add_add_lit' bv_sub_sub_lit'
  epilogueStagingCells epilogueStagingCells_entails_memRegion fnAddr_fwd_eq
  libsignalSessionCode_fnOff_decoderIntoPb libsignalSessionCode_fnOff_encoderIntoPb
  memRegion_out_224_eq outWords28
  protoPolynomialDecoderHeap protoPolynomialDecoder_expose
  protoPolynomialEncoderHeap protoPolynomialEncoder_expose
  sp_sub_1520_add_1424 sp_sub_480_add_200
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168 sp_sub_96_sub_176
  sp_sub_96_sub_192 sp_sub_96_sub_208
  stackAt_encoderIntoPb_eq_decoderIntoPb stackAt_statesIntoPb_split_96
  stackAt_statesIntoPb_split_fsp stack_restore_statesIntoPb
  statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
  statesIntoPbStack statesIntoPb_fnOff
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (
  DecoderIntoPbAllocEnv DecoderIntoPbEnv DecoderIntoPbOkExt
  decoderIntoPbSpec fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (
  EncoderIntoPbAllocEnv EncoderIntoPbEnv EncoderIntoPbOkExt
  encoderIntoPbSpec fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (
  ct1CloneEvents ct1DeallocEvents freeOnlyEvs_ct1DeallocEvents
)

/-! ## 1. VM-Step & Framing Helpers -/

theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

theorem vmPreserved_prepend {s s1 s2 : State}
    (h2 : VmPreserved s1 s2) (h1 : VmPreserved s s1) :
    VmPreserved s s2 :=
  h1.trans h2

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

theorem seq_vm_step {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

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

local macro "by_into_pb_vm_steps " "(" tac:tacticSeq ")" : tactic =>
  `(tactic| (
      apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
      ($tac)))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_1520_add_1424
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168 sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 2. Allocator Event Envelopes for Arms 7 & 8 -/

/-- Exact allocation envelope for cloning `ct1 : List (BitVec 8)`. -/
def Ct1CloneAllocEnv (ct1 : List (BitVec 8)) : List AllocEvent → Prop :=
  (· = ct1CloneEvents ct1)

/-- Sequential envelope for cloning `ct1` followed by dropping the old `(cap_ct1, ptr_ct1)` buffer. -/
def Ct1CloneAndDropEnv (ct1 : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAllocEnv ct1) FreeOnlyEvs

theorem fitsEvents_clone_of_ct1CloneAndDropEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {ct1 : List (BitVec 8)}
    (h : FitsEnv M lim st (Ct1CloneAndDropEnv ct1)) :
    FitsEvents M lim st (ct1CloneEvents ct1) :=
  FitsEnv.eq_iff.mp h.seq_left

theorem ct1CloneAndDropEnv_of_dealloc (ct1 : List (BitVec 8)) (cap_ct1 : BitVec 64) :
    Ct1CloneAndDropEnv ct1 (ct1CloneEvents ct1 ++ ct1DeallocEvents cap_ct1) :=
  SeqEnv.append rfl (freeOnlyEvs_ct1DeallocEvents cap_ct1)

/-- Full allocator event envelope for Arm 7 (`States.ct1Sampled`):
    `Ct1CloneAndDropEnv s.uc.ct1`, then `EncoderIntoPbEnv s.sending_ct1`,
    then `DecoderIntoPbEnv s.receiving_ek`. -/
def Ct1SampledEnv {F : ShaCompress}
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) : List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAndDropEnv s.uc.ct1)
    (SeqEnv (EncoderIntoPbEnv s.sending_ct1) (DecoderIntoPbEnv s.receiving_ek))

theorem ct1SampledEnv_of_parts {F : ShaCompress}
    {s : Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {evs_cd evs_enc evs_dec : List AllocEvent}
    (hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd)
    (henc : EncoderIntoPbEnv s.sending_ct1 evs_enc)
    (hdec : DecoderIntoPbEnv s.receiving_ek evs_dec) :
    Ct1SampledEnv s (evs_cd ++ (evs_enc ++ evs_dec)) :=
  SeqEnv.append hcd (SeqEnv.append henc hdec)

/-- Full allocator event envelope for Arm 8 (`States.ekReceivedCt1Sampled`):
    `Ct1CloneAndDropEnv s.uc.ct1`, then `EncoderIntoPbEnv s.sending_ct1`. -/
def EkReceivedCt1SampledEnv {F : ShaCompress}
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    List AllocEvent → Prop :=
  SeqEnv (Ct1CloneAndDropEnv s.uc.ct1) (EncoderIntoPbEnv s.sending_ct1)

theorem ekReceivedCt1SampledEnv_of_parts {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)}
    {evs_cd evs_enc : List AllocEvent}
    (hcd : Ct1CloneAndDropEnv s.uc.ct1 evs_cd)
    (henc : EncoderIntoPbEnv s.sending_ct1 evs_enc) :
    EkReceivedCt1SampledEnv s (evs_cd ++ evs_enc) :=
  SeqEnv.append hcd henc

/-! ## 3. Re-Exports of `RustAlloc`-Parametric Representation Helpers -/

abbrev polyEncoderTag := @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTag
abbrev encoderStateTailAt := @CryptoVerification.SpqrV1.States.IntoPb.encoderStateTailAt
abbrev polyEncoderTailAt := @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTailAt
abbrev polyEncoderAt_eq_tag_tail :=
  @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderAt_eq_tag_tail
abbrev polyEncoderTag_eq_zero_or_one :=
  @CryptoVerification.SpqrV1.States.IntoPb.polyEncoderTag_eq_zero_or_one
abbrev chunkedCt1Sampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedCt1Sampled_expose
abbrev stA_ct1Sampled_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ct1Sampled_entails_928
abbrev ct1SampledScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ct1SampledScratchCells_entails_memRegions
abbrev outWords28_entails_ct1Sampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ct1Sampled
abbrev chunkedEkReceivedCt1Sampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedEkReceivedCt1Sampled_expose
abbrev stA_ekReceivedCt1Sampled_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ekReceivedCt1Sampled_entails_928
abbrev ekReceivedScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ekReceivedScratchCells_entails_memRegions
abbrev outWords28_entails_ekReceivedCt1Sampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ekReceivedCt1Sampled

/-! ## 4. `EncoderIntoPb` & `DecoderIntoPb` Call-and-Expose Helpers -/

theorem sub_ok_encoderIntoPb_raw {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec M A lim) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 23100) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_encoderIntoPb (by decide)).symm
    henc

theorem sub_ok_decoderIntoPb_raw {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec M A lim) :=
  sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 25104) (b := b) (X := Rust.withPanics ext)
      statesIntoPb_fnOff libsignalSessionCode_fnOff_decoderIntoPb (by decide)).symm
    hdec

theorem call_encoderIntoPb_expose_wp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
      (encoderIntoPbSpec M A lim))
    (outEncA encA : BitVec 64) (enc : PolyEncoder) (st : M.σ)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hfits : FitsEnv M lim st (EncoderIntoPbAllocEnv enc))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outEncA)
    (hx1 : s.readReg64 .x1 = encA)
    (hsplit : P = (memRegion outEncA protoPolynomialEncoderSize ∗
      polyEncoderAt A.repAlloc encA enc ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (e0 e1 e2 e3 e4 e5 e6 : BitVec 64),
      EncoderIntoPbEnv enc evs →
      AllocCallPreserved s sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
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
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [encoderIntoPbSpec]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨⟨hx0, hx1, hfits⟩, hm⟩)
    (fun _ _ _ h => by dsimp only [encoderIntoPbSpec] at h; exact not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => by dsimp only [encoderIntoPbSpec] at h; exact not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  dsimp only [encoderIntoPbSpec]
  rw [hsp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun evs => ?_
  refine SepWP.pure_elim fun ⟨htr, hacp, henv⟩ => ?_
  have hexp :
      protoPolynomialEncoderAt A.repAlloc outEncA enc.intoPb ∗
        memRegion encA polyEncoderSize ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ Frame ⊢
      ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
      ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64, ∃∗ e6 : BitVec 64,
        (((outEncA ↦₆₄ e0) ∗ ((outEncA + 8#64) ↦₆₄ e1) ∗ ((outEncA + 16#64) ↦₆₄ e2) ∗
          ((outEncA + 24#64) ↦₆₄ e3) ∗ ((outEncA + 32#64) ↦₆₄ e4) ∗ ((outEncA + 40#64) ↦₆₄ e5) ∗
          ((outEncA + 48#64) ↦₆₄ e6) ∗
          protoPolynomialEncoderHeap A.repAlloc e0 e1 e2 e3 e4 e5 e6 enc.intoPb ∗
          memRegion encA polyEncoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
    refine Entails.trans
      (sepConj_mono_left (protoPolynomialEncoder_expose A.repAlloc outEncA enc.intoPb)) ?_
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
          (Entails.sepExists_right e6 ?_))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hexp ?_
  refine SepWP.exists_elim fun e0 => SepWP.exists_elim fun e1 =>
    SepWP.exists_elim fun e2 => SepWP.exists_elim fun e3 =>
    SepWP.exists_elim fun e4 => SepWP.exists_elim fun e5 =>
    SepWP.exists_elim fun e6 => ?_
  exact hnext sf evs e0 e1 e2 e3 e4 e5 e6 henv hacp hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
    ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

theorem call_decoderIntoPb_expose_wp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
      (decoderIntoPbSpec M A lim))
    (outDecA decA : BitVec 64) (dec : PolyDecoder) (st : M.σ)
    {s0 s : State} {ret_pc target_pc : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hfits : FitsEnv M lim st (DecoderIntoPbAllocEnv dec))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = outDecA)
    (hx1 : s.readReg64 .x1 = decA)
    (hsplit : P = (memRegion outDecA protoPolynomialDecoderSize ∗
      polyDecoderAt A.repAlloc decA dec ∗
      A.pool lim st s ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent) (d0 d1 d2 d3 d4 : BitVec 64),
      DecoderIntoPbEnv dec evs →
      AllocCallPreserved s sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s P post := by
  have hstk := stackAt_encoderIntoPb_eq_decoderIntoPb (s0.sp - 1520#64)
  refine SepWP.call_subroutine_frame hdec_raw (x := (⟨outDecA, decA, dec⟩, st))
    (F := memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit, hstk] at hm
      dsimp only [decoderIntoPbSpec]
      rw [hsp]
      have hm' : s.mem ⊨
          (memRegion outDecA protoPolynomialDecoderSize ∗
           polyDecoderAt A.repAlloc decA dec ∗
           A.pool lim st s ∗
           stackAt (s0.sp - 1520#64) decoderIntoPbStack) ∗
          (memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame ∗ R') :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
      exact ⟨⟨hx0, hx1, hfits⟩, hm'⟩)
    (fun _ _ _ h => by dsimp only [decoderIntoPbSpec] at h; exact not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => by dsimp only [decoderIntoPbSpec] at h; exact not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  dsimp only [decoderIntoPbSpec]
  rw [hsp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun evs => ?_
  refine SepWP.pure_elim fun ⟨htr, hacp, henv⟩ => ?_
  have hexp :
      protoPolynomialDecoderAt A.repAlloc outDecA dec.intoPb ∗
        memRegion decA polyDecoderSize ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 1520#64) decoderIntoPbStack ∗
        memRegion ((s0.sp - 1520#64) - 4352#64) 64 ∗ Frame ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
      ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64,
        (((outDecA ↦₆₄ d0) ∗ ((outDecA + 8#64) ↦₆₄ d1) ∗ ((outDecA + 16#64) ↦₆₄ d2) ∗
          ((outDecA + 24#64) ↦₆₄ d3) ∗ ((outDecA + 32#64) ↦₆₄ d4) ∗
          protoPolynomialDecoderHeap A.repAlloc d0 d1 d2 d3 d4 dec.intoPb ∗
          memRegion decA polyDecoderSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗ Frame) := by
    have hrecomb :
        stackAt (s0.sp - 1520#64) decoderIntoPbStack ∗
          memRegion ((s0.sp - 1520#64) - 4352#64) 64 =
        stackAt (s0.sp - 1520#64) encoderIntoPbStack := by
      rw [hstk]; ac_rfl
    refine Entails.trans
      (sepConj_mono_left (protoPolynomialDecoder_expose A.repAlloc outDecA dec.intoPb)) ?_
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro d0
    apply Entails.sepExists_elim; intro d1
    apply Entails.sepExists_elim; intro d2
    apply Entails.sepExists_elim; intro d3
    apply Entails.sepExists_elim; intro d4
    refine Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d4 ?_))))
    rw [← hrecomb]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hexp ?_
  refine SepWP.exists_elim fun d0 => SepWP.exists_elim fun d1 =>
    SepWP.exists_elim fun d2 => SepWP.exists_elim fun d3 =>
    SepWP.exists_elim fun d4 => ?_
  exact hnext sf evs d0 d1 d2 d3 d4 henv hacp hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
    ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-! ## 5. `VmPreserved`-Preserving Prologue (`+0 -> +60`) and Epilogue (`+1544 -> ret`) -/

theorem states_into_pb_prologue_60_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out stA tag : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64) s0
      (stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ tag) ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 1512#64) 1416 ∗
          statesIntoPbSavedCells s0 ∗
          (stA ↦₆₄ tag) ∗ Rest) ∧
        AllocCallPreserved s0 s1 ∧
        s1.sp = s0.sp - 1520#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x28 = s0.sp - 256#64 ∧
        s1.readReg64 .x27 = s0.sp - 1360#64 ∧
        s1.readReg64 .x26 = s0.sp - 480#64 ∧
        s1.readReg64 .x20 = stA ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x8 = tag ∧
        TraceCalleeSaved s1 s0) := by
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsplit_1424 : memRegion (s0.sp - 1520#64) 1424 =
      cells (s0.sp - 1520#64) 1 ∗
      memRegion (s0.sp - 1512#64) 1416 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rw [stackAt_statesIntoPb_split_96 s0.sp, stackAt_statesIntoPb_split_fsp s0.sp]
  nth_rw 1 [hsplit_1424]
  cells_unfold
  wp_pull_exists
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, statesIntoPbSavedCells,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [hfn_eq] at hpc
  conv => enter [2]; rw [hfn_eq]
  by_into_pb_vm_steps (
    into_pb_fetches_range b trapHooks 0 60
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

theorem states_into_pb_epilogue_vm {b : BitVec 64} {ext : String → Option (State → State)}
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
       Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          outWords28 out
            (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
            w64 w72 w80 w88 w96 w104 w112 w120
            w128 w136 w144 w152 w160 w168 w176 w184
            w192 w200 w208 w216 ∗
          stackAt s0.sp statesIntoPbStack ∗
          Rest) ∧
        AllocCallPreserved s sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr with ⟨htr, hvregs⟩
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
      Rest ⊢
      outWords28 out
        (s.readReg64 .x22) w8 w16 w24 w32 w40 w48 (s.readReg64 .x21)
        w64 w72 w80 w88 w96 w104 w112 w120
        w128 w136 w144 w152 w160 w168 w176 w184
        w192 w200 w208 w216 ∗
      stackAt s0.sp statesIntoPbStack ∗
      Rest := by
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
  refine SepWP.mono
    (post := fun sf Pf =>
      VmPreserved s sf ∧
      (Pf ⊢
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
        Rest) ∧
      AllocCallPreserved s sf ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace)
    ?_
    (fun _ _ _ _ ⟨hvm, hPf, hacp, hrest⟩ => ⟨hvm, Entails.trans hPf hrestore, hacp, hrest⟩)
  rw [memRegion_out_224_eq out]
  wp_pull_exists
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    outWords28, epilogueStagingCells, statesIntoPbSavedCells, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [hfn_eq] at hpc
  by_into_pb_vm_steps (
    into_pb_fetches_range b trapHooks 1544 100
    generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_pre (by sep_ac_rfl) ?_
    wp_done
  )

/-! ## 6. Variant Specifications for Arms 7 & 8 -/

/-- Envelope-parametric per-variant fixed-offset specification of `<States>::into_pb`. -/
def statesIntoPbVariantSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, stA⟩, st) s0 =>
    ⌜s0.readReg64 .x8 = out ∧ s0.readReg64 .x0 = stA ∧
      (b &&& 0xfff#64) = 0#64 ∧ FitsEnv M lim st Env⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA stateVal ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack
  post := fun (⟨out, stA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

abbrev statesIntoPbCt1SampledSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (s : Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.ct1Sampled s) (Ct1SampledEnv s)

abbrev statesIntoPbEkReceivedCt1SampledSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b (.ekReceivedCt1Sampled s)
    (EkReceivedCt1SampledEnv s)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
