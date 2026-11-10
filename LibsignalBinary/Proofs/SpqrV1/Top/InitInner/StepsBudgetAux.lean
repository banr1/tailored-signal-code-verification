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
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Steps
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::init_inner`: VM-Preserving Fixed-Offset Step Lemmas (Entry, Epilogue, Post-Auth)

Proves `VmPreserved`-strengthened sequencing helpers, `.v0` execution, `.v1` prologue/epilogue,
and post-`Authenticator::new` construction for `spqr::init_inner` (`0x532dc`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.LibsignalTripleRatchet (ImgCallInv tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Bytes Direction Version)
open CryptoVerification.SpqrV1.Auth (authNewStackX authenticatorAt)
open CryptoVerification.SpqrV1.Drop
  (chunkedKeysUnsampledAt chunkedNoHeaderReceivedAt chunkedStatesAt none3Cap'
   optProtoInnerStateSize optProtoPqRatchetInnerAt unchunkedKeysUnsampledAt
   unchunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt)
open CryptoVerification.SpqrV1.States.IntoPb
  (authenticatorAt_of_words_heap authenticatorHeap bv_add_add_lit' bv_sub_sub_lit')
open CryptoVerification.SpqrV1.Top.InitInner
  (emptySortedSetPtCells initHdrDecoder initInnerName initInnerResultAt initInnerSavedCells
   initInnerStack initInnerValue initV1State memRegion_out_224_split_8
   polyDecoderAt_initHdrDecoder stackAt_initInner_split stack_restore_initInner)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
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

local macro "init_inner_fetches_plain " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.Top.InitInner.libsignalSessionBin
      $b $H CryptoVerification.SpqrV1.Top.InitInner.initInner_fnOff
      (ls_off% "spqr::init_inner") $k0 $len)

local macro "init_inner_fetches_vm " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| (
      init_inner_fetches_plain $b $H $k0 $len
      lift_fetches_withSvc))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

theorem align_pre_tp {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Tp : State → Prop} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => Tp sm ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => Tp sm ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

theorem sepWP_rebase_entails_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre Q : SepProp} {R : State → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q) ∧ VmPreserved s sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hQ, hR⟩ => ⟨hQ, hvm, hR⟩

theorem sepWP_rebase_strengthen_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre Q Q' : SepProp} {R : State → Prop}
    (h : Q ⊢ Q')
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q') ∧ VmPreserved s sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hQ, hR⟩ => ⟨Entails.trans hQ h, hvm, hR⟩

/-! ## 1. Re-Exports, Sequencing, and Callee-Saved Helpers -/

abbrev initInnerSavedCells_entails_memRegion :=
  @CryptoVerification.SpqrV1.Top.InitInner.initInnerSavedCells_entails_memRegion
abbrev sortedSetPtOf_withCapacity_zero :=
  @CryptoVerification.SpqrV1.Top.InitInner.sortedSetPtOf_withCapacity_zero
abbrev emptySortedSetPtCells_entails :=
  @CryptoVerification.SpqrV1.Top.InitInner.emptySortedSetPtCells_entails
abbrev initInner_seq_sepWP_inImage :=
  @CryptoVerification.SpqrV1.Top.InitInner.initInner_seq_sepWP_inImage

theorem initInner_seq_wp {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      Post s' → SepWP prog ret s' P' Q) :
    SepWP prog ret s P Q :=
  SepWP.seq hstep fun s' _P1 hpc' hrun' ⟨hent, hpost⟩ =>
    SepWP.weaken_pre hent (hnext s' hpc' hrun' hpost)

theorem sepWPp_of_sepWP_keepInv {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      (∀ img, ImgCallInv img s → ImgCallInv img sm) → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (fun _ hinv => hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem initInner_seq_sepWP {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      (∀ img, ImgCallInv img s → ImgCallInv img s') → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_of_sepWP_keepInv (mid := mid) ?_
  refine SepWP.mono hstep fun s' _P1 hpc' hrun' ⟨hent, hpost⟩ hinv' =>
    SepWPp.weaken_pre hent (hnext s' hpc' hrun' hinv' hpost)

theorem calleeSaved_chain_hi {s0 s sf : State}
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcs : CalleeSavedPreserved s sf) :
    sf.readReg64 .x22 = s0.readReg64 .x22 ∧ sf.readReg64 .x23 = s0.readReg64 .x23 ∧
    sf.readReg64 .x24 = s0.readReg64 .x24 ∧ sf.readReg64 .x25 = s0.readReg64 .x25 ∧
    sf.readReg64 .x26 = s0.readReg64 .x26 ∧ sf.readReg64 .x27 = s0.readReg64 .x27 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  dsimp only [CalleeSavedPreserved] at hcs
  rcases hcs_hi with ⟨h22, h23, h24, h25, h26, h27, hvregs⟩
  exact ⟨by simp only [hcs, h22], by simp only [hcs, h23], by simp only [hcs, h24],
         by simp only [hcs, h25], by simp only [hcs, h26], by simp only [hcs, h27],
         by simp only [hcs, hvregs]⟩

theorem calleeSaved_x29 {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x29 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x29 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

theorem calleeSaved_x19 {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x19 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x19 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

/-! ## 2. Version `.v0` Branch (`+0 -> +28 -> +92 -> +116`) and Epilogue (`+416 -> +432`) -/

/-- Full execution of `spqr::init_inner` for `v = .v0` (`w1 = 0#32`):
    `+0 -> +28 -> +92 -> +116 -> ret`, preserving `VmPreserved s0 sf`. -/
theorem init_inner_v0 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v0.toI32) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
      (memRegion out optProtoInnerStateSize ∗
       stackAt s0.sp initInnerStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          initInnerResultAt A (F := F) out .v0 d authKey ∗
          stackAt s0.sp initInnerStack ∗
          Rest) ∧
        VmPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      initInnerResultAt A (F := F) out .v0 d authKey ∗
      stackAt s0.sp initInnerStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono_left (stack_restore_initInner s0))
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [tripleRatchetProgAtExt, initInnerName, Version.toI32,
    State.readReg32, Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at hpc hx0 hw1 ⊢
  refine sepWP_rebase_strengthen_vmPreserved hrestore ?_
  rw [hfn_eq] at hpc
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 0 32
  init_inner_fetches_vm b trapHooks 92 28
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  rw [memRegion_out_224_split_8 out, stackAt_initInner_split s0.sp]
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerResultAt, initInnerValue, Option.map,
    optProtoPqRatchetInnerAt, none3Cap', initInnerSavedCells]
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- Epilogue of `spqr::init_inner` for `v = .v1` (`+416 -> +432 -> ret`),
    preserving `VmPreserved s sf`. -/
theorem init_inner_epilogue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0 ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp initInnerStack ∗ Rest) ∧
        VmPreserved s sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      (stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992 ∗
       initInnerSavedCells s0) ∗
      Rest ⊢
      stackAt s0.sp initInnerStack ∗ Rest :=
    sepConj_mono_left (stack_restore_initInner s0)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  have hsp1040_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hrestore ?_
  rw [hfn_eq] at hpc
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 416 20
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  dsimp only [initInnerSavedCells]
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-! ## 3. Version `.v1` Prologue (`+0 -> +36`) and Post-`Authenticator::new` Construction -/

/-- Prologue of `spqr::init_inner` for `v = .v1` (`w1 = 1#32`):
    `+0 -> +36` (9 instructions), preserving `VmPreserved s0 s1`. -/
theorem init_inner_prologue_v1 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out)
    (hw1 : s0.readReg32 .x1 = Version.v1.toI32)
    (hw2 : s0.readReg32 .x2 = d.toI32)
    (hx3 : s0.readReg64 .x3 = akPtr)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 authKey.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64) s0
      (cells (s0.sp - 48#64) 6 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ initInnerSavedCells s0 ∗ Rest) ∧
        VmPreserved s0 s1 ∧
        s1.sp = s0.sp - 1040#64 ∧
        s1.readReg64 .x29 = s0.sp - 48#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length ∧
        s1.readReg32 .x2 = d.toI32 ∧
        s1.readReg64 .x3 = akPtr ∧
        (s1.readReg64 .x22 = s0.readReg64 .x22 ∧
         s1.readReg64 .x23 = s0.readReg64 .x23 ∧
         s1.readReg64 .x24 = s0.readReg64 .x24 ∧
         s1.readReg64 .x25 = s0.readReg64 .x25 ∧
         s1.readReg64 .x26 = s0.readReg64 .x26 ∧
         s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.trace = s0.trace) := by
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  have hsp48_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 48#64 hsp0_align (by decide)
  dsimp only [tripleRatchetProgAtExt, initInnerName, Version.toI32,
    State.readReg32, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, BitVec.ofNat_eq_ofNat]
    at hpc hx0 hw1 hw2 hx3 hx4 ⊢
  refine sepWP_rebase_entails_vmPreserved ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 0 36
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  dsimp only [initInnerSavedCells]
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

/-- Post-`Authenticator::new` construction for `d = .a2b` (`+368 -> +412`, 11 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_a2b_post_auth {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 1032#64) 8 ∗
       memRegion (s0.sp - 968#64) 864 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
          memRegion (s0.sp - 104#64) 48 ∗
          Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       memRegion (s0.sp - 968#64) 864) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have h48 :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ⊢
        memRegion (s0.sp - 104#64) 48 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 6 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h64 : (s0.sp - 1032#64) + 64#64 = s0.sp - 968#64 := by bv_omega
    rw [h56, h64]
    refine sepConj_mono ?_ (sepConj_mono_left h48)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hst ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 368 44
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  cells_unfold
  wp_pull_exists
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

set_option maxHeartbeats 1600000 in
/-- Post-`Authenticator::new` construction for `d = .b2a` (`+196 -> +340 -> +400 -> +412`, 41 instructions),
    preserving `VmPreserved s s2`. -/
theorem init_inner_b2a_post_auth {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (authKey : Bytes)
    (a0 a1 a2 a3 a4 a5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64) s
      ((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
       cells (s0.sp - 56#64) 1 ∗
       cells (s0.sp - 1032#64) 20 ∗
       cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗
       (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗
       memRegion (s0.sp - 568#64) 464 ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
          memRegion (s0.sp - 104#64) 56 ∗
          Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x8 = out ∧
        s2.readReg64 .x0 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hst :
      (((s0.sp - 1032#64) ↦₆₄ 7#64) ∗
       (((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64)) ∗
       ((s0.sp - 976#64) ↦₆₄ 1#64) ∗
       (emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7) ∗
       memRegion (s0.sp - 568#64) 464) ∗
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
       ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
       ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
       ((s0.sp - 56#64) ↦₆₄ 1#64)) ∗
      Rest ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗
      Rest := by
    have hauth :
        ((s0.sp - 1024#64) ↦₆₄ a0) ∗ ((s0.sp - 1016#64) ↦₆₄ a1) ∗
        ((s0.sp - 1008#64) ↦₆₄ a2) ∗ ((s0.sp - 1000#64) ↦₆₄ a3) ∗
        ((s0.sp - 992#64) ↦₆₄ a4) ∗ ((s0.sp - 984#64) ↦₆₄ a5) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ⊢
        authenticatorAt A ((s0.sp - 1032#64) + 8#64) (Authenticator.new F authKey 1#64) := by
      have h := authenticatorAt_of_words_heap A ((s0.sp - 1032#64) + 8#64) a0 a1 a2 a3 a4 a5
        (Authenticator.new F authKey 1#64)
      simpa only [arm64_norm, sepConj_assoc] using h
    have hpoly :
        emptySortedSetPtCells 16 (s0.sp - 968#64) ∗
        ((s0.sp - 584#64) ↦₆₄ 48#64) ∗
        ((s0.sp - 576#64) ↦₈ 0#8) ∗
        memRegion (s0.sp - 575#64) 7 ⊢
        polyDecoderAt A ((s0.sp - 1032#64) + 8#64 + 56#64) initHdrDecoder := by
      have h := polyDecoderAt_initHdrDecoder A (s0.sp - 968#64)
      simpa only [arm64_norm] using h
    have h56_cells :
        ((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
        ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
        ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5) ∗
        ((s0.sp - 56#64) ↦₆₄ 1#64) ⊢
        memRegion (s0.sp - 104#64) 56 := by
      rw [ProofLib.memRegion_cells (s0.sp - 104#64) 7 (by decide)]
      cells_unfold
      refine Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5
            (Entails.sepExists_right 1#64 ?_))))))
      exact Entails.of_eq (by simp only [arm64_norm])
    dsimp only [initV1State, chunkedStatesAt, chunkedNoHeaderReceivedAt, unchunkedNoHeaderReceivedAt]
    have h56 : (s0.sp - 1032#64) + 8#64 + 48#64 = s0.sp - 976#64 := by bv_omega
    have h464 : (s0.sp - 1032#64) + 464#64 = s0.sp - 568#64 := by bv_omega
    rw [h56, h464]
    refine sepConj_mono ?_ (sepConj_mono_left h56_cells)
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hauth)) ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpoly)))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr =
      (libsignalSessionCode.rebase b trapHooks).fnAddr := rebase_fnAddr_eq _ _ _ _
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWP_rebase_strengthen_vmPreserved hst ?_
  rw [hfn_eq] at hpc ⊢
  apply sepWP_rebase_vmPreserved
  init_inner_fetches_vm b trapHooks 196 148
  init_inner_fetches_vm b trapHooks 400 12
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  simp (config := { maxSteps := 500000 }) only [ProofLib.cells_succ, ProofLib.cells_zero,
    sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  wp_pull_exists
  simp only [emptySortedSetPtCells, arm64_norm, sepConj_emp]
  wp_steps
  refine align_pre_tp (by sep_ac_rfl) ?_
  wp_done

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudgetAux
