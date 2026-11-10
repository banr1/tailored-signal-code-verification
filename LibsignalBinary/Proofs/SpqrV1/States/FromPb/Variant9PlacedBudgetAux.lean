/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
import ProofLib.SepLogic.WPp

/-!
# Budget Envelopes and Step Liftings for `Variant9PlacedBudget`

Defines `Ct1AcknowledgedUcSomeEnv` and `Ct1AcknowledgedFromPbEnv` with `StatesFromPbEnv` subsumption,
and lifts `<Ct1Sent>::from_pb` call combinators and Variant 9 pure steps (`+444`, `+2768`, `+2864`)
to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 lsProg_333 lsmpl
   sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator ProtoPolynomialDecoder V1State
   pbToProtoPolyDecoder spqrAuthApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v9_Saved5368Preserved v9_optProtoPolyDecoderWordsAt v9_optProtoUcWordsAt)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth
   rawUcCt1Sent rawUcCt1Sent_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecAllocEnv_imp_fromPbDecEnv
   fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudget
  (ct1_sent_from_pb_on_333_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudgetAux
  (v9_saved5368Preserved_stripS)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv authFromPbAllocEvents
   ct1SentFromPb ct1SentFromPbAllocEvents ct1SentFromPbPostEnv_of_nil ct1SentFromPbSpec)

/-! ## 1. Relocatable Callee Contracts & Total `SepWP` Call / Sequencing Helpers -/

/-- Relocatable `<Ct1Sent>::from_pb` (Block `339`) lifted to caller program `lsProg_333`. -/
theorem v9_sub_ok_ct1_sent_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) :=
  ct1_sent_from_pb_on_333_placed_ok hA.shim hA.alloc hA.dealloc hA.memcpy

/-- Total `SepWP` sequence helper threading `LibsignalCodeLoaded lsmpl ·.mem` across `mid`
    with state-dependent intermediate resource `P_mid sm`. -/
theorem v9_seq_clean_lscl [LibsignalPlacement]
    {ext : String → Option (State → State)} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_333 (Rust.withPanics ext)) mid s P
      (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWP (lsProg_333 (Rust.withPanics ext)) ret sm (P_mid sm) Q) :
    SepWP (lsProg_333 (Rust.withPanics ext)) ret s P Q :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hP, hQ⟩ hclm =>
    SepWP.weaken_pre hP (h2 sm hpc hrun hclm hQ))

/-- Single-call `SepWP` step to `ret_pc` for any total (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`,
    `onOom = ⌜False⌝`) `withLsCodeLoaded lsmpl spec` contract. -/
theorem v9_call_ret_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step Frame : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_step ⊢ spec.pre x s)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP prog ret_pc s (P_step ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ spec.post x s sm ∗ Frame) ∧
        sm.sp = s.sp ∧ CalleeSavedPreserved s sm) := by
  have hpre_cl : P_step ⊢ (withLsCodeLoaded lsmpl spec).pre x s := by
    dsimp only [withLsCodeLoaded]
    exact Entails.trans (Entails.pure_right hcl hpre) (Entails.of_eq (by ac_rfl))
  refine SepWP.call_subroutine_frame hcall (x := x) (F := Frame)
    hpc hrun hsp_align hlr
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_cl) hm)
    (fun sf _ _ hm => by
      dsimp only [withLsCodeLoaded] at hm
      rw [hpan_eq] at hm
      exact not_satisfies_false_sepConj hm)
    (fun sf code _ _ hm => by
      dsimp only [withLsCodeLoaded] at hm
      rw [hexit_eq] at hm
      exact not_satisfies_false_sepConj hm)
    (fun sm hpcm hrunm hspm hcsm => by
      dsimp only [withLsCodeLoaded]
      exact ProofLib.SepWP.done hpcm hrunm ⟨Entails.refl _, hspm, hcsm⟩)
    (fun sf _ _ hm => by
      dsimp only [withLsCodeLoaded] at hm
      rw [hoom_eq] at hm
      exact False.elim (not_satisfies_false_sepConj hm))

/-- Call-and-continue `SepWP` combinator on `lsProg_333` threading `LibsignalCodeLoaded lsmpl`
    into `hnext` for total (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`) specs. -/
theorem v9_call_entails_lscl [LibsignalPlacement] {α : Type}
    {ext : String → Option (State → State)}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_333 (Rust.withPanics ext)) entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_step ⊢ spec.pre x s)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      LibsignalCodeLoaded lsmpl sf.mem → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWP (lsProg_333 (Rust.withPanics ext)) target_pc sf (spec.post x s sf ∗ Frame) post)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWP (lsProg_333 (Rust.withPanics ext)) target_pc s (P_step ∗ Frame) post :=
  v9_seq_clean_lscl hcl
    (v9_call_ret_lscl hcall hcl hpc hrun hsp_align hlr hpre hpan_eq hexit_eq hoom_eq)
    fun sf hpcf hrunf hclf ⟨hsp_f, hcs_f⟩ => hnext sf hpcf hrunf hclf hsp_f hcs_f

/-! ## 2. `VmPreserved` & Pool-Threading Liftings of Pure Variant 9 Steps (`Variant9b/9cPlaced`) -/

/-- `VmPreserved`-strengthened `+444 -> +2768` when `receivingEk = none` (`w0 = noneCap`). -/
theorem v9_states_from_pb_step_444_to_2768_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗ Rest) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = noneCap ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9bPlaced.v9_states_from_pb_step_444_to_2768_none_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
      w8 w16 d24 d28 w32 Rest
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0, hx8, hx9, hx13, hx19_m, hx20, hx21, hx22, hx23, hx25, hx27_m, hx29, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0, by simpa using hx8,
       by simpa using hx9, by simpa using hx13, by simpa using hx19_m, by simpa using hx20,
       by simpa using hx21, by simpa using hx22, by simpa using hx23, by simpa using hx25,
       by simpa using hx27_m, by simpa using hx29,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v9_states_from_pb_step_444_to_2768_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗
        Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) noneCap w8 w16 d24 d28 w32 ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = noneCap ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v9_states_from_pb_step_444_to_2768_none_placed (ext := ext) s0 s fsp out pbA
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
    w8 w16 d24 d28 w32 (Rest ∗ A.pool lim st s) hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened `+444 -> +2768` when `receivingEk = some d` (`d24 = 576#32`). -/
theorem v9_states_from_pb_step_444_to_2768_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗ Rest) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = (576#32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9bPlaced.v9_states_from_pb_step_444_to_2768_some_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
      w0 w8 w16 d28 w32 Rest hw0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0, hx8, hx9, hx10, hx13, hx19_m, hx20, hx21, hx22, hx23, hx25, hx27_m, hx29, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0, by simpa using hx8,
       by simpa using hx9, by simpa using hx10, by simpa using hx13, by simpa using hx19_m,
       by simpa using hx20, by simpa using hx21, by simpa using hx22, by simpa using hx23,
       by simpa using hx25, by simpa using hx27_m, by simpa using hx29,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v9_states_from_pb_step_444_to_2768_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp) (hw0_lt : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2768#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗
        Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = (576#32).zeroExtend 64 ∧
        sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v9_states_from_pb_step_444_to_2768_some_placed (ext := ext) s0 s fsp out pbA
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
    w0 w8 w16 d28 w32 (Rest ∗ A.pool lim st s) hw0_lt hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened `+444 -> +488` when `receivingEk = some d` with `d24 ≠ 576#32`. -/
theorem v9_states_from_pb_step_444_to_488_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp) (hw0_lt : w0.toNat < 2 ^ 63) (hd24_ne : d24 ≠ 576#32)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 488#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ Rest) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9bPlaced.v9_states_from_pb_step_444_to_488_err_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
      w0 w8 w16 d24 d28 w32 Rest hw0_lt hd24_ne
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0, hx8, hx19_m, hx20, hx21, hx22, hx23, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0, by simpa using hx8,
       by simpa using hx19_m, by simpa using hx20, by simpa using hx21, by simpa using hx22,
       by simpa using hx23, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v9_states_from_pb_step_444_to_488_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (Rest : SepProp) (hw0_lt : w0.toNat < 2 ^ 63) (hd24_ne : d24 ≠ 576#32)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 488#64) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pbA + 8#64 ∧
        sm.readReg64 .x8 = u0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v9_states_from_pb_step_444_to_488_err_placed (ext := ext) s0 s fsp out pbA
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
    w0 w8 w16 d24 d28 w32 (Rest ∗ A.pool lim st s) hw0_lt hd24_ne hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened `+2768 -> lsmpl.base 339` (`<Ct1Sent>::from_pb` setup & `bl`). -/
theorem v9_states_from_pb_copy_uc_to_call_2768_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 w32 : BitVec 64)
    (z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 : BitVec 64)
    (b1400 : BitVec 8) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2768#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0) (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx27 : s.readReg64 .x27 = pbA) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗ ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ z1401) ∗ ((fsp + 1409#64) ↦₆₄ z1409) ∗
        ((fsp + 1417#64) ↦ₛ loBytes7 z1417) ∗ ((fsp + 1424#64) ↦₆₄ z1424) ∗
        ((fsp + 1432#64) ↦₆₄ z1432) ∗ ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗ ((fsp + 1456#64) ↦₆₄ z1456) ∗
        ((fsp + 1464#64) ↦₆₄ z1464) ∗ ((fsp + 1472#64) ↦₆₄ z1472) ∗
        ((fsp + 1480#64) ↦₆₄ z1480) ∗ ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗ ((fsp + 1504#64) ↦₆₄ z1504) ∗
        ((fsp + 1512#64) ↦₆₄ z1512) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          Rest) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 2864#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9bPlaced.v9_states_from_pb_copy_uc_to_call_2768_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
      w0 w8 w16 w32 z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472
      z1480 z1488 z1496 z1504 z1512 b1400 Rest hfsp_align hu0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx8) (by simpa using hx9) (by simpa using hx13)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx25)
      (by simpa using hx27) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0, hx1, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24, hx25_m, hx27_m, hx29, hx30, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0, by simpa using hx1,
       by simpa using hx19_m, by simpa using hx20_m, by simpa using hx21_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx24,
       by simpa using hx25_m, by simpa using hx27_m, by simpa using hx29,
       by simpa using hx30, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v9_states_from_pb_copy_uc_to_call_2768_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 w32 : BitVec 64)
    (z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 : BitVec 64)
    (b1400 : BitVec 8) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2768#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0)
    (hx9 : s.readReg64 .x9 = ((loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0) (hx22 : s.readReg64 .x22 = w16)
    (hx23 : s.readReg64 .x23 = w32) (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx27 : s.readReg64 .x27 = pbA) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339) s
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗ ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ z1401) ∗ ((fsp + 1409#64) ↦₆₄ z1409) ∗
        ((fsp + 1417#64) ↦ₛ loBytes7 z1417) ∗ ((fsp + 1424#64) ↦₆₄ z1424) ∗
        ((fsp + 1432#64) ↦₆₄ z1432) ∗ ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗ ((fsp + 1456#64) ↦₆₄ z1456) ∗
        ((fsp + 1464#64) ↦₆₄ z1464) ∗ ((fsp + 1472#64) ↦₆₄ z1472) ∗
        ((fsp + 1480#64) ↦₆₄ z1480) ∗ ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗ ((fsp + 1504#64) ↦₆₄ z1504) ∗
        ((fsp + 1512#64) ↦₆₄ z1512) ∗ Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = w8 ∧
        sm.readReg64 .x21 = w0 ∧
        sm.readReg64 .x22 = w16 ∧
        sm.readReg64 .x23 = w32 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 2864#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v9_states_from_pb_copy_uc_to_call_2768_placed (ext := ext) s0 s fsp out pbA
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
    w0 w8 w16 w32 z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472
    z1480 z1488 z1496 z1504 z1512 b1400 (Rest ∗ A.pool lim st s)
    hfsp_align hu0_lt hpc hrun hsp hx8 hx9 hx13 hx19 hx20 hx21 hx22 hx23 hx25 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened error branch after `ct1SentFromPb` (`+2864 -> +5360`). -/
theorem v9_step_2864_err_to_5360_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap) (hx22 : s.readReg64 .x22 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Frame)
      (fun s' P' =>
        (P' ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ Frame) ∧
        VmPreserved s s' ∧
        v9_Saved5368Preserved s0 s' fsp out ptsPtr ptsCap w1896 ∧
        s'.readReg64 .x22 = ptsLen) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9bPlaced.v9_step_2864_err_to_5360_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap ptsLen w1896 w1904 w1912 Frame hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun s' P' hvm ⟨hP', hpres', hx22'⟩ =>
      ⟨hP', hvm, v9_saved5368Preserved_stripS.mp hpres', by simpa using hx22'⟩

theorem v9_step_2864_err_to_5360_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64)
    (w1896 w1904 w1912 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap) (hx22 : s.readReg64 .x22 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s
      (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Rest ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Rest ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        v9_Saved5368Preserved s0 s' fsp out ptsPtr ptsCap w1896 ∧
        s'.readReg64 .x22 = ptsLen) := by
  have hwp := v9_step_2864_err_to_5360_placed (ext := ext) s0 s fsp out ptsPtr ptsCap ptsLen
    w1896 w1904 w1912 (Rest ∗ A.pool lim st s) hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 htrace
  refine SepWP.mono hwp fun s' P' _ _ ⟨hP', hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, hrest⟩

/-- `VmPreserved`-strengthened `+2864 -> +6904` when `ct1SentFromPb` returned `Ok(uc)` and
    `receivingEk = none` (`x21 = noneCap`). -/
theorem v9_step_2864_ok_none_to_6904_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w72 w128 w144 w152 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = noneCap)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6904#64) s
      (((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
        ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
        ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
        v9_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗ memRegion (fsp + 1888#64) 128 ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
        s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant9cPlaced.v9_step_2864_ok_none_to_6904_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep w72 w128 w144 w152 w240 w248 d96 Rest
      hfsp_align hrk_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx21) (by simpa using hx25)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx0, hx1, hx10, hx13, hx14, hx19_1, hx28, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx0, by simpa using hx1,
       by simpa using hx10, by simpa using hx13, by simpa using hx14,
       by simpa using hx19_1, by simpa using hx28,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v9_step_2864_ok_none_to_6904_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w72 w128 w144 w152 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = noneCap)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6904#64) s
      (((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
        ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
        ((fsp + 248#64) ↦ₛ loBytes7 w248) ∗
        v9_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
          ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗ memRegion (fsp + 1888#64) 128 ∗
          Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
        s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  have hwp := v9_step_2864_ok_none_to_6904_placed (ext := ext) s0 s fsp out
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    w72 w128 w144 w152 w240 w248 d96 (Rest ∗ A.pool lim st s)
    hfsp_align hrk_lt hpc hrun hsp hx19 hx21 hx25 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-! ## 3. Exact Binary Allocation Envelopes & `StatesFromPbEnv` Subsumption -/

/-- Exact binary allocator event envelope at `+2768` when `uc = some u` and either `receivingEk = none`
    or `receivingEk = some d` (`d.ptsNeeded == 576#32`):
    - if `<Ct1Sent>::from_pb` returns `.ok _` and `optDec = some d`, `<Ct1Sent>::from_pb` events
      followed by `<PolyDecoder>::from_pb` events followed by `FreeOnlyEvs` cleanup (empty on `.ok`);
    - otherwise, `<Ct1Sent>::from_pb` events followed by `FreeOnlyEvs` cleanup of any remaining
      fields. -/
def Ct1AcknowledgedUcSomeEnv (F : ShaCompress) (u : V1State.Unchunked.Ct1Sent)
    (optDec : Option PolynomialDecoder) (evs : List AllocEvent) : Prop :=
  match ct1SentFromPb (spqrAuthApi F) u, optDec with
  | .ok _, some d =>
    ∃ evs1 evs2 evs3,
      Ct1SentFromPbPostEnv F u evs1 ∧
      FromPbDecEnv (pbToProtoPolyDecoder d) evs2 ∧
      FreeOnlyEvs evs3 ∧
      evs = evs1 ++ evs2 ++ evs3
  | _, _ =>
    ∃ evs1 evs2,
      Ct1SentFromPbPostEnv F u evs1 ∧
      FreeOnlyEvs evs2 ∧
      evs = evs1 ++ evs2

/-- Exact binary allocator event envelope for Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) of
    `<spqr::v1::chunked::states::States>::from_pb`. -/
def Ct1AcknowledgedFromPbEnv (F : ShaCompress)
    (st : V1State.Chunked.Ct1Acknowledged) (evs : List AllocEvent) : Prop :=
  match st.receivingEk, st.uc with
  | some d, some u =>
    if d.ptsNeeded == 576#32 then Ct1AcknowledgedUcSomeEnv F u (some d) evs else FreeOnlyEvs evs
  | none, some u => Ct1AcknowledgedUcSomeEnv F u none evs
  | _, none => FreeOnlyEvs evs

theorem ct1AcknowledgedUcSomeEnv_of_err {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {optDec : Option PolynomialDecoder} {e : _}
    (herr : ct1SentFromPb (spqrAuthApi F) u = .error e)
    {evs1 evs2 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1) (h2 : FreeOnlyEvs evs2) :
    Ct1AcknowledgedUcSomeEnv F u optDec (evs1 ++ evs2) := by
  unfold Ct1AcknowledgedUcSomeEnv
  rw [herr]
  exact ⟨evs1, evs2, h1, h2, rfl⟩

theorem ct1AcknowledgedUcSomeEnv_of_ok_none {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    {evs1 evs2 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1) (h2 : FreeOnlyEvs evs2) :
    Ct1AcknowledgedUcSomeEnv F u none (evs1 ++ evs2) := by
  unfold Ct1AcknowledgedUcSomeEnv
  rw [hok]
  exact ⟨evs1, evs2, h1, h2, rfl⟩

theorem ct1AcknowledgedUcSomeEnv_of_ok_some {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc) (d : PolynomialDecoder)
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : FromPbDecEnv (pbToProtoPolyDecoder d) evs2)
    (h3 : FreeOnlyEvs evs3) :
    Ct1AcknowledgedUcSomeEnv F u (some d) (evs1 ++ evs2 ++ evs3) := by
  unfold Ct1AcknowledgedUcSomeEnv
  rw [hok]
  exact ⟨evs1, evs2, evs3, h1, h2, h3, rfl⟩

theorem fitsEnv_ct1SentPre_of_ucSomeEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent} {optDec : Option PolynomialDecoder}
    (hfits : FitsEnv M lim st (Ct1AcknowledgedUcSomeEnv F u optDec)) :
    FitsEnv M lim st (Ct1SentFromPbPreEnv F u) := by
  intro evs1 hevs1
  subst hevs1
  apply hfits
  have h1 : Ct1SentFromPbPostEnv F u (ct1SentFromPbAllocEvents F u) :=
    ct1SentFromPbPostEnv_of_nil F u
  unfold Ct1AcknowledgedUcSomeEnv
  cases ct1SentFromPb (spqrAuthApi F) u with
  | error _ => exact ⟨_, [], h1, FreeOnlyEvs.nil, (List.append_nil _).symm⟩
  | ok _ =>
    cases optDec with
    | none => exact ⟨_, [], h1, FreeOnlyEvs.nil, (List.append_nil _).symm⟩
    | some d =>
      exact ⟨_, [], [], h1, fromPbDecAllocEnv_imp_fromPbDecEnv (Or.inl rfl), FreeOnlyEvs.nil, by simp⟩

theorem fitsEnv_decAlloc_step_of_ucSomeEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (d : PolynomialDecoder) {evs1 : List AllocEvent}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (hfits : FitsEnv M lim st (Ct1AcknowledgedUcSomeEnv F u (some d))) :
    FitsEnv M lim (M.stepEvents evs1 st) (FromPbDecAllocEnv (pbToProtoPolyDecoder d)) := by
  intro evs2 hevs2
  have hmem : Ct1AcknowledgedUcSomeEnv F u (some d) (evs1 ++ evs2) := by
    unfold Ct1AcknowledgedUcSomeEnv
    rw [hok]
    exact ⟨evs1, evs2, [], h1, fromPbDecAllocEnv_imp_fromPbDecEnv hevs2, FreeOnlyEvs.nil, by simp⟩
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfits (evs1 ++ evs2) hmem)).2

private theorem rawAuth_le_ct1Acknowledged_encodeRaw
    (st : V1State.Chunked.Ct1Acknowledged) (u : V1State.Unchunked.Ct1Sent)
    (auth : ProtoAuthenticator) (huc : st.uc = some u) (hauth : u.auth = some auth) :
    auth.rootKey.length + auth.macKey.length ≤
      (V1State.encodeRaw { innerState := some (.ct1Acknowledged st) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 st
  have h1 := length_le_encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw
    rawUcCt1Sent rawUcCt1Sent_le_encodeRaw 1#32 st.uc
  rw [huc] at h1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct1Acknowledged.encodeRaw, optRaw, rawUcCt1Sent, rawAuth] at h0 h1 ⊢
  rw [List.length_append, huc] at h0
  rw [hauth] at h1
  dsimp only [] at h1
  omega

private theorem sum_pts_le_polyDecoder_encodeRaw (d : PolynomialDecoder) :
    (d.pts.map List.length).sum ≤ (PolynomialDecoder.encodeRaw d).length := by
  unfold PolynomialDecoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 3#32 d.pts
  omega

private theorem sum_pts_le_ct1Acknowledged_encodeRaw
    (st : V1State.Chunked.Ct1Acknowledged) (d : PolynomialDecoder)
    (hdec : st.receivingEk = some d) :
    (d.pts.map List.length).sum ≤
      (V1State.encodeRaw { innerState := some (.ct1Acknowledged st) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 st
  have h1 := length_le_encodeOptMessage PolynomialDecoder.encodeRaw
    (fun m => (m.pts.map List.length).sum) sum_pts_le_polyDecoder_encodeRaw 2#32 st.receivingEk
  rw [hdec] at h1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct1Acknowledged.encodeRaw, optRaw] at h0 h1 ⊢
  rw [List.length_append, hdec] at h0
  omega

private theorem mem_length_le_sum_map {bs : List (BitVec 8)} {pts : List (List (BitVec 8))}
    (hmem : bs ∈ pts) :
    bs.length ≤ (pts.map List.length).sum := by
  induction pts with
  | nil => nomatch hmem
  | cons x xs ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.map_cons, List.sum_cons]
    rcases hmem with rfl | hmem'
    · omega
    · have := ih hmem'; omega

private theorem spqrBoundedEvs_sliceClone {bs : List (BitVec 8)} {B : Nat}
    (hb : bs.length ≤ B) (hmax : B ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 B (if bs = [] then [] else rustAllocEvents bs.length 1) := by
  split
  · exact SpqrBoundedEvs.nil 1 B
  · rename_i hne
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => contradiction
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hre : rustAllocEvents bs.length 1 = [.alloc bs.length] := by
      simp [rustAllocEvents, hpos]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans hb hmax, hb, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_ct1SentPostEnv {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {B : Nat} (hmax : B ≤ MallocngMaxAllocSize)
    (hauth_le : ∀ auth, u.auth = some auth → auth.rootKey.length + auth.macKey.length ≤ B)
    {evs : List AllocEvent} (hevs : Ct1SentFromPbPostEnv F u evs) :
    SpqrBoundedEvs 2 B evs := by
  rcases hevs with ⟨evsFree, hfree, rfl⟩
  have halloc : SpqrBoundedEvs 2 B (ct1SentFromPbAllocEvents F u) := by
    unfold ct1SentFromPbAllocEvents
    cases ct1SentFromPb (spqrAuthApi F) u with
    | error _ => exact SpqrBoundedEvs.nil 2 B
    | ok _ =>
      cases hauth : u.auth with
      | none => exact SpqrBoundedEvs.nil 2 B
      | some auth =>
        have hle := hauth_le auth hauth
        unfold authFromPbAllocEvents
        have h1 := spqrBoundedEvs_sliceClone (bs := auth.rootKey) (B := B) (by omega) hmax
        have h2 := spqrBoundedEvs_sliceClone (bs := auth.macKey) (B := B) (by omega) hmax
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h1 h2)
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append halloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_fromPbDecSlot {bs : List (BitVec 8)} {B : Nat}
    (hmod : (bs.length % 4 == 0) = true) (hb : bs.length ≤ B)
    (hmax : B ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 B (fromPbDecSlotEvents bs) := by
  unfold fromPbDecSlotEvents
  split
  · exact SpqrBoundedEvs.nil 1 B
  · rename_i hempty
    have hpos : 0 < bs.length := by
      cases bs with
      | nil => exact False.elim (hempty rfl)
      | cons _ _ => exact Nat.succ_pos _
    have hmod0 : bs.length % 4 = 0 := beq_iff_eq.mp hmod
    have hge2 : 2 ≤ bs.length := by omega
    have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
      simp [rustAllocEvents, hge2]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans hb hmax, hb, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_slot :
    ∀ (xs : List (List (BitVec 8))) {B : Nat},
      B ≤ MallocngMaxAllocSize →
      (∀ bs ∈ xs, (bs.length % 4 == 0) = true ∧ bs.length ≤ B) →
      SpqrBoundedEvs xs.length B (xs.flatMap fromPbDecSlotEvents)
  | [], _, _, _ => SpqrBoundedEvs.nil 0 _
  | bs :: rest, B, hmax, hall => by
    simp only [List.flatMap_cons, List.length_cons]
    have ⟨hm0, hb0⟩ := hall bs List.mem_cons_self
    have hhead := spqrBoundedEvs_fromPbDecSlot hm0 hb0 hmax
    have htail := spqrBoundedEvs_flatMap_slot rest hmax
      (fun x hx => hall x (List.mem_cons_of_mem bs hx))
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hhead htail)

private theorem takeWhile_length_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.takeWhile]
    split
    · simp only [List.length_cons]; exact Nat.succ_le_succ (takeWhile_length_le p xs)
    · exact Nat.zero_le _

private theorem mem_and_pred_of_mem_takeWhile {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ xs.takeWhile p → x ∈ xs ∧ p x = true
  | [], h => by simp [List.takeWhile] at h
  | y :: ys, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hy
      simp only [List.mem_cons] at h ⊢
      rcases h with rfl | h'
      · exact ⟨Or.inl rfl, hy⟩
      · rcases mem_and_pred_of_mem_takeWhile h' with ⟨hm, hp⟩
        exact ⟨Or.inr hm, hp⟩
    · simp at h

private theorem spqrBoundedEvs_fromPbDecEnv {d : ProtoPolynomialDecoder} {B : Nat}
    (hmax : B ≤ MallocngMaxAllocSize) (hsum : (d.pts.map List.length).sum ≤ B)
    {evs : List AllocEvent} (hevs : FromPbDecEnv d evs) :
    SpqrBoundedEvs 16 B evs := by
  rcases hevs with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hb_alloc : SpqrBoundedEvs 16 B evs_alloc := by
    rcases halloc with rfl | ⟨hlen16, rfl⟩
    · exact SpqrBoundedEvs.nil 16 B
    · unfold fromPbDecLoopAllocEvents
      have htw := spqrBoundedEvs_flatMap_slot
        (d.pts.takeWhile (fun bs => bs.length % 4 == 0)) hmax fun bs hbs => by
          rcases mem_and_pred_of_mem_takeWhile hbs with ⟨hmem, hmod⟩
          exact ⟨hmod, Nat.le_trans (mem_length_le_sum_map hmem) hsum⟩
      have hlen_le : (d.pts.takeWhile (fun bs => bs.length % 4 == 0)).length ≤ 16 :=
        hlen16 ▸ takeWhile_length_le _ d.pts
      exact SpqrBoundedEvs.mono hlen_le (Nat.le_refl B) htw
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append hb_alloc (SpqrBoundedEvs.of_freeOnly hfree))

/-- Subsumption of `Ct1AcknowledgedFromPbEnv F st` into the canonical `StatesFromPbEnv` envelope. -/
theorem ct1AcknowledgedFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} (F : ShaCompress)
    (st : V1State.Chunked.Ct1Acknowledged)
    (hfits : FitsEnv M lim st0 (StatesFromPbEnv { innerState := some (.ct1Acknowledged st) }))
    {evs : List AllocEvent} (hevs : Ct1AcknowledgedFromPbEnv F st evs) :
    StatesFromPbEnv { innerState := some (.ct1Acknowledged st) } evs := by
  let pb : V1State := { innerState := some (.ct1Acknowledged st) }
  let B := (V1State.encodeRaw pb).length
  change SpqrBoundedEvs 128 (4 * B + 4096) evs
  let m := min B MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv pb [.alloc m] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) (by omega),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hm_fit : FitsEvents M lim st0 [.alloc m] := hfits [.alloc m] hm_env
  rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st0 := M.req_le_stepReserve (.alloc m) st0
  have hmax : B ≤ MallocngMaxAllocSize := by
    dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
    omega
  unfold Ct1AcknowledgedFromPbEnv at hevs
  cases hdec : st.receivingEk <;> rw [hdec] at hevs <;>
    cases huc : st.uc <;> rw [huc] at hevs
  · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  · rename_i u
    dsimp only [Ct1AcknowledgedUcSomeEnv] at hevs
    cases hct : ct1SentFromPb (spqrAuthApi F) u with
    | error _ =>
      rw [hct] at hevs; dsimp only at hevs
      rcases hevs with ⟨evs1, evs2, h1, h2, rfl⟩
      have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax
        (fun auth ha => rawAuth_le_ct1Acknowledged_encodeRaw st u auth huc ha) h1
      exact SpqrBoundedEvs.mono (by decide) (by omega)
        (SpqrBoundedEvs.append hb1 (SpqrBoundedEvs.of_freeOnly h2))
    | ok _ =>
      rw [hct] at hevs; dsimp only at hevs
      rcases hevs with ⟨evs1, evs2, h1, h2, rfl⟩
      have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax
        (fun auth ha => rawAuth_le_ct1Acknowledged_encodeRaw st u auth huc ha) h1
      exact SpqrBoundedEvs.mono (by decide) (by omega)
        (SpqrBoundedEvs.append hb1 (SpqrBoundedEvs.of_freeOnly h2))
  · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  · dsimp only at hevs
    split at hevs
    · rename_i d u _
      dsimp only [Ct1AcknowledgedUcSomeEnv] at hevs
      cases hct : ct1SentFromPb (spqrAuthApi F) u with
      | error _ =>
        rw [hct] at hevs; dsimp only at hevs
        rcases hevs with ⟨evs1, evs2, h1, h2, rfl⟩
        have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax
          (fun auth ha => rawAuth_le_ct1Acknowledged_encodeRaw st u auth huc ha) h1
        exact SpqrBoundedEvs.mono (by decide) (by omega)
          (SpqrBoundedEvs.append hb1 (SpqrBoundedEvs.of_freeOnly h2))
      | ok _ =>
        rw [hct] at hevs; dsimp only at hevs
        rcases hevs with ⟨evs1, evs2, evs3, h1, h2, h3, rfl⟩
        have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax
          (fun auth ha => rawAuth_le_ct1Acknowledged_encodeRaw st u auth huc ha) h1
        have hpts_eq : (pbToProtoPolyDecoder d).pts = d.pts := rfl
        have hb2 := spqrBoundedEvs_fromPbDecEnv hmax
          (hpts_eq ▸ sum_pts_le_ct1Acknowledged_encodeRaw st d hdec) h2
        have hb12 := SpqrBoundedEvs.append hb1 hb2
        exact SpqrBoundedEvs.mono (by decide) (by omega)
          (SpqrBoundedEvs.append hb12 (SpqrBoundedEvs.of_freeOnly h3))
    · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)

theorem fitsEnv_ct1AcknowledgedFromPbEnv_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} (F : ShaCompress)
    (st : V1State.Chunked.Ct1Acknowledged)
    (hfits : FitsEnv M lim st0 (StatesFromPbEnv { innerState := some (.ct1Acknowledged st) })) :
    FitsEnv M lim st0 (Ct1AcknowledgedFromPbEnv F st) :=
  fun evs hevs => hfits evs (ct1AcknowledgedFromPbEnv_sub_statesFromPbEnv F st hfits hevs)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudgetAux
