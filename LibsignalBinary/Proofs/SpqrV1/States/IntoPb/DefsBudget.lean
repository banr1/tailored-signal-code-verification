/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications, Prologue, and Epilogue for `<States>::into_pb` (Block `334`)

Fixed-offset and relocatable (`[LibsignalPlacement]`) `RustCliAllocBudget M` specifications,
`.rodata`-free `LibsignalRoLoaded` lifts, `StatesIntoPbAllocPlacedBudget` hook bundle, and
pool-synchronized prologue (`+0 -> +44 -> +60`) and common epilogue (`+1544 -> ret`) for
`<spqr::v1::chunked::states::States>::into_pb`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
   extract_withLsCodeLoaded libsignalSessionCode lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (extHookStack tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly.DecoderPb (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Drop
  (align_pre chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (StatesIntoPbGhost TraceCalleeSaved epilogueStagingCells
   epilogueStagingCells_entails_memRegion lsro_statesIntoPbJumpTablePlacedAt
   memRegion_out_224_eq outWords28
   sp_sub_1520_add_1424 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
   sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160
   stackAt_statesIntoPb_split_96 stackAt_statesIntoPb_split_fsp
   stack_restore_statesIntoPb statesIntoPbJumpTableAt
   statesIntoPbJumpTablePlacedAt statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack statesIntoPbStackX)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)

export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (nonFreeCount SpqrBoundedEvs StatesIntoPbEnv statesIntoPbPlacedSpecOfEnv)
export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (statesIntoPbPlacedSpec statesIntoPbVariantPlacedSpecOfEnv statesIntoPbVariantPlacedSpec
   statesIntoPbPlacedSpecXOfEnv statesIntoPbPlacedSpecX)
export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (StatesIntoPbPlacedOkX)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160
  sp_sub_1520_add_1424
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Fixed-Offset & Relocatable Budget Specifications (`Block 334`) -/

/-- Envelope-parametric fixed-offset specification of `<States>::into_pb` (`0x5ce20`). -/
def statesIntoPbSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      b &&& 0xfff#64 = 0#64 ∧ FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc x.stA x.st ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

/-- Fixed-offset budget specification of `<States>::into_pb` (`0x5ce20`). -/
abbrev statesIntoPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64) : Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbSpecOfEnv M A lim F b StatesIntoPbEnv

/-- Envelope-parametric per-variant fixed-offset specification of `<States>::into_pb`. -/
def statesIntoPbVariantSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, stA⟩, st) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = stA ∧
      b &&& 0xfff#64 = 0#64 ∧ FitsEnv M lim st Env⌝ ∗
      memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA stateVal ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStack
  post := fun (⟨out, stA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack

/-- Per-variant fixed-offset budget specification of `<States>::into_pb`. -/
abbrev statesIntoPbVariantSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantSpecOfEnv M A lim F b stateVal
    (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024))

/-- Envelope-parametric extended-stack fixed-offset specification of `<States>::into_pb`. -/
def statesIntoPbSpecXOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      b &&& 0xfff#64 = 0#64 ∧ FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc x.stA x.st ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStackX

/-- Extended-stack fixed-offset budget specification of `<States>::into_pb`. -/
abbrev statesIntoPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64) : Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbSpecXOfEnv M A lim F b StatesIntoPbEnv

/-- `<States>::into_pb` meets `statesIntoPbSpec M A lim F b` on `tripleRatchetProgAtExt b ext`. -/
def StatesIntoPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
    (statesIntoPbSpec M A lim F b)

/-- `<States>::into_pb` meets `(statesIntoPbSpecX M A lim F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def StatesIntoPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
    ((statesIntoPbSpecX M A lim F img.base).inImage img)

theorem statesIntoPbSpecXOfEnv_of_statesIntoPbSpecOfEnv
    {P : Program} {addr b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (statesIntoPbSpecOfEnv M A lim F b Env)) :
    subroutine_ok P addr (statesIntoPbSpecXOfEnv M A lim F b Env) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : statesIntoPbStack ≤ statesIntoPbStackX := by decide
  have hsplit : stackAt s0.sp statesIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
        (statesIntoPbStackX - statesIntoPbStack) ∗
        stackAt s0.sp statesIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesIntoPbStack
      (statesIntoPbStackX - statesIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
      (statesIntoPbStackX - statesIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (statesIntoPbSpecOfEnv M A lim F b Env).pre (x, st) s0 ∗ R' := by
    dsimp only [statesIntoPbSpecXOfEnv, statesIntoPbSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesIntoPbSpecXOfEnv, statesIntoPbSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem statesIntoPbSpecX_of_statesIntoPbSpec
    {P : Program} {addr b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbSpec M A lim F b)) :
    subroutine_ok P addr (statesIntoPbSpecX M A lim F b) :=
  statesIntoPbSpecXOfEnv_of_statesIntoPbSpecOfEnv h

theorem statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (statesIntoPbPlacedSpecOfEnv M A lim F Env)) :
    subroutine_ok P addr (statesIntoPbPlacedSpecXOfEnv M A lim F Env) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : statesIntoPbStack ≤ statesIntoPbStackX := by decide
  have hsplit : stackAt s0.sp statesIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
        (statesIntoPbStackX - statesIntoPbStack) ∗
        stackAt s0.sp statesIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesIntoPbStack
      (statesIntoPbStackX - statesIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesIntoPbStackX)
      (statesIntoPbStackX - statesIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (statesIntoPbPlacedSpecOfEnv M A lim F Env).pre (x, st) s0 ∗ R' := by
    dsimp only [statesIntoPbPlacedSpecXOfEnv, statesIntoPbPlacedSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesIntoPbPlacedSpecXOfEnv, statesIntoPbPlacedSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem statesIntoPbPlacedSpecX_of_statesIntoPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbPlacedSpec M A lim F)) :
    subroutine_ok P addr (statesIntoPbPlacedSpecX M A lim F) :=
  statesIntoPbPlacedSpecXOfEnv_of_statesIntoPbPlacedSpecOfEnv h

/-- Envelope-parametric `.rodata`-free extended-stack relocatable specification of `<States>::into_pb`
    (`Block 334`), where `statesIntoPbJumpTablePlacedAt` is discharged from `LibsignalRoLoaded`. -/
def statesIntoPbPlacedRoFreeSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : StatesIntoPbGhost F → List AllocEvent → Prop) :
    Spec (StatesIntoPbGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.stA ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc x.stA x.st ∗
      A.pool lim st s ∗ stackAt s.sp statesIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
      memRegion x.stA chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStackX

/-- `.rodata`-free extended-stack relocatable budget specification of `<States>::into_pb`. -/
abbrev statesIntoPbPlacedRoFreeSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesIntoPbGhost F × M.σ) :=
  statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F StatesIntoPbEnv

/-- `<States>::into_pb` (`Block 334`) meets `withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F)`
    on `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))

/-- `<States>::into_pb` (`Block 334`) meets
    `withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecX M A lim F)` on
    `(blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)`. -/
def StatesIntoPbPlacedRoFreeOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecX M A lim F))

/-- Discharge `statesIntoPbJumpTablePlacedAt` from `LibsignalCodeRoLoaded lsmpl s0.mem`. -/
theorem statesIntoPbPlacedRoFreeSpecXOfEnv_of_placedSpecXOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : StatesIntoPbGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl, hro⟩, hpre0⟩ := hpre
  have hjt : s0.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
      ((statesIntoPbPlacedRoFreeSpecXOfEnv M A lim F Env).pre (x, st) s0 ∗ R) :=
    lsro_statesIntoPbJumpTablePlacedAt (s := s0) hro hpre0
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F Env)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [statesIntoPbPlacedSpecXOfEnv, statesIntoPbPlacedRoFreeSpecXOfEnv] at hjt ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hjt
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withLsCodeLoaded,
      statesIntoPbPlacedRoFreeSpecXOfEnv, statesIntoPbPlacedSpecXOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    have hpost_reord : sf.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
        ((⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
          optProtoInnerStateAt A.repAlloc x.out x.st.into_pb.innerState ∗
          memRegion x.stA chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact Satisfies.of_sep_right hpost_reord
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Relocatable (`[LibsignalPlacement]`) bundle of the allocator/memory hook contracts needed
    inside Block `334` (`<spqr::v1::chunked::states::States>::into_pb`). -/
structure StatesIntoPbAllocPlacedBudget [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec
  alloc_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false)
  dealloc_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)
  memcpy_ok :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec
  panic_ok :
    (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked

/-! ## 2. Pool-Synchronized Prologue (`+0 -> +44`), Extended Prologue (`+0 -> +60`), Common Epilogue (`+1544 -> ret`), and Exit Adapter -/

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

/-- Pool-synchronized relocatable prologue (`+0 -> +44` in Block `334`). -/
theorem states_into_pb_prologue_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (out stA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_334).base)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 44#64) s0
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
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 44#64) s0
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
    by_vm_steps (
      wp_steps
      refine align_entails_vm ?_ ?_
      · unfold statesIntoPbSavedCells
        dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hvm1, hP1, hsp1, hx29, hx28, hx19, hx0_1, htr1⟩ => ?_
  refine ⟨?_, hsp1, hx29, hx28, hx19, hx0_1, htr1, hvm1⟩
  rw [A.pool_of_vmPreserved hvm1]
  exact hP1

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` (with existential `evs` satisfying `Env`)
    into a `SepWPp` for `statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env`. -/
theorem sepWPp_of_states_into_pb_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
            memRegion stA chunkedStatesSize ∗
            statesIntoPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env).post ((out, stA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env).onPanic ((out, stA), st) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨⟨evs, henv, hPf⟩, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesIntoPbVariantPlacedSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for
    `withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env)`. -/
theorem sepWPp_of_states_into_pb_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
            memRegion stA chunkedStatesSize ∗
            statesIntoPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env)).post ((out, stA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpecOfEnv M A lim F stateVal Env)).onPanic ((out, stA), st) s0 sf ∗ R)) :=
  sepWPp_of_states_into_pb_exit_placed st s0 s out stA stateVal Env P R h

/-- Pool-synchronized relocatable extended prologue (`+0 -> +60` in Block `334`). -/
theorem states_into_pb_prologue_60_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (out stA tag : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_334).base)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = stA) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 60#64) s0
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
    rw [ProofLib.memRegion_split' (b := s0.sp - 1520#64) (n := 8) (k := 1416)
          (b' := s0.sp - 1512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1520#64) 1 (by decide)]
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      ((blkPl_334).base + 60#64) s0
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
    by_vm_steps (
      wp_steps
      refine align_entails_vm ?_ ?_
      · unfold statesIntoPbSavedCells
        dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  refine SepWP.mono hwp
    fun s1 P1 _ _ ⟨hvm1, hP1, hsp1, hx29, hx28, hx27, hx26, hx20, hx19, hx8_1, htr1⟩ => ?_
  refine ⟨?_, hsp1, hx29, hx28, hx27, hx26, hx20, hx19, hx8_1, htr1, hvm1⟩
  rw [A.pool_of_vmPreserved hvm1]
  exact hP1

/-- Pool-synchronized relocatable common epilogue (`+1544 -> s0.readReg64 .x30` in Block `334`). -/
theorem states_into_pb_epilogue_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (out : BitVec 64)
    (w8 w16 w24 w32 w40 w48
     w64 w72 w80 w88 w96 w104 w112 w120
     w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_334).base + 1544#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = out)
    (htr : TraceCalleeSaved s s0) :
    SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
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
  have hwp : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
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
    by_vm_steps (
      wp_steps
      refine align_entails_vm (Entails.trans ?_ hrestore) ?_
      · dsimp only [outWords28, epilogueStagingCells, statesIntoPbSavedCells,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  dsimp only [Rest'] at hwp
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hvm_f, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
  refine ⟨?_, hsp_f, hcs_f, htr_f, hvm_f⟩
  rw [A.pool_of_vmPreserved hvm_f]
  exact hPf

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
