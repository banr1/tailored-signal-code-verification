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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications & Prologue/Epilogue for `<States>::from_pb` (Block `333`)

Defines the `<PolyDecoder>::from_pb` budget contract bridge, the linear allocation envelope
`StatesFromPbEnv`, fixed-offset and `[LibsignalPlacement]` `RustCliAllocBudget M` specifications
for `<spqr::v1::chunked::states::States>::from_pb`, and pool-synchronized Block `333` prologue,
epilogue, and `None`-variant proofs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded blkPC_333 blkPl_333
   extract_withLsCodeLoaded libsignalSessionLib lsProg_333 lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (extHookStack tripleRatchetProgAtExt withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop
  (align_pre chunkedStatesAt chunkedStatesSize none2Cap none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize seq_clean)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.DecoderPb
  (FromPbDecGhost fromPbDecResult fromPbDecStack fromPbDec_eq_ok)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (DecoderFromPbGhost StatesFromPbGhost TraceCalleeSaved
   cell0_2296_entails_memRegion_2304 decoderFromPbName decoderFromPbResult decoderFromPbStack
   decoderFromPb_eq_ok memRegion_2304_split_cell0 memRegion_out_928_split_err
   resultChunkedStatesAt rodata_statesFromPbJumpTablePlacedAt
   sp_sub_2400_add_2304 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
   sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_2304 spqrErrorByte
   stackAt_statesFromPb_split_96 stackAt_statesFromPb_split_fsp stack_restore_statesFromPb
   statesFromPbJumpTableAt statesFromPbJumpTablePlacedAt statesFromPbName
   statesFromPbSavedCells statesFromPbStack statesFromPbStackX v1StatePtsBound)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecSpec fromPbDecSpecBase)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_2304 sp_sub_2400_add_2304
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Budget-Threaded `<PolyDecoder>::from_pb` Contract Bridge (`Block 376`) -/

theorem decoderFromPbStack_eq_fromPbDecStack :
    decoderFromPbStack = fromPbDecStack := rfl

theorem decoderFromPbResult_eq_fromPbDecResult (pb : ProtoPolynomialDecoder) :
    decoderFromPbResult pb = fromPbDecResult pb :=
  Except.ok.inj ((decoderFromPb_eq_ok pb).symm.trans (fromPbDec_eq_ok pb))

/-- Unplaced base specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb`
    over `DecoderFromPbGhost × M.σ` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def decoderFromPbSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp decoderFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (decoderFromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decoderFromPbStack

/-- Budget-threaded specification of `<spqr::encoding::polynomial::PolyDecoder>::from_pb`
    over `DecoderFromPbGhost × M.σ` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def decoderFromPbSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DecoderFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (FromPbDecAllocEnv x.pb) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out polyDecoderSize ∗
      protoPolynomialDecoderAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp decoderFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ FromPbDecEnv x.pb evs⌝ ∗
      resultPolyDecoderFromPbAt A.repAlloc x.out (decoderFromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialDecoderSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decoderFromPbStack

/-- `<PolyDecoder>::from_pb` meets `decoderFromPbSpecBase M A lim` on `tripleRatchetProgAtExt b ext`. -/
def DecoderFromPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr decoderFromPbName)
    (decoderFromPbSpecBase M A lim)

/-- `<PolyDecoder>::from_pb` (Block `376`) meets `withLsCodeLoaded lsmpl (decoderFromPbSpec M A lim)`
    on `lsProg_333 (Rust.withPanics ext)`. -/
def DecoderFromPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 376)
    (withLsCodeLoaded lsmpl (decoderFromPbSpec M A lim))

theorem decoderFromPbSpec_of_fromPbDecSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (fromPbDecSpecBase M A lim)) :
    subroutine_ok P addr (decoderFromPbSpecBase M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  let xg : FromPbDecGhost := ⟨x.out, x.pbA, x.pb⟩
  have hpre' : s0.mem ⊨ (fromPbDecSpecBase M A lim).pre (xg, st) s0 ∗ R := hpre
  refine h.mono_outcome (xg, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decoderFromPbSpecBase, fromPbDecSpecBase, xg] at hpost ⊢
    rwa [decoderFromPbResult_eq_fromPbDecResult x.pb]
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem withLsCodeLoaded_decoderFromPbSpec_of_fromPbDecSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (fromPbDecSpec M A lim))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (decoderFromPbSpec M A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  let xg : FromPbDecGhost := ⟨x.out, x.pbA, x.pb⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (fromPbDecSpec M A lim)).pre (xg, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre0⟩
  refine h.mono_outcome (xg, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, decoderFromPbSpec, fromPbDecSpec, xg] at hpost ⊢
    rwa [decoderFromPbResult_eq_fromPbDecResult x.pb]
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Allocation Envelope & Budget-Threaded `<States>::from_pb` Specifications (`Block 333`) -/

/-- Default allocation envelope of `<spqr::v1::chunked::states::States>::from_pb` (`Block 333`):
    `evs = []` when `pb.innerState = none`, and linearly bounded in the serialized `V1State` length
    when `pb.innerState = some _`. -/
def StatesFromPbEnv (pb : V1State) (evs : List AllocEvent) : Prop :=
  match pb.innerState with
  | none => evs = []
  | some _ => SpqrBoundedEvs 128 (4 * (V1State.encodeRaw pb).length + 4096) evs

theorem StatesFromPbEnv.nil (pb : V1State) : StatesFromPbEnv pb [] := by
  unfold StatesFromPbEnv
  cases pb.innerState
  · rfl
  · exact SpqrBoundedEvs.nil _ _

/-- Envelope-parametric fixed-offset specification of `<States>::from_pb` (`0x5a0a4`). -/
def statesFromPbSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (Env : V1State → List AllocEvent → Prop) : Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound x.pb ∧
      FitsEnv M lim st (Env x.pb)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack

/-- Fixed-offset budget specification of `<States>::from_pb` (`0x5a0a4`). -/
abbrev statesFromPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64) : Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbSpecOfEnv M A lim F b StatesFromPbEnv

/-- Envelope-parametric per-variant fixed-offset specification of `<States>::from_pb`. -/
def statesFromPbVariantSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (pb : V1State) (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, pbA⟩, st) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound pb ∧
      FitsEnv M lim st Env⌝ ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStack
  post := fun (⟨out, pbA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
      memRegion pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack

/-- Per-variant fixed-offset budget specification of `<States>::from_pb`. -/
abbrev statesFromPbVariantSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) (pb : V1State) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesFromPbVariantSpecOfEnv M A lim F b pb (StatesFromPbEnv pb)

/-- Envelope-parametric extended-stack fixed-offset specification of `<States>::from_pb`. -/
def statesFromPbSpecXOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64)
    (Env : V1State → List AllocEvent → Prop) : Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      b &&& 0xfff#64 = 0#64 ∧ v1StatePtsBound x.pb ∧
      FitsEnv M lim st (Env x.pb)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStackX

/-- Extended-stack fixed-offset budget specification of `<States>::from_pb`. -/
abbrev statesFromPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (b : BitVec 64) : Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbSpecXOfEnv M A lim F b StatesFromPbEnv

/-- `<States>::from_pb` meets `statesFromPbSpec M A lim F b` on `tripleRatchetProgAtExt b ext`. -/
def StatesFromPbOkExt (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
    (statesFromPbSpec M A lim F b)

/-- `<States>::from_pb` meets `(statesFromPbSpecX M A lim F img.base).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def StatesFromPbOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr statesFromPbName)
    ((statesFromPbSpecX M A lim F img.base).inImage img)

theorem statesFromPbSpecXOfEnv_of_statesFromPbSpecOfEnv
    {P : Program} {addr b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : V1State → List AllocEvent → Prop}
    (h : subroutine_ok P addr (statesFromPbSpecOfEnv M A lim F b Env)) :
    subroutine_ok P addr (statesFromPbSpecXOfEnv M A lim F b Env) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : statesFromPbStack ≤ statesFromPbStackX := by decide
  have hsplit : stackAt s0.sp statesFromPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX)
        (statesFromPbStackX - statesFromPbStack) ∗
        stackAt s0.sp statesFromPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesFromPbStack
      (statesFromPbStackX - statesFromPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX)
      (statesFromPbStackX - statesFromPbStack) ∗ R
  have hpre' : s0.mem ⊨ (statesFromPbSpecOfEnv M A lim F b Env).pre (x, st) s0 ∗ R' := by
    dsimp only [statesFromPbSpecXOfEnv, statesFromPbSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesFromPbSpecXOfEnv, statesFromPbSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem statesFromPbSpecX_of_statesFromPbSpec
    {P : Program} {addr b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesFromPbSpec M A lim F b)) :
    subroutine_ok P addr (statesFromPbSpecX M A lim F b) :=
  statesFromPbSpecXOfEnv_of_statesFromPbSpecOfEnv h

/-- Envelope-parametric relocatable specification of `<States>::from_pb` (`Block 333`)
    carrying `statesFromPbJumpTablePlacedAt` explicitly. -/
def statesFromPbPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : V1State → List AllocEvent → Prop) : Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      v1StatePtsBound x.pb ∧ FitsEnv M lim st (Env x.pb)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack

/-- Relocatable budget specification of `<States>::from_pb` (`Block 333`). -/
abbrev statesFromPbPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbPlacedSpecOfEnv M A lim F StatesFromPbEnv

/-- Envelope-parametric per-variant relocatable specification of `<States>::from_pb` (`Block 333`). -/
def statesFromPbVariantPlacedSpecOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (pb : V1State) (Env : List AllocEvent → Prop) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) where
  pre := fun (⟨out, pbA⟩, st) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = pbA ∧
      v1StatePtsBound pb ∧ FitsEnv M lim st Env⌝ ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStack
  post := fun (⟨out, pbA⟩, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
      memRegion pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack

/-- Per-variant relocatable budget specification of `<States>::from_pb` (`Block 333`). -/
abbrev statesFromPbVariantPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (pb : V1State) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesFromPbVariantPlacedSpecOfEnv M A lim F pb (StatesFromPbEnv pb)

/-- Envelope-parametric extended-stack relocatable specification of `<States>::from_pb` (`Block 333`)
    carrying `statesFromPbJumpTablePlacedAt` explicitly. -/
def statesFromPbPlacedSpecXOfEnv [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : V1State → List AllocEvent → Prop) : Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      v1StatePtsBound x.pb ∧ FitsEnv M lim st (Env x.pb)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStackX

/-- Extended-stack relocatable budget specification of `<States>::from_pb` (`Block 333`). -/
abbrev statesFromPbPlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbPlacedSpecXOfEnv M A lim F StatesFromPbEnv

/-- Envelope-parametric `.rodata`-free extended-stack relocatable specification of `<States>::from_pb`
    (`Block 333`) for callers discharging `statesFromPbJumpTablePlacedAt` via `LibsignalRoLoaded`. -/
def statesFromPbPlacedRoFreeSpecXOfEnv (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : V1State → List AllocEvent → Prop) : Spec (StatesFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbA ∧
      v1StatePtsBound x.pb ∧ FitsEnv M lim st (Env x.pb)⌝ ∗
      memRegion x.out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc x.pbA x.pb.innerState ∗
      A.pool lim st s ∗ stackAt s.sp statesFromPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
      resultChunkedStatesAt A.repAlloc (F := F) x.out (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA optProtoInnerStateSize ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStackX

/-- `.rodata`-free extended-stack relocatable budget specification of `<States>::from_pb`. -/
abbrev statesFromPbPlacedRoFreeSpecX (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (StatesFromPbGhost × M.σ) :=
  statesFromPbPlacedRoFreeSpecXOfEnv M A lim F StatesFromPbEnv

/-- `<States>::from_pb` (`Block 333`) meets `withLsCodeLoaded lsmpl (statesFromPbPlacedSpec M A lim F)`
    on `lsProg_333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeLoaded lsmpl (statesFromPbPlacedSpec M A lim F))

/-- `<States>::from_pb` (`Block 333`) meets `withLsCodeLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)`
    on `lsProg_333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOkExt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecX M A lim F))

/-- `<States>::from_pb` (`Block 333`) meets `withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)`
    on `libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext)`. -/
def StatesFromPbPlacedOkX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
    (lsmpl.base 333)
    (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F))

theorem statesFromPbPlacedSpecXOfEnv_of_statesFromPbPlacedSpecOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : V1State → List AllocEvent → Prop}
    (h : subroutine_ok P addr (statesFromPbPlacedSpecOfEnv M A lim F Env)) :
    subroutine_ok P addr (statesFromPbPlacedSpecXOfEnv M A lim F Env) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : statesFromPbStack ≤ statesFromPbStackX := by decide
  have hsplit : stackAt s0.sp statesFromPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX)
        (statesFromPbStackX - statesFromPbStack) ∗
        stackAt s0.sp statesFromPbStack := by
    have h1 := stackAt_split_bottom s0.sp statesFromPbStack
      (statesFromPbStackX - statesFromPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 statesFromPbStackX)
      (statesFromPbStackX - statesFromPbStack) ∗ R
  have hpre' : s0.mem ⊨ (statesFromPbPlacedSpecOfEnv M A lim F Env).pre (x, st) s0 ∗ R' := by
    dsimp only [statesFromPbPlacedSpecXOfEnv, statesFromPbPlacedSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [statesFromPbPlacedSpecXOfEnv, statesFromPbPlacedSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem statesFromPbPlacedSpecX_of_statesFromPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesFromPbPlacedSpec M A lim F)) :
    subroutine_ok P addr (statesFromPbPlacedSpecX M A lim F) :=
  statesFromPbPlacedSpecXOfEnv_of_statesFromPbPlacedSpecOfEnv h

/-- Symbol name of Rust `__rust_dealloc` hook. -/
abbrev spqrRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-- Relocatable (`[LibsignalPlacement]`) bundle of the allocator/memory hook contracts needed
    inside Block `333` (`<spqr::v1::chunked::states::States>::from_pb`). -/
structure FromPbAllocHooksPlacedBudget [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  shim_ok :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec
  alloc_ok :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false)
  dealloc_ok :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim)
  memcpy_ok :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec
  panic_ok :
    (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked

/-! ## 3. Pool-Synchronized Relocatable Prologue (`+0 -> +36`), Epilogue (`+64 -> ret`), and `None` Path (Block `333`) -/

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

/-- Pool-synchronized relocatable prologue (`+0 -> +36` in Block `333`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96` and `sp = s0.sp - 2400`,
    stores `0#64` at `[sp, #0]`, and transports `A.pool lim st s0` to `A.pool lim st s1`. -/
theorem states_from_pb_prologue_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 : State) (out pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = lsmpl.base 333)
    (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = out)
    (hx0 : s0.readReg64 .x0 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 36#64) s0
      (stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
          statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 2400#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x8 = out ∧
        s1.readReg64 .x0 = pbA ∧
        TraceCalleeSaved s1 s0 ∧
        VmPreserved s0 s1) := by
  change s0.pc = (blkPl_333).base at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 36#64) s0 _ _
  have hwp : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 36#64) s0
      (stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
          statesFromPbSavedCells s0 ∗ A.pool lim st s0 ∗ Rest) ∧
        (s1.sp = s0.sp - 2400#64 ∧
         s1.readReg64 .x29 = s0.sp - 96#64 ∧
         s1.readReg64 .x8 = out ∧
         s1.readReg64 .x0 = pbA ∧
         TraceCalleeSaved s1 s0)) := by
    rw [stackAt_statesFromPb_split_96 s0.sp, stackAt_statesFromPb_split_fsp s0.sp,
        memRegion_2304_split_cell0 (s0.sp - 2400#64)]
    cells_unfold
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w0
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w4
    apply ProofLib.SepWP.exists_left; intro w5
    apply ProofLib.SepWP.exists_left; intro w6
    apply ProofLib.SepWP.exists_left; intro w7
    apply ProofLib.SepWP.exists_left; intro w8
    apply ProofLib.SepWP.exists_left; intro w9
    apply ProofLib.SepWP.exists_left; intro w10
    apply ProofLib.SepWP.exists_left; intro w11
    apply ProofLib.SepWP.exists_left; intro v_fsp0
    by_vm_steps (
      wp_steps
      refine align_entails_vm ?_ ?_
      · unfold statesFromPbSavedCells
        dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done)
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hvm1, hP1, hsp1, hx29, hx8_1, hx0_1, htr1⟩ => ?_
  refine ⟨?_, hsp1, hx29, hx8_1, hx0_1, htr1, hvm1⟩
  rw [A.pool_of_vmPreserved hvm1]
  exact hP1

/-- Pool-synchronized relocatable epilogue (`+64 -> s0.lr` in Block `333`):
    adds `2304` to `sp`, restores `x19..x30` from `s0.sp - 96`, executes `ret`,
    and transports `A.pool lim st s` to `A.pool lim st sf`. -/
theorem states_from_pb_epilogue_64_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp statesFromPbStack ∗ A.pool lim st sf ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace ∧
        VmPreserved s sf) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  change s.pc = (blkPl_333).base + 64#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (s0.readReg64 .x30) s _ _
  have hwp : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp statesFromPbStack ∗ A.pool lim st s ∗ Rest) ∧
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace)) := by
    conv => arg 4; unfold statesFromPbSavedCells
    by_vm_steps (
      wp_steps
      refine align_entails_vm ?_ ?_
      · have hrest := stack_restore_statesFromPb s0
        unfold statesFromPbSavedCells at hrest
        dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at hrest ⊢
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion (s0.sp - 2400#64) 2304 ∗
             (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
              ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
              ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
              ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
              ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ (A.pool lim st s ∗ Rest) by sep_ac_rfl))
          (sepConj_mono_left hrest)
      · wp_done)
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hvm_f, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
  refine ⟨?_, hsp_f, hcs_f, htr_f, hvm_f⟩
  rw [A.pool_of_vmPreserved hvm_f]
  exact hPf

/-- Pool-synchronized relocatable `None` error path (`+36 -> s0.lr` in Block `333`):
    when `pb.innerState = none`, `[pbA] = none2Cap` (`-2`), writes `Err(Error::StateDecode)` at
    `out` with `0` allocator events (`M.stepEvents [] st = st`) and returns via `+64..+92`. -/
theorem states_from_pb_none_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htrace1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
        memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA none ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents [] st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace ∧
        VmPreserved s1 sf) := by
  rcases htrace1 with ⟨htrace1, hvregs1⟩
  have hnone_pb : optProtoInnerStateAt A.repAlloc pbA none =
      ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) := rfl
  rw [hnone_pb, memRegion_out_928_split_err out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro b_out8
  apply ProofLib.SepWP.exists_left; intro v_out0
  let Pre1 : SepProp :=
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v_out0) ∗
      ((out + 8#64) ↦₈ b_out8) ∗
      memRegion (out + 9#64) 919 ∗
      (pbA ↦₆₄ none2Cap) ∗
      memRegion (pbA + 8#64) 216 ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1
  have hleg1 : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64) s1
      Pre1
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ A.pool lim st sm ∗
          (resultChunkedStatesAt A.repAlloc (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
           memRegion pbA optProtoInnerStateSize ∗
           statesFromPbJumpTablePlacedAt)) ∧
        sm.sp = s0.sp - 2400#64 ∧ TraceCalleeSaved sm s0 ∧ VmPreserved s1 sm) := by
    change s1.pc = (blkPl_333).base + 36#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 64#64) s1 Pre1 _
    have hwp1 : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 64#64) s1
        Pre1
        (fun sm Pm =>
          VmPreserved s1 sm ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 2304 ∗
            statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
            (resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
             memRegion pbA optProtoInnerStateSize ∗
             statesFromPbJumpTablePlacedAt)) ∧
          (sm.sp = s0.sp - 2400#64 ∧ TraceCalleeSaved sm s0)) := by
      dsimp only [Pre1]
      by_vm_steps (
        wp_steps
        refine align_entails_vm ?_ ?_
        · dsimp only [States.from_pb, resultChunkedStatesAt, spqrErrorByte, optProtoInnerStateSize]
          have hpb : (pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216 ⊢ memRegion pbA 224 := by
            rw [ProofLib.memRegion_split pbA 8 216 (by decide)]
            exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion pbA none2Cap)
          have hfsp := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
          refine Entails.trans
            (Entails.of_eq (show _ =
              (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
              ((pbA ↦₆₄ none2Cap) ∗ memRegion (pbA + 8#64) 216) ∗
              (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               statesFromPbSavedCells s0 ∗
               (out ↦₆₄ 18446744073709551615#64) ∗
               ((out + 8#64) ↦₈ 0#8) ∗
               memRegion (out + 9#64) 919 ∗
               statesFromPbJumpTablePlacedAt ∗
               A.pool lim st s1) by sep_ac_rfl)) ?_
          refine Entails.trans (sepConj_mono hfsp (sepConj_mono_left hpb)) ?_
          unfold noneCap
          exact Entails.of_eq (by sep_ac_rfl)
        · wp_done)
    refine SepWP.mono hwp1 fun sm Pm _ _ ⟨hvm_m, hPm, hsp_m, htr_m⟩ => ?_
    refine ⟨?_, hsp_m, htr_m, hvm_m⟩
    rw [A.pool_of_vmPreserved hvm_m]
    exact hPm
  refine SepWP.seq hleg1 fun s2 Pm hpc2 hrun2 ⟨hPm, hsp2, htr2, hvm12⟩ => ?_
  refine SepWP.weaken_pre hPm ?_
  have hep := states_from_pb_epilogue_64_placed (ext := ext) A lim st s0 s2
    (resultChunkedStatesAt A.repAlloc (F := F) out
      (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := none }) ∗
     memRegion pbA optProtoInnerStateSize ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc2 hrun2 hsp2 htr2
  refine SepWP.mono hep ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, hvm2f⟩
  refine ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [AllocCostModel.stepEvents]; sep_ac_rfl)),
    hsp_f, hcc_f, htr_f, hvm12.trans hvm2f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` (with existential `evs` satisfying `Env`)
    into a `SepWPp` for `statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env`. -/
theorem sepWPp_of_states_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env).post ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env).onPanic ((out, pbA), st) s0 sf ∗ R)) := by
  refine SepWPp.of_sepWP (SepWP.mono h fun sf Pf hpcf hrunf ⟨⟨evs, henv, hPf⟩, hspf, hcs, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [statesFromPbVariantPlacedSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, henv⟩, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

/-- Convert a clean exit `SepWP` to `s0.readReg64 .x30` into a `SepWPp` for
    `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)`. -/
theorem sepWPp_of_states_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (Env : List AllocEvent → Prop)
    (P R : SepProp)
    (h : SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)).post ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)).onPanic ((out, pbA), st) s0 sf ∗ R)) :=
  sepWPp_of_states_exit_placed st s0 s out pbA pb Env P R h

/-- Envelope-parametric `subroutine_ok` for the `None` variant (`pb = { innerState := none }`)
    for any `Env` containing `[]`. -/
theorem states_from_pb_none_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} {Env : List AllocEvent → Prop}
    (hnil : Env []) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := none } Env) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, _, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA none ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA none ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine SepWPp.of_sepWP (SepWP.mono hpro fun s1 P1 hpc1 hrun1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩ => ?_)
  have hP1' : P1 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA none ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s1 :=
    Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))
  refine SepWPp.weaken_pre hP1' ?_
  have hnone := states_from_pb_none_step_placed (A := A) (lim := lim) (F := F) (ext := ext)
    st s0 s1 out pbA hsp0_align hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_of_states_exit_placed st s0 s1 out pbA { innerState := none } Env _ R ?_
  refine SepWP.mono hnone fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, _⟩ => ?_
  exact ⟨⟨[], hnil, hPf⟩, hsp_f, hcc_f, htr_f⟩

/-- `subroutine_ok` for the `None` variant (`pb = { innerState := none }`) with
    `statesFromPbVariantPlacedSpec`. -/
theorem states_from_pb_none_placed_ok_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (statesFromPbVariantPlacedSpec M A lim F { innerState := none }) :=
  states_from_pb_none_placed_ok_of_env rfl

/-- `subroutine_ok` for the `None` variant (`pb = { innerState := none }`) with `withLsCodeLoaded`. -/
theorem states_from_pb_none_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec M A lim F { innerState := none })) :=
  subroutine_ok_withLsCodeLoaded_of_plain states_from_pb_none_placed_ok_raw

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
