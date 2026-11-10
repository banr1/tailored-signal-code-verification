/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Fixed-Offset Specifications for `spqr::init_inner` (`0x532dc`)

Defines fixed-offset envelope-parametric (`*OfEnv`) and default (`InitInnerEnv F`) budget
specifications for `spqr::init_inner` (`0x532dc`) at both `initInnerStack` (`17680`B) and
`initInnerStackExt` (`18912`B), together with stack-slack and envelope-weakening lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.IntoPb (statesIntoPbJumpTableAt)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initHdrDecoder initInnerFrame initInnerName initInnerResultAt
   initInnerResultAt_v0 initInnerResultAt_v1 initInnerStack initInnerStackExt
   initInnerStackExt_eq initInnerStackExt_eq_add initInnerStackX initInnerValue
   initInner_fnOff initInner_spqrDeps_eq_ok initV1State polyDecoderNew_96_eq
   spqrDeps_initV1Inner_eq_ok states_init_a_eq_ok states_init_b_eq_ok)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Re-Exports -/

export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (nonFreeCount nonFreeCount_nil nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)
export LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs StatesIntoPbEnv InitInnerEnv)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbSpecOfEnv statesIntoPbSpec statesIntoPbVariantSpecOfEnv statesIntoPbVariantSpec
   statesIntoPbSpecXOfEnv)
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (statesIntoPbSpecX StatesIntoPbOkExt StatesIntoPbOkX
   statesIntoPbSpecXOfEnv_of_statesIntoPbSpecOfEnv statesIntoPbSpecX_of_statesIntoPbSpec)

export CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initHdrDecoder initInnerFrame initInnerName initInnerResultAt)
export CryptoVerification.SpqrV1.Top.InitInner
  (initInnerResultAt_v0 initInnerResultAt_v1 initInnerStack initInnerStackExt
   initInnerStackExt_eq)
export CryptoVerification.SpqrV1.Top.InitInner
  (initInnerStackExt_eq_add initInnerStackX initInnerValue initInner_fnOff
   initInner_spqrDeps_eq_ok)
export CryptoVerification.SpqrV1.Top.InitInner
  (initV1State polyDecoderNew_96_eq spqrDeps_initV1Inner_eq_ok
   states_init_a_eq_ok states_init_b_eq_ok)

/-! ## 2. Fixed-Offset Budget Specifications for `spqr::init_inner` (`0x532dc`) -/

/-- Envelope-parametric fixed-offset Hoare specification of `spqr::init_inner` (`0x532dc`). -/
def initInnerSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStack

abbrev initInnerSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerSpecOfEnv M A lim F b (InitInnerEnv F)

/-- Envelope-parametric extended-stack fixed-offset specification of `spqr::init_inner`
    (`initInnerStackX = initInnerStack`). -/
def initInnerSpecXOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStackX

abbrev initInnerSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerSpecXOfEnv M A lim F b (InitInnerEnv F)

/-- `spqr::init_inner` meets `initInnerSpecOfEnv M A lim F b Env` on `tripleRatchetProgAtExt b ext`. -/
def InitInnerOkExtOfEnv (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (initInnerSpecOfEnv M A lim F b Env)

abbrev InitInnerOkExt (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitInnerOkExtOfEnv b M A lim F (InitInnerEnv F) ext

/-- `spqr::init_inner` meets `(initInnerSpecXOfEnv M A lim F img.base Env).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def InitInnerOkXOfEnv (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName)
    ((initInnerSpecXOfEnv M A lim F img.base Env).inImage img)

abbrev InitInnerOkX (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitInnerOkXOfEnv img M A lim F (InitInnerEnv F) ext

theorem initInnerSpecXOfEnv_of_initInnerSpecOfEnv
    {P : Program} {addr b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    (h : subroutine_ok P addr (initInnerSpecOfEnv M A lim F b Env)) :
    subroutine_ok P addr (initInnerSpecXOfEnv M A lim F b Env) :=
  h

theorem initInnerSpecX_of_initInnerSpec
    {P : Program} {addr b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (initInnerSpec M A lim F b)) :
    subroutine_ok P addr (initInnerSpecX M A lim F b) :=
  h

/-! ## 3. Contract-Backed (`initInnerStackExt = 18912`B) Specifications & Monotonicity -/

/-- Envelope-parametric contract-backed (`initInnerStackExt = 18912`B) specification of
    `spqr::init_inner`. -/
def initInnerSpecExtOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (Env : InitInnerGhost → List AllocEvent → Prop) :
    Spec (InitInnerGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧
      s.readReg32 .x1 = x.v.toI32 ∧
      s.readReg32 .x2 = x.d.toI32 ∧
      s.readReg64 .x3 = x.akPtr ∧
      s.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧
      32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.out optProtoInnerStateSize ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim st s ∗ stackAt s.sp initInnerStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStackExt

abbrev initInnerSpecExt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64) :
    Spec (InitInnerGhost × M.σ) :=
  initInnerSpecExtOfEnv M A lim F b (InitInnerEnv F)

/-- `spqr::init_inner` meets `initInnerSpecExtOfEnv M A lim F b Env` on
    `tripleRatchetProgAtExt b ext`. -/
def InitInnerBaseOkExtOfEnv (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (initInnerSpecExtOfEnv M A lim F b Env)

abbrev InitInnerBaseOkExt (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitInnerBaseOkExtOfEnv b M A lim F (InitInnerEnv F) ext

/-- `spqr::init_inner` meets `(initInnerSpecExtOfEnv M A lim F img.base Env).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def InitInnerOkXExtOfEnv (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : InitInnerGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName)
    ((initInnerSpecExtOfEnv M A lim F img.base Env).inImage img)

abbrev InitInnerOkXExt (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  InitInnerOkXExtOfEnv img M A lim F (InitInnerEnv F) ext

theorem stackAt_initInnerExt_split_base (sp : BitVec 64) :
    stackAt sp initInnerStackExt =
      stackAt sp initInnerStack ∗ memRegion (sp - 18912#64) 1232 := by
  change memRegion (sp - 18912#64) 18912 =
    memRegion (sp - 17680#64) 17680 ∗ memRegion (sp - 18912#64) 1232
  rw [@ProofLib.memRegion_split' (sp - 18912#64) (sp - 17680#64) 1232 17680 18912
        rfl (by bv_omega) (by decide), sepConj_comm]

theorem initInnerSpecExtOfEnv_of_initInnerSpecOfEnv
    {P : Program} {addr b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    (h : subroutine_ok P addr (initInnerSpecOfEnv M A lim F b Env)) :
    subroutine_ok P addr (initInnerSpecExtOfEnv M A lim F b Env) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  let R' : SepProp := memRegion (s0.sp - 18912#64) 1232 ∗ R
  have hpre' : s0.mem ⊨ (initInnerSpecOfEnv M A lim F b Env).pre (x, st) s0 ∗ R' := by
    dsimp only [initInnerSpecExtOfEnv, initInnerSpecOfEnv, R'] at hpre ⊢
    rw [stackAt_initInnerExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [initInnerSpecExtOfEnv, initInnerSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_initInnerExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem initInnerSpecExt_of_initInnerSpec
    {P : Program} {addr b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (initInnerSpec M A lim F b)) :
    subroutine_ok P addr (initInnerSpecExt M A lim F b) :=
  initInnerSpecExtOfEnv_of_initInnerSpecOfEnv h

/-- Stack-slack monotonicity: `InitInnerOkExtOfEnv` (`17680`B) implies `InitInnerBaseOkExtOfEnv` (`18912`B). -/
theorem InitInnerOkExtOfEnv.toBaseExt {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitInnerOkExtOfEnv b M A lim F Env ext) :
    InitInnerBaseOkExtOfEnv b M A lim F Env ext :=
  initInnerSpecExtOfEnv_of_initInnerSpecOfEnv h

/-- Stack-slack monotonicity: `InitInnerOkExt` (`17680`B) implies `InitInnerBaseOkExt` (`18912`B). -/
theorem InitInnerOkExt.toBaseExt {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : InitInnerOkExt b M A lim F ext) :
    InitInnerBaseOkExt b M A lim F ext :=
  InitInnerOkExtOfEnv.toBaseExt h

/-- Stack-slack monotonicity: `InitInnerOkXOfEnv` (`17680`B) implies `InitInnerOkXExtOfEnv` (`18912`B). -/
theorem InitInnerOkXOfEnv.toExt {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitInnerOkXOfEnv img M A lim F Env ext) :
    InitInnerOkXExtOfEnv img M A lim F Env ext := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  let R' : SepProp := memRegion (s0.sp - 18912#64) 1232 ∗ R
  have hpre' : s0.mem ⊨ ((initInnerSpecXOfEnv M A lim F img.base Env).inImage img).pre (x, st) s0 ∗ R' := by
    dsimp only [Spec.inImage, initInnerSpecExtOfEnv, initInnerSpecXOfEnv, R'] at hpre ⊢
    change _ at hpre ⊢
    rw [stackAt_initInnerExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, initInnerSpecExtOfEnv, initInnerSpecXOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_initInnerExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Stack-slack monotonicity: `InitInnerOkX` (`17680`B) implies `InitInnerOkXExt` (`18912`B). -/
theorem InitInnerOkX.toExt {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : InitInnerOkX img M A lim F ext) :
    InitInnerOkXExt img M A lim F ext :=
  InitInnerOkXOfEnv.toExt h

/-! ## 4. Envelope Weakening (`Env₁ → Env₂`) -/

theorem initInnerSpecOfEnv_mono_env
    {P : Program} {addr b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : InitInnerGhost → List AllocEvent → Prop}
    (himp : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (h : subroutine_ok P addr (initInnerSpecOfEnv M A lim F b Env₁)) :
    subroutine_ok P addr (initInnerSpecOfEnv M A lim F b Env₂) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (initInnerSpecOfEnv M A lim F b Env₁).pre (x, st) s0 ∗ R := by
    dsimp only [initInnerSpecOfEnv] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hw1, hw2, hx3, hx4, hne, hlt, hb, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hw1, hw2, hx3, hx4, hne, hlt, hb, FitsEnv.mono (himp x) hfits⟩, hmem⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [initInnerSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, henv1⟩, hmem⟩
    exact ⟨⟨htr, himp x evs henv1⟩, hmem⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem InitInnerOkExtOfEnv.mono_env {b : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : InitInnerGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (himp : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (h : InitInnerOkExtOfEnv b M A lim F Env₁ ext) :
    InitInnerOkExtOfEnv b M A lim F Env₂ ext :=
  initInnerSpecOfEnv_mono_env himp h

theorem InitInnerOkXOfEnv.mono_env {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : InitInnerGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (himp : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (h : InitInnerOkXOfEnv img M A lim F Env₁ ext) :
    InitInnerOkXOfEnv img M A lim F Env₂ ext := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((initInnerSpecXOfEnv M A lim F img.base Env₁).inImage img).pre (x, st) s0 ∗ R := by
    dsimp only [Spec.inImage, initInnerSpecXOfEnv] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, hpre⟩
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hw1, hw2, hx3, hx4, hne, hlt, hb, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hw1, hw2, hx3, hx4, hne, hlt, hb, FitsEnv.mono (himp x) hfits⟩, hmem⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, initInnerSpecXOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, henv1⟩, hmem⟩
    exact ⟨⟨htr, himp x evs henv1⟩, hmem⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsBudget
