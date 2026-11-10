/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Dispatch & Variant Composition for `<States>::from_pb` (Block `333`)

Provides `LibsignalCodeLoaded`-threading `SepWP -> SepWPp` sequencing helpers, envelope-parametric
prologue and jump-table dispatch combiners for Block `333`, Variant 0 (`KeysUnsampled`) re-exports,
and top-level reductions to `StatesFromPbPlacedOk*` and `.rodata`-free specifications.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_333
   extract_withLsCodeLoaded libsignalSessionLib lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost TaggedVariantDispatch TraceCalleeSaved
   cell0_2296_entails_memRegion_2304 resultChunkedStatesAt
   rodata_statesFromPbJumpTablePlacedAt statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack statesFromPbStackX v1StatePtsBound)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv statesFromPbPlacedRoFreeSpecX
   statesFromPbPlacedRoFreeSpecXOfEnv statesFromPbPlacedSpecOfEnv
   statesFromPbPlacedSpecXOfEnv statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_ct1Sampled_placed_budget
   states_from_pb_dispatch_tagged_placed_budget)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## 1. `SepWPp` Sequencing & Postcondition Helpers (`sfpProof_*_placed`) -/

/-- Sequence a clean `SepWP` step before a `SepWPp` continuation while threading
    `LibsignalCodeLoaded lsmpl`. -/
theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog target sm P_mid Q Qp) :
    SepWPp prog target s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-- State-indexed variant of `sepWPp_seq_clean_lscl` for continuations whose spatial assertion
    `P_mid sm` carries `A.pool lim st sm`. -/
theorem sepWPp_seq_clean_lscl_st [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm → SepWPp prog target sm (P_mid sm) Q Qp) :
    SepWPp prog target s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-- Convert a `SepWPp` with an `Entails`-based existential event postcondition into the
    `Satisfies`-based postcondition expected by `subroutine_ok_of_sepWPp` for
    `statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env`. -/
theorem sfpProof_sepWPp_of_states_body_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (Env : List AllocEvent → Prop) (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
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
        sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env).post ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env).onPanic
              ((out, pbA), st) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, ⟨⟨evs, henv, hPf⟩, hspf, hcs, htrf⟩⟩ | hpan⟩ :=
    h R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨fun hmem_f => ?_, hspf, hcs⟩⟩⟩
    dsimp only [statesFromPbVariantPlacedSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, henv⟩,
      Satisfies.mono
        (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem sfpProof_sepWPp_of_states_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, StatesFromPbEnv pb evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb).post
              ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb).onPanic
              ((out, pbA), st) s0 sf ∗ R)) :=
  sfpProof_sepWPp_of_states_body_placed_of_env st s0 s out pbA pb (StatesFromPbEnv pb) P R h

/-- Convert an `Entails`-based `SepWPp` body into the `Satisfies`-based `SepWPp` for
    `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)`. -/
theorem sfpProof_sepWPp_of_states_body_cl_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (Env : List AllocEvent → Prop) (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
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
        sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (withLsCodeLoaded lsmpl
              (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)).post ((out, pbA), st) s0 sf ∗
            R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeLoaded lsmpl
              (statesFromPbVariantPlacedSpecOfEnv M A lim F pb Env)).onPanic
              ((out, pbA), st) s0 sf ∗ R)) :=
  sfpProof_sepWPp_of_states_body_placed_of_env st s0 s out pbA pb Env P R h

theorem sfpProof_sepWPp_of_states_body_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64) (pb : V1State)
    (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (∃ evs : List AllocEvent, StatesFromPbEnv pb evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (withLsCodeLoaded lsmpl
              (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb)).post
              ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (withLsCodeLoaded lsmpl
              (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb)).onPanic
              ((out, pbA), st) s0 sf ∗ R)) :=
  sfpProof_sepWPp_of_states_body_placed st s0 s out pbA pb P R h

/-! ## 2. Canonical Per-Variant Step Shapes & Prologue+Dispatch Wrappers -/

alias StatesFromPbVariantStepPlaced := Variant1bPlacedBudget.StatesFromPbVariantStepPlaced
alias sfpProof_tagged_ok_of_step_placed_raw :=
  Variant1bPlacedBudget.sfpProof_tagged_ok_of_step_placed_raw
alias sfpProof_tagged_ok_of_step_placed := Variant1bPlacedBudget.sfpProof_tagged_ok_of_step_placed

/-- Post-dispatch `Satisfies`-form `SepWPp` obligation at offset `off` in Block `333` carrying
    `LibsignalCodeLoaded lsmpl s1.mem` for variants that make cross-block calls. -/
def StatesFromPbVariantStepClPlacedOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (inner : V1State.InnerState) (off : BitVec 64)
    (Env : List AllocEvent → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp),
    LibsignalCodeLoaded lsmpl s1.mem →
    FitsEnv M lim st Env →
    (s0.sp &&& 15#64 == 0#64) = true →
    s1.pc = lsmpl.base 333 + off →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env).post
              ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env).onPanic
            ((out, pbA), st) s0 sf ∗ R))

abbrev StatesFromPbVariantStepClPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (inner : V1State.InnerState) (off : BitVec 64) : Prop :=
  StatesFromPbVariantStepClPlacedOfEnv M A lim F ext inner off
    (StatesFromPbEnv { innerState := some inner })

/-- Post-dispatch `Entails`-form `SepWPp` obligation at offset `off` in Block `333` carrying
    `LibsignalCodeLoaded lsmpl s1.mem` and existential event witness `evs` in `Env`. -/
def StatesFromPbVariantBodyClPlacedOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (inner : V1State.InnerState) (off : BitVec 64)
    (Env : List AllocEvent → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp),
    LibsignalCodeLoaded lsmpl s1.mem →
    FitsEnv M lim st Env →
    (s0.sp &&& 15#64 == 0#64) = true →
    s1.pc = lsmpl.base 333 + off →
    s1.status = .Running →
    s1.sp = s0.sp - 2400#64 →
    s1.readReg64 .x19 = out →
    s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
    s1.readReg64 .x27 = pbA →
    TraceCalleeSaved s1 s0 →
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, Env evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some inner }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))

abbrev StatesFromPbVariantBodyClPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (inner : V1State.InnerState) (off : BitVec 64) : Prop :=
  StatesFromPbVariantBodyClPlacedOfEnv M A lim F ext inner off
    (StatesFromPbEnv { innerState := some inner })

/-- Lift a tagged-variant `StatesFromPbVariantStepClPlacedOfEnv` at `+off` (threading
    `LibsignalCodeLoaded lsmpl` through prologue and jump-table dispatch) to `subroutine_ok` for
    `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)`. -/
theorem sfpProof_tagged_ok_of_step_cl_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantStepClPlacedOfEnv M A lim F ext inner off Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl_st hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1, _⟩
  have hP1' :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
       statesFromPbJumpTablePlacedAt) ⊢
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail pbA) ∗
      A.pool lim st s1 := by
    rw [hinner pbA]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA tag off
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail pbA)
    htag hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_seq_clean_lscl_st hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join :
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail pbA) ∗
      A.pool lim st s2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    rw [hinner pbA]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (hstep hpts st s0 s2 out pbA R hcl2 hfits hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2)

theorem sfpProof_tagged_ok_of_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantStepClPlaced M A lim F ext inner off) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some inner })) :=
  sfpProof_tagged_ok_of_step_cl_placed_of_env htag hinner hstep

/-- Lift an `Entails`-based `StatesFromPbVariantBodyClPlacedOfEnv` at `+off` to `subroutine_ok`
    for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)`. -/
theorem sfpProof_tagged_ok_of_body_cl_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hbody : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantBodyClPlacedOfEnv M A lim F ext inner off Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)) := by
  refine sfpProof_tagged_ok_of_step_cl_placed_of_env htag hinner fun hpts => ?_
  intro st s0 s1 out pbA R hcl1 hfits hsp0 hpc1 hrun1 hsp1 hx19 hx23 hx27 htr1
  exact sfpProof_sepWPp_of_states_body_placed_of_env st s0 s1 out pbA
    { innerState := some inner } Env _ R
    (hbody hpts st s0 s1 out pbA R hcl1 hfits hsp0 hpc1 hrun1 hsp1 hx19 hx23 hx27 htr1)

theorem sfpProof_tagged_ok_of_body_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hbody : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantBodyClPlaced M A lim F ext inner off) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some inner })) :=
  sfpProof_tagged_ok_of_body_cl_placed_of_env htag hinner hbody

/-- Lift an untagged `Ct1Sampled` (`+36 -> +1056`) `StatesFromPbVariantStepClPlacedOfEnv` to
    `subroutine_ok` for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv ...)`. -/
theorem sfpProof_ct1Sampled_ok_of_step_cl_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.Ct1Sampled} {Env : List AllocEvent → Prop}
    (hinner : ∀ pbA, ∃ (w0 : BitVec 64) (Tail : SepProp),
      (w0 = noneCap ∨ w0.toNat < 2 ^ 63) ∧
      (optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ⊢ (pbA ↦₆₄ w0) ∗ Tail) ∧
      ((pbA ↦₆₄ w0) ∗ Tail ⊢ optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s))))
    (hstep : v1StatePtsBound { innerState := some (.ct1Sampled s) } →
      StatesFromPbVariantStepClPlacedOfEnv M A lim F ext (.ct1Sampled s) 1056#64 Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  obtain ⟨w0, Tail, hw0, hopen, hclose⟩ := hinner pbA
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl_st hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1, _⟩
  have hP1' :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
       statesFromPbJumpTablePlacedAt) ⊢
      (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail) ∗
      A.pool lim st s1 := by
    refine Entails.trans (Entails.of_eq (show _ =
      optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
      (statesFromPbJumpTablePlacedAt ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       A.pool lim st s1) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hopen) (Entails.of_eq (by sep_ac_rfl))
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_ct1Sampled_placed_budget A lim st (ext := ext)
    s0 s1 out pbA w0
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail)
    hw0 hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_seq_clean_lscl_st hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join :
      (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail) ∗
      A.pool lim st s2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (((pbA ↦₆₄ w0) ∗ Tail) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2)) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono h2304 (sepConj_mono_left hclose))
      (Entails.of_eq (by sep_ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (hstep hpts st s0 s2 out pbA R hcl2 hfits hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2)

/-- Lift an untagged `Ct1Sampled` (`+36 -> +1056`) `StatesFromPbVariantBodyClPlacedOfEnv` to
    `subroutine_ok` for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv ...)`. -/
theorem sfpProof_ct1Sampled_ok_of_body_cl_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.Ct1Sampled} {Env : List AllocEvent → Prop}
    (hinner : ∀ pbA, ∃ (w0 : BitVec 64) (Tail : SepProp),
      (w0 = noneCap ∨ w0.toNat < 2 ^ 63) ∧
      (optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s)) ⊢ (pbA ↦₆₄ w0) ∗ Tail) ∧
      ((pbA ↦₆₄ w0) ∗ Tail ⊢ optProtoInnerStateAt A.repAlloc pbA (some (.ct1Sampled s))))
    (hbody : v1StatePtsBound { innerState := some (.ct1Sampled s) } →
      StatesFromPbVariantBodyClPlacedOfEnv M A lim F ext (.ct1Sampled s) 1056#64 Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.ct1Sampled s) } Env)) := by
  refine sfpProof_ct1Sampled_ok_of_step_cl_placed_of_env hinner fun hpts => ?_
  intro st s0 s1 out pbA R hcl1 hfits hsp0 hpc1 hrun1 hsp1 hx19 hx23 hx27 htr1
  exact sfpProof_sepWPp_of_states_body_placed_of_env st s0 s1 out pbA
    { innerState := some (.ct1Sampled s) } Env _ R
    (hbody hpts st s0 s1 out pbA R hcl1 hfits hsp0 hpc1 hrun1 hsp1 hx19 hx23 hx27 htr1)

/-! ## 3. Variant 0 (`KeysUnsampled`, `+156`) Complete Subroutine Theorems -/

alias states_from_pb_keysUnsampled_placed_ok_of_env :=
  Variant1bPlacedBudget.states_from_pb_keysUnsampled_placed_ok_of_env
alias states_from_pb_keysUnsampled_placed_ok_tight :=
  Variant1bPlacedBudget.states_from_pb_keysUnsampled_placed_ok_tight
alias states_from_pb_keysUnsampled_placed_ok_raw :=
  Variant1bPlacedBudget.states_from_pb_keysUnsampled_placed_ok_raw
alias states_from_pb_keysUnsampled_ok_ext_placed :=
  Variant1bPlacedBudget.states_from_pb_keysUnsampled_ok_ext_placed

/-! ## 4. Top-Level `<States>::from_pb` Composition, Stack-Frame, & `RoLoaded` Bridges -/

/-- Envelope-parametric reduction of `withLsCodeLoaded lsmpl (statesFromPbPlacedSpecOfEnv ...)` to
    per-`pb` `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv ... pb (Env pb))`. -/
theorem states_from_pb_placed_ok_of_forall_pb_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : V1State → List AllocEvent → Prop}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb (Env pb)))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (⟨out, pbA, pb⟩, st) R s0 hpc hrun hpre hal => ?_
  exact (hpb pb).mono_outcome ((out, pbA), st) R s0 hpc hrun hpre hal (fun _ hout => hout)

/-- Reduce `DefsBudget.StatesFromPbPlacedOk M A lim F ext` to
    `withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb)` for each
    `pb : V1State`. -/
theorem states_from_pb_placed_ok_of_forall_pb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb))) :
    DefsBudget.StatesFromPbPlacedOk M A lim F ext :=
  states_from_pb_placed_ok_of_forall_pb_of_env hpb

/-- Envelope-parametric stack-frame lift from `statesFromPbPlacedSpecOfEnv` (`statesFromPbStack`)
    to `statesFromPbPlacedSpecXOfEnv` (`statesFromPbStackX`) under `withLsCodeLoaded lsmpl`. -/
theorem states_from_pb_placed_ok_ext_of_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : V1State → List AllocEvent → Prop}
    (hok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecOfEnv M A lim F Env))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
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
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecOfEnv M A lim F Env)).pre (x, st) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    dsimp only [statesFromPbPlacedSpecXOfEnv, statesFromPbPlacedSpecOfEnv, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre0
  refine hok.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, statesFromPbPlacedSpecXOfEnv, statesFromPbPlacedSpecOfEnv, R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Lift `DefsBudget.StatesFromPbPlacedOk M A lim F ext` (`statesFromPbStack = 7552`B) to
    `DefsBudget.StatesFromPbPlacedOkExt M A lim F ext` (`statesFromPbStackX` on `lsProg_333`). -/
theorem states_from_pb_placed_ok_ext_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : DefsBudget.StatesFromPbPlacedOk M A lim F ext) :
    DefsBudget.StatesFromPbPlacedOkExt M A lim F ext :=
  states_from_pb_placed_ok_ext_of_ok_of_env hok

/-- Envelope-parametric reduction of `statesFromPbPlacedSpecXOfEnv` directly to per-`pb`
    `statesFromPbVariantPlacedSpecOfEnv`. -/
theorem states_from_pb_ok_of_forall_pb_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : V1State → List AllocEvent → Prop}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb (Env pb)))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env)) :=
  states_from_pb_placed_ok_ext_of_ok_of_env (states_from_pb_placed_ok_of_forall_pb_of_env hpb)

/-- Reduce `DefsBudget.StatesFromPbPlacedOkExt M A lim F ext` directly to
    `DefsBudget.statesFromPbVariantPlacedSpec` for each `pb : V1State`. -/
theorem states_from_pb_ok_of_forall_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hpb : ∀ pb : V1State,
      subroutine_ok (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333)
        (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpec M A lim F pb))) :
    DefsBudget.StatesFromPbPlacedOkExt M A lim F ext :=
  states_from_pb_placed_ok_ext_of_ok (states_from_pb_placed_ok_of_forall_pb hpb)

/-- Envelope-parametric lift from `lsProg_333` (`withLsCodeLoaded`) to
    `libsignalSessionLib.blockProgram lsmpl 333` (`withLsCodeRoLoaded`). -/
theorem states_from_pb_okX_of_ok_ext_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : V1State → List AllocEvent → Prop}
    (hok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env)) := by
  rw [← IsLsBlockProg.eq_blockProgram (prog := lsProg_333 (Rust.withPanics ext))
    (i := 333) (H := Rust.withPanics ext)]
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hok

/-- Lift `DefsBudget.StatesFromPbPlacedOkExt M A lim F ext` (`lsProg_333`, `withLsCodeLoaded`) to
    `DefsBudget.StatesFromPbPlacedOkX M A lim F ext` (`libsignalSessionLib.blockProgram lsmpl 333`,
    `withLsCodeRoLoaded`). -/
theorem states_from_pb_okX_of_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : DefsBudget.StatesFromPbPlacedOkExt M A lim F ext) :
    DefsBudget.StatesFromPbPlacedOkX M A lim F ext :=
  states_from_pb_okX_of_ok_ext_placed_of_env hok

/-- Lift `DefsBudget.StatesFromPbPlacedOk M A lim F ext` (`statesFromPbStack = 7552`B,
    `withLsCodeLoaded`) directly to `DefsBudget.StatesFromPbPlacedOkX M A lim F ext`
    (`statesFromPbStackX`, `withLsCodeRoLoaded`). -/
theorem states_from_pb_okX_of_ok_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : DefsBudget.StatesFromPbPlacedOk M A lim F ext) :
    DefsBudget.StatesFromPbPlacedOkX M A lim F ext :=
  states_from_pb_okX_of_ok_ext_placed (states_from_pb_placed_ok_ext_of_ok hok)

/-- Discharge `statesFromPbJumpTablePlacedAt` via `LibsignalRoLoaded` to obtain the `.rodata`-free
    extended-stack contract `statesFromPbPlacedRoFreeSpecXOfEnv`. -/
theorem states_from_pb_roFree_okX_of_okX_placed_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : V1State → List AllocEvent → Prop}
    (hok : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedRoFreeSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  obtain ⟨hfr, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre_jt := rodata_statesFromPbJumpTablePlacedAt hfr.2 hpre0
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    dsimp only [statesFromPbPlacedRoFreeSpecXOfEnv, statesFromPbPlacedSpecXOfEnv] at hpre_jt ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre_jt
  refine hok.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, statesFromPbPlacedRoFreeSpecXOfEnv, statesFromPbPlacedSpecXOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    have hpost' : sf.mem ⊨ statesFromPbJumpTablePlacedAt ∗
        ((⌜sf.trace = s0.trace ∧ Env x.pb evs⌝ ∗
          resultChunkedStatesAt A.repAlloc (F := F) x.out
            (States.from_pb spqrPolyApi (spqrAuthApi F) x.pb) ∗
          memRegion x.pbA optProtoInnerStateSize ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact Satisfies.of_sep_right hpost'
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem states_from_pb_roFree_okX_of_okX_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hok : DefsBudget.StatesFromPbPlacedOkX M A lim F ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedRoFreeSpecX M A lim F)) :=
  states_from_pb_roFree_okX_of_okX_placed_of_env hok

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
