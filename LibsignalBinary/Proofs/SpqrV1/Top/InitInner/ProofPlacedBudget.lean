/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `spqr::init_inner` (`Block 324`): Relocatable `[LibsignalPlacement]` Budget Verification

Wires unconditional well-sizedness of `initV1State` (`States.IntoPb` on `Block 334`),
`<Authenticator>::new` envelope monotonicity (`Block 340`), and `.rodata` jump-table discharge
to prove `init_inner_placed_ok_unconditional` and `init_inner_placed_ok_x_unconditional`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_340 blkPl_340 libsignalMutatedBlocks
   libsignalSessionLib ls_externAt?_blockProgram_eq_of_externs_eq ls_subroutine_ok_cl_of_block
   lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Bytes Direction)
open CryptoVerification.SpqrV1.Auth (AuthNewGhost)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (LsCallInv withLsCallInv)
open CryptoVerification.SpqrV1.States.IntoPb
  (lsro_statesIntoPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initHdrDecoder initInnerResultAt initInnerStackX initV1State)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_324 blkPl_324)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux
  (AuthNewEnv AuthNewPlacedOk authNewSpec authNewSpecAt spqrBoundedEvs_of_authNewEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (StatesIntoPbAllocPlacedBudget StatesIntoPbPlacedOkExt StatesIntoPbPlacedOkX
   statesIntoPbPlacedOkX_of_statesIntoPbPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget
  (StatesIntoPbBounded StatesIntoPbExactPlacedOkX StatesIntoPbWellSized
   states_into_pb_placed_env_of_alloc_ok_x_blockProgram
   states_into_pb_placed_env_ok_x_blockProgram
   states_into_pb_variant_of_bounds_cl_placed
   states_into_pb_variant_of_bounds_of_alloc_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerPlacedOkX SpqrBoundedEvs initInnerPlacedRoSpecX initInnerPlacedRoSpecXOfEnv
   initInnerPlacedSpecX initInnerPlacedSpecXOfEnv statesIntoPbPlacedSpec
   statesIntoPbVariantPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
  (AuthNewBudgetEnv authNewBudgetSpec authNewBudgetSpecOfEnv
   init_inner_placed_ok_ext_of_arms init_inner_placed_ok_ext_of_intoPb
   init_inner_placed_ok_x_of_arms init_inner_placed_ok_x_of_intoPb
   le_two_pow_48_of_fitsEnv_spqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

/-! ## 1. Unconditional `StatesIntoPbWellSized` for `initV1State` -/

/-- Both initial `.v1` states (`States.init_a` / `.keysUnsampled` and `States.init_b` /
    `.noHeaderReceived` with 16 empty buckets) satisfy `StatesIntoPbWellSized` unconditionally. -/
theorem statesIntoPbWellSized_initV1State (F : ShaCompress) (d : Direction) (authKey : Bytes) :
    StatesIntoPbWellSized (initV1State F d authKey) := by
  cases d
  · trivial
  · dsimp only [StatesIntoPbWellSized, StatesIntoPbBounded, initV1State, initHdrDecoder]
    refine ⟨by simp only [List.length_replicate]; decide, by omega, ?_⟩
    intro sl hsl
    rw [List.eq_of_mem_replicate hsl]
    exact ⟨by decide, Nat.le_trans (by decide : _ ≤ 0) (Nat.zero_le _)⟩

/-! ## 2. `<Authenticator>::new` Envelope Monotonicity & Cross-Block (`340 → 324`) Lifts -/

/-- Any `FitsEnv` witness for `AuthNewBudgetEnv x` bounds `32 + x.rootKey.length ≤ MallocngMaxAllocSize`,
    so `AuthNewEnv x` refines `AuthNewBudgetEnv x` and inherits `FitsEnv`. -/
theorem authNewEnv_imp_authNewBudgetEnv_of_fitsEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {x : AuthNewGhost}
    (hfit : FitsEnv M lim st (AuthNewBudgetEnv x)) :
    (∀ evs, AuthNewEnv x evs → AuthNewBudgetEnv x evs) ∧ FitsEnv M lim st (AuthNewEnv x) := by
  have h48 : x.rootKey.length ≤ 2 ^ 48 :=
    le_two_pow_48_of_fitsEnv_spqrBoundedEvs (n := x.rootKey.length) (by decide) (by omega) hfit
  have hcap : (32 : Nat) + 2 ^ 48 ≤ MallocngMaxAllocSize := by decide
  have hmax : 32 + x.rootKey.length ≤ MallocngMaxAllocSize := by omega
  have himp : ∀ evs, AuthNewEnv x evs → AuthNewBudgetEnv x evs := fun evs hev =>
    SpqrBoundedEvs.mono (by decide) (by omega) (spqrBoundedEvs_of_authNewEnv hmax hev)
  exact ⟨himp, fun evs hev => hfit evs (himp evs hev)⟩

/-- Monotonicity from `Auth.NewBudgetAux.authNewSpec F M A lim` (`AuthNewEnv`) to
    `authNewBudgetSpec M A lim F` (`AuthNewBudgetEnv`). -/
theorem authNewBudgetSpec_of_authNewSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (authNewSpec F M A lim)) :
    subroutine_ok P addr (authNewBudgetSpec M A lim F) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  dsimp only [authNewBudgetSpec, authNewBudgetSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlt, hfit, hlr⟩, hm⟩
  have ⟨himp, hfit_new⟩ := authNewEnv_imp_authNewBudgetEnv_of_fitsEnv hfit
  have hpre' : s0.mem ⊨ (authNewSpec F M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [authNewSpec, authNewSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlt, hfit_new, hlr⟩, hm⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [authNewSpec, authNewSpecAt, authNewBudgetSpec, authNewBudgetSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, himp evs hpost.1.2⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- `withLsCallInv lsmpl`-wrapped monotonicity from `authNewSpec F M A lim` to
    `authNewBudgetSpec M A lim F`. -/
theorem withLsCallInv_authNewBudgetSpec_of_authNewSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCallInv lsmpl (authNewSpec F M A lim))) :
    subroutine_ok P addr (withLsCallInv lsmpl (authNewBudgetSpec M A lim F)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  dsimp only [withLsCallInv, authNewBudgetSpec, authNewBudgetSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlt, hfit, hlr⟩, hm⟩
  have ⟨himp, hfit_new⟩ := authNewEnv_imp_authNewBudgetEnv_of_fitsEnv hfit
  have hpre' : s0.mem ⊨ (withLsCallInv lsmpl (authNewSpec F M A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCallInv, authNewSpec, authNewSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlt, hfit_new, hlr⟩, hm⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, authNewSpec, authNewSpecAt,
      authNewBudgetSpec, authNewBudgetSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, himp evs hpost.1.2⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Cross-block `subroutine_ok` transport for `withLsCallInv lsmpl`-wrapped contracts between
    blocks sharing the same `LibsignalHooks`. -/
theorem ls_subroutine_ok_callInv_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCallInv lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCallInv lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hinv0 : LsCallInv lsmpl s0.mem := by
    dsimp only [withLsCallInv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hinv0.2 j (by omega) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Lift `AuthNewPlacedOk F M A lim (Rust.withPanics ext)` (`Block 340`) onto `Block 324`. -/
theorem authNew_324_of_placedOk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hAuth : AuthNewPlacedOk F M A lim (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec F M A lim)) :=
  ls_subroutine_ok_callInv_of_block
    (callerProg := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
    (calleeProg := (blkPC_340).rebase (blkPl_340).base (Rust.withPanics ext))
    hAuth

/-! ## 3. Cross-Block (`334 → 324`) `<States>::into_pb` Lifts & `.rodata` Discharge -/

/-- Project `withLsCl lsmpl spec` back to `withLsCodeLoaded lsmpl spec`. -/
theorem subroutine_ok_withLsCodeLoaded_of_withLsCl [LibsignalPlacement] {α : Type}
    {P : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P addr (withLsCl lsmpl spec)) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hpost => by
    dsimp only [withLsCl, withLsCodeLoaded] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2)

/-- Lift per-arm `<States>::into_pb` on `initV1State F d authKey` from `Block 334` onto `Block 324`. -/
theorem statesIntoPb_initV1State_324_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_into : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (d : Direction) (authKey : Bytes) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F d authKey))) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block
      (callerProg := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (states_into_pb_variant_of_bounds_cl_placed hA_into henc_raw hdec_raw hmemcpy_into
        (initV1State F d authKey) (statesIntoPbWellSized_initV1State F d authKey)))

/-- `statesIntoPb_initV1State_324_cl` deriving `hmemcpy_into` from `hA_into`. -/
theorem statesIntoPb_initV1State_324_of_alloc_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (d : Direction) (authKey : Bytes) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F d authKey))) :=
  subroutine_ok_withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block
      (callerProg := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (states_into_pb_variant_of_bounds_of_alloc_cl_placed hA_into henc_raw hdec_raw
        (initV1State F d authKey) (statesIntoPbWellSized_initV1State F d authKey)))

/-- Discharge `statesIntoPbJumpTablePlacedAt` from `LibsignalRoLoaded lsmpl s0.mem` on
    `initInnerPlacedSpecXOfEnv`. -/
theorem initInnerPlacedRoSpecXOfEnv_of_placedSpecXOfEnv [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {Env : InitInnerGhost → List AllocEvent → Prop}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpecXOfEnv M A lim F Env))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (initInnerPlacedRoSpecXOfEnv M A lim F Env)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl, hro⟩, hpre0⟩ := hpre
  have hjt : s0.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
      ((initInnerPlacedRoSpecXOfEnv M A lim F Env).pre (x, st) s0 ∗ R) :=
    lsro_statesIntoPbJumpTablePlacedAt (s := s0) hro hpre0
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (initInnerPlacedSpecXOfEnv M A lim F Env)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [initInnerPlacedSpecXOfEnv, initInnerPlacedRoSpecXOfEnv] at hjt ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hjt
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withLsCodeLoaded,
      initInnerPlacedRoSpecXOfEnv, initInnerPlacedSpecXOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    have hpost_reord : sf.mem ⊨ statesIntoPbJumpTablePlacedAt ∗
        ((⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
          initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
          (x.akPtr ↦ₛ x.authKey) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp initInnerStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact Satisfies.of_sep_right hpost_reord
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Specialize `initInnerPlacedRoSpecXOfEnv_of_placedSpecXOfEnv` to `InitInnerEnv F`. -/
theorem initInnerPlacedRoSpecX_of_placedSpecX [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F))) :
    subroutine_ok P addr (withLsCodeRoLoaded lsmpl (initInnerPlacedRoSpecX M A lim F)) :=
  initInnerPlacedRoSpecXOfEnv_of_placedSpecXOfEnv h

/-! ## 4. Top-Level Relocatable `[LibsignalPlacement]` Verification Theorems -/

/-- Top-level verification of `spqr::init_inner` on
    `(blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)` against
    `withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)`. -/
theorem init_inner_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)) :=
  init_inner_placed_ok_ext_of_intoPb hshim halloc hmemcpy
    (authNewBudgetSpec_of_authNewSpec hauth) hinto

/-- Top-level verification of `spqr::init_inner` on
    `(blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)` against
    `withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)`. -/
theorem init_inner_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec F M A lim)))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) :=
  init_inner_placed_ok_x_of_intoPb hshim halloc hmemcpy
    (withLsCallInv_authNewBudgetSpec_of_authNewSpec hauth) hinto

/-- `.rodata`-free top-level verification of `spqr::init_inner` (`Block 324`) against
    `withLsCodeRoLoaded lsmpl (initInnerPlacedRoSpecX M A lim F)`. -/
theorem init_inner_placed_ro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeRoLoaded lsmpl (initInnerPlacedRoSpecX M A lim F)) :=
  initInnerPlacedRoSpecX_of_placedSpecX
    (init_inner_placed_ok_ext hshim halloc hmemcpy hauth hinto)

/-- Top-level verification of `spqr::init_inner` (`Block 324`) on
    `libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext)` at `lsmpl.base 324`
    (`InitInnerPlacedOkX M A lim F ext`), parameterized by `hIntoPb : StatesIntoPbPlacedOkExt M A lim F ext`. -/
theorem init_inner_placed_ok_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hIntoPb : StatesIntoPbPlacedOkExt M A lim F ext) :
    InitInnerPlacedOkX M A lim F ext := by
  have hinto_324 :
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F)) :=
    subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_block
        (callerProg := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        hIntoPb)
  have hok := init_inner_placed_ok_ext hshim halloc hmemcpy hauth hinto_324
  dsimp only [InitInnerPlacedOkX]
  have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      324 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
  rwa [hprog, hbase] at hok

/-- Wiring of `StatesIntoPbPlacedOkX M A lim F ext` on `libsignalSessionLib.blockProgram lsmpl 334`
    from `StatesIntoPbPlacedOkExt M A lim F ext`. -/
theorem states_into_pb_placed_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hIntoPb : StatesIntoPbPlacedOkExt M A lim F ext) :
    StatesIntoPbPlacedOkX M A lim F ext :=
  statesIntoPbPlacedOkX_of_statesIntoPbPlacedOkExt hIntoPb

/-- Unconditional exact-envelope `<States>::into_pb` verification on
    `libsignalSessionLib.blockProgram lsmpl 334` (`StatesIntoPbExactPlacedOkX M A lim F ext`). -/
theorem states_into_pb_exact_placed_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    StatesIntoPbExactPlacedOkX M A lim F ext :=
  states_into_pb_placed_env_ok_x_blockProgram hA henc_raw hdec_raw hmemcpy_raw

/-- `states_into_pb_exact_placed_ok_x_blockProgram` deriving `hmemcpy_raw` from `hA`. -/
theorem states_into_pb_exact_placed_of_alloc_ok_x_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    StatesIntoPbExactPlacedOkX M A lim F ext :=
  states_into_pb_placed_env_of_alloc_ok_x_blockProgram hA henc_raw hdec_raw

/-- Unconditional top-level verification of `spqr::init_inner` (`Block 324`) on
    `libsignalSessionLib.blockProgram lsmpl 324` (`InitInnerPlacedOkX M A lim F ext`), wired
    directly through `States.IntoPb.TopPlacedBudget` using `statesIntoPbWellSized_initV1State`. -/
theorem init_inner_placed_ok_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_into : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    InitInnerPlacedOkX M A lim F ext := by
  have hok := init_inner_placed_ok_ext_of_arms hshim halloc hmemcpy
    (authNewBudgetSpec_of_authNewSpec hauth)
    (statesIntoPb_initV1State_324_cl hA_into henc_raw hdec_raw hmemcpy_into .a2b)
    (statesIntoPb_initV1State_324_cl hA_into henc_raw hdec_raw hmemcpy_into .b2a)
  dsimp only [InitInnerPlacedOkX]
  have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      324 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
  rwa [hprog, hbase] at hok

/-- `init_inner_placed_ok_unconditional` deriving `hmemcpy_into` from `hA_into`. -/
theorem init_inner_placed_ok_unconditional_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    InitInnerPlacedOkX M A lim F ext := by
  have hok := init_inner_placed_ok_ext_of_arms hshim halloc hmemcpy
    (authNewBudgetSpec_of_authNewSpec hauth)
    (statesIntoPb_initV1State_324_of_alloc_cl hA_into henc_raw hdec_raw .a2b)
    (statesIntoPb_initV1State_324_of_alloc_cl hA_into henc_raw hdec_raw .b2a)
  dsimp only [InitInnerPlacedOkX]
  have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      324 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
  rwa [hprog, hbase] at hok

/-- Unconditional `withLsCallInv lsmpl` verification of `spqr::init_inner` (`Block 324`) on
    `libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext)` at `lsmpl.base 324`,
    wired directly from `AuthNewPlacedOk F M A lim (Rust.withPanics ext)` (`Block 340`) and
    `States.IntoPb.TopPlacedBudget` (`Block 334`). -/
theorem init_inner_placed_ok_x_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hAuth : AuthNewPlacedOk F M A lim (Rust.withPanics ext))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_into : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
      (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) := by
  have hok := init_inner_placed_ok_x_of_arms hshim halloc hmemcpy
    (withLsCallInv_authNewBudgetSpec_of_authNewSpec (authNew_324_of_placedOk hAuth))
    (statesIntoPb_initV1State_324_cl hA_into henc_raw hdec_raw hmemcpy_into .a2b)
    (statesIntoPb_initV1State_324_cl hA_into henc_raw hdec_raw hmemcpy_into .b2a)
  have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      324 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
  rwa [hprog, hbase] at hok

/-- `init_inner_placed_ok_x_unconditional` deriving `hmemcpy_into` from `hA_into`. -/
theorem init_inner_placed_ok_x_unconditional_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hAuth : AuthNewPlacedOk F M A lim (Rust.withPanics ext))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
      (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) := by
  have hok := init_inner_placed_ok_x_of_arms hshim halloc hmemcpy
    (withLsCallInv_authNewBudgetSpec_of_authNewSpec (authNew_324_of_placedOk hAuth))
    (statesIntoPb_initV1State_324_of_alloc_cl hA_into henc_raw hdec_raw .a2b)
    (statesIntoPb_initV1State_324_of_alloc_cl hA_into henc_raw hdec_raw .b2a)
  have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      324 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
  rwa [hprog, hbase] at hok

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget
