/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 0 (`KeysUnsampled`) Envelopes and Dispatch Combiner

Allocator event envelopes for `InnerState.keysUnsampled`, `StatesFromPbEnv` subsumption,
and the generic tagged-variant dispatch combiner in Block `333`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap
open CryptoVerification (LibsignalPlacement lsProg_333 lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator V1State)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v1StatePtsBound)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawChKeysUnsampled
   rawInnerState rawUcKeysUnsampled rawUcKeysUnsampled_le_encodeRaw)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved
   fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents fitsEvents_of_fitsEnv_authFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv sepWPp_of_states_exit_placed
   spqrRustDeallocSym statesFromPbVariantPlacedSpec statesFromPbVariantPlacedSpecOfEnv
   states_from_pb_prologue_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget states_from_pb_epilogue_8176_keysUnsampled_placed
   states_from_pb_keysUnsampled_auth_none_placed
   states_from_pb_keysUnsampled_step0_156_200_placed_budget
   states_from_pb_keysUnsampled_uc_none_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Allocation Envelopes & `StatesFromPbEnv` Subsumption for Variant 0 (`KeysUnsampled`) -/

/-- Allocation-only event envelope for Variant 0 (`KeysUnsampled`) of `<States>::from_pb`:
    `[]` on the `uc = none` and `auth = none` error paths, and `AuthFromPbEnv auth` on
    `uc = some { auth := some auth, .. }`. -/
def KeysUnsampledFromPbAllocEnv (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some uc =>
    match uc.auth with
    | none => evs = []
    | some auth => AuthFromPbEnv auth evs

/-- Complete allocator event envelope for Variant 0 (`KeysUnsampled`) of `<States>::from_pb`,
    including trailing `FreeOnlyEvs` drops of the input `ProtoAuthenticator` buffers. -/
def KeysUnsampledFromPbEnv (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some uc =>
    match uc.auth with
    | none => evs = []
    | some auth =>
      ∃ evs_free, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents auth ++ evs_free

theorem fitsEnv_auth_of_keysUnsampled {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {auth : ProtoAuthenticator}
    (h : FitsEnv M lim st
      (KeysUnsampledFromPbAllocEnv { uc := some { epoch := ep, auth := some auth } })) :
    FitsEnv M lim st (AuthFromPbEnv auth) :=
  h

theorem fitsEnv_alloc_of_keysUnsampledEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled}
    (h : FitsEnv M lim st (KeysUnsampledFromPbEnv s)) :
    FitsEnv M lim st (KeysUnsampledFromPbAllocEnv s) := by
  intro evs hevs
  cases s with | mk uc =>
  cases uc with
  | none => exact h evs hevs
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none => exact h evs hevs
    | some auth =>
      apply h evs
      refine ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, ?_⟩
      simpa [KeysUnsampledFromPbAllocEnv, AuthFromPbEnv] using hevs

theorem rawAuth_le_keysUnsampled_encodeRaw (ep : BitVec 64) (auth : ProtoAuthenticator) :
    auth.rootKey.length + auth.macKey.length ≤
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
        { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }).length := by
  have h0 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw 1#32
    { uc := some { auth := some auth, epoch := ep } }
  have h1 := length_le_encodeOptMessage _ rawUcKeysUnsampled rawUcKeysUnsampled_le_encodeRaw 1#32
    (some ({ auth := some auth, epoch := ep } : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.KeysUnsampled))
  dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
    CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled.encodeRaw, rawUcKeysUnsampled, optRaw, rawAuth] at h0 h1 ⊢
  omega

theorem spqrBoundedEvs_authKeyCloneEvents {bs : List (BitVec 8)}
    (hmax : bs.length ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 bs.length (authKeyCloneEvents bs) := by
  unfold authKeyCloneEvents
  split
  · exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 1 bs.length
  · rename_i hne
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => simp at hne
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hre : rustAllocEvents bs.length 1 = [.alloc bs.length] := by
      simp [rustAllocEvents, hpos]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem keysUnsampledFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.keysUnsampled s) }))
    {evs : List AllocEvent} (hevs : KeysUnsampledFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.keysUnsampled s) } evs := by
  let pb : V1State := { innerState := some (.keysUnsampled s) }
  change SpqrBoundedEvs 128 (4 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length + 4096) evs
  cases s with | mk uc =>
  cases uc with
  | none =>
    subst hevs; exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      subst hevs; exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil _ _
    | some auth =>
      rcases hevs with ⟨evs_free, hfree, rfl⟩
      have hlen_pb : auth.rootKey.length + auth.macKey.length ≤ (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length :=
        rawAuth_le_keysUnsampled_encodeRaw ep auth
      let m := min (auth.rootKey.length + auth.macKey.length) MallocngMaxAllocSize
      have hm_env : StatesFromPbEnv pb [.alloc m] := by
        refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
        simp only [List.mem_singleton] at hev
        subst hev
        exact ⟨Nat.min_le_right _ _,
          Nat.le_trans (Nat.min_le_left _ _) (by omega),
          (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
      rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
      have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
      have hm_max : auth.rootKey.length + auth.macKey.length ≤ MallocngMaxAllocSize := by
        dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
        omega
      have hb_r : SpqrBoundedEvs 1 auth.rootKey.length (authKeyCloneEvents auth.rootKey) :=
        spqrBoundedEvs_authKeyCloneEvents (by omega)
      have hb_m : SpqrBoundedEvs 1 auth.macKey.length (authKeyCloneEvents auth.macKey) :=
        spqrBoundedEvs_authKeyCloneEvents (by omega)
      have hb_auth : SpqrBoundedEvs 2 (max auth.rootKey.length auth.macKey.length)
          (authFromPbEvents auth) :=
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_r hb_m
      have hb_all : SpqrBoundedEvs 2 (max (max auth.rootKey.length auth.macKey.length) 0)
          (authFromPbEvents auth ++ evs_free) :=
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_auth (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree)
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by omega) hb_all

theorem fitsEnv_alloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysUnsampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.keysUnsampled s) })) :
    FitsEnv M lim st (KeysUnsampledFromPbAllocEnv s) := by
  refine fitsEnv_alloc_of_keysUnsampledEnv fun evs hevs => ?_
  exact hfits evs (keysUnsampledFromPbEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## Local Deallocation & Sequencing Helpers -/

def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

theorem seq_clean_st {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

/-! ## Tagged-Variant Dispatch Combiner (`+0 -> +36 -> +off`) -/

/-- Canonical budget-threaded post-dispatch `SepWPp` obligation at offset `off` in Block `333`
    for a `V1State.InnerState` variant `inner` under envelope `Env`. -/
def StatesFromPbVariantStepPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (inner : CryptoVerification.LibsignalSpqrV1.V1State.InnerState) (off : BitVec 64)
    (Env : List AllocEvent → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp),
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
            (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env).post
              ((out, pbA), st) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env).onPanic
            ((out, pbA), st) s0 sf ∗ R))

/-- Lift a tagged-variant `StatesFromPbVariantStepPlaced` at `+off` to `subroutine_ok` for
    `statesFromPbVariantPlacedSpecOfEnv`. -/
theorem sfpProof_tagged_ok_of_step_placed_raw [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : CryptoVerification.LibsignalSpqrV1.V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantStepPlaced M A lim F ext inner off Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre
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
  refine SepWPp.of_sepWP (SepWP.mono hpro fun s1 P1 hpc1 hrun1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩ => ?_)
  have hP1' : P1 ⊢
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail pbA) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
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
  refine SepWPp.of_sepWP (SepWP.mono hdisp fun s2 P2 hpc2 hrun2
    ⟨hP2, hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩ => ?_)
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
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
    (hstep hpts st s0 s2 out pbA R hfits hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2)

/-- Lift `sfpProof_tagged_ok_of_step_placed_raw` to `withLsCodeLoaded`. -/
theorem sfpProof_tagged_ok_of_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : CryptoVerification.LibsignalSpqrV1.V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : v1StatePtsBound { innerState := some inner } →
      StatesFromPbVariantStepPlaced M A lim F ext inner off Env) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (sfpProof_tagged_ok_of_step_placed_raw htag hinner hstep)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
