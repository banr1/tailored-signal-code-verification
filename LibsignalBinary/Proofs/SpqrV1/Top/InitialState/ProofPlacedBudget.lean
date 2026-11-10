/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2Budget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs

/-!
# Budget-Threaded Relocatable Verification of `spqr::initial_state`

Proves the deterministic allocation-budget contracts `InitialStatePlacedOkX` and
`InitialStatePlacedOkBlockProgram` for `spqr::initial_state` (Block `327`) under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_270 blkPl_270 libsignalSessionCode libsignalSessionLib
   lsLogFilterAddr lsMemcpySym lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Version)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (LsCallInv)
open CryptoVerification.SpqrV1.Drop
  (optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb
  (lsro_statesIntoPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.Top.InitialState
  (InitialStateGhost initialStatePB initialStatePB_encodeRaw_length_lt initialStatePlacedEntry
   initialStatePlacedProg initialStateResultAt initialStateStack initialStateValue
   initialState_pbAt_of_cells paramsAt)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_324 blkPl_324)
open CryptoVerification.SpqrV1.Top.Recv
  (lsro_optProtoInnerStateJumpTablePlacedAt protoPqRatchetStateAt_eq_pqRatchetStatePBAt)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
   rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux (authNewSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2Budget (drop_proto_pq_ratchet_state_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlacedBudget
  (pqRatchetStateEncodeToVec_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget (StatesIntoPbAllocPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerPlacedOkX initInnerPlacedSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget
  (init_inner_placed_ok_unconditional init_inner_placed_ok_unconditional_of_alloc)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
  (InitialStateEnv InitialStatePlacedOkBlockProgram InitialStatePlacedOkX initialStatePlacedSpec
   initialStatePlacedSpecOfEnv initialStatePlacedSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget
  (initialState_v0_step_placed initial_state_v1_body_placed sepWPp_of_initialState_v1_placed_wpp)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 1. Relocatable Budget Callee Contract Bundle (`InitialStateContractsPlaced`) -/

/-- Relocatable budget callee contracts of `spqr::initial_state` (`Block 327`). -/
structure InitialStateContractsPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  panic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
    noAllocShimBudgetSpec
  alloc_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
    (rustCliAllocBudgetSpec M A lim false)
  memcpy_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
    framelessMemcpyBudgetSpec
  initInner_ok : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
    (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F))
  encodeToVec_ok : PqRatchetStateEncodeToVecPlacedOkExt A lim ext
  dropPqRatchetState_ok : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
    (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))

/-! ## 2. Dispatch on `params.version` -/

/-- `initialStatePlacedSpecX` restricted to `p.version = v`. -/
def initialStateVPlacedSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (v : Version) :
    Spec (InitialStateGhost × M.σ) :=
  { initialStatePlacedSpecX M A lim F with
    pre := fun (x, st) s => ⌜x.p.version = v⌝ ∗ (initialStatePlacedSpecX M A lim F).pre (x, st) s }

/-- `InitialStatePlacedOkX` from its two version cases (`.v0` and `.v1`). -/
theorem initialState_placed_ok_of_versions [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h0 : subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX M A lim F .v0))
    (h1 : subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX M A lim F .v1)) :
    InitialStatePlacedOkX M A lim F ext := by
  dsimp only [InitialStatePlacedOkX]
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp => ?_
  have key : ∀ v, x.p.version = v →
      s0.mem ⊨ (initialStateVPlacedSpecX M A lim F v).pre (x, st) s0 ∗ R := by
    intro v hv
    dsimp only [initialStateVPlacedSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hv, hpre⟩
  cases hv : x.p.version with
  | v0 => exact h0.mono_outcome (x, st) R s0 hpc hrun (key .v0 hv) hsp fun _ hout => hout
  | v1 => exact h1.mono_outcome (x, st) R s0 hpc hrun (key .v1 hv) hsp fun _ hout => hout

/-! ## 3. V0 Path on `Block 327` (`initialState_v0_placed_ok`) -/

/-- `version = .v0` returns `Ok(vec![])` without calls (`evs = []`). -/
theorem initialState_v0_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX M A lim F .v0) := by
  refine subroutine_ok_of_sepWP fun (x, st0) R s0 hpc hrun hpre hsp0_align => ?_
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    withLsCodeRoLoaded, initialStatePlacedSpec, initialStatePlacedSpecOfEnv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hcrl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, _hak_ne, _hlen, _hfit⟩, hm⟩
  have hpre_eq :
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗ ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s0)) ∗ R := by
    sep_ac_rfl
  rw [hpre_eq] at hm
  refine ⟨_, R, hm, SepWP.mono (initialState_v0_step_placed (A := A.repAlloc) (F := F) s0 x
    ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s0) hsp0_align hpc hrun hx0 hx8 hv) ?_⟩
  rintro sf P_f _ _ ⟨hent, hvm, hspf, hcsf, htrf⟩
  refine ⟨fun hmf => ?_, hspf, hcsf⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨[], ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have henv0 : InitialStateEnv F x [] := by simp only [InitialStateEnv, hv]
  refine ⟨⟨htrf, henv0⟩, ?_⟩
  have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
  have hpool_eq : A.pool lim (M.stepEvents [] st0) sf = A.pool lim st0 s0 := by
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, ← A.pool_of_vmPreserved hvm]
  rw [hpool_eq]
  have hpost_eq :
      (paramsAt x.pA x.akPtr x.p ∗ initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp initialStateStack ∗
       ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s0)) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack) ∗ R := by
    sep_ac_rfl
  rwa [hpost_eq] at hmf'

/-! ## 4. V1 Path on `Block 327` (`initialState_v1_placed_ok`) -/

/-- `version = .v1` executes `auth_key.to_vec()`, `spqr::init_inner`,
    `PqRatchetState::encode_to_vec`, and `drop_glue::<PqRatchetState>` without panic or OOM
    under `FitsEnv M lim st0 (InitialStateEnv F x)`. -/
theorem initialState_v1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsPlaced M A lim F ext) :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX M A lim F .v1) := by
  refine subroutine_ok_of_sepWPp fun (x, st0) R s0 hpc hrun hpre hsp => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    withLsCodeRoLoaded] at hpre ⊢
  dsimp only [initialStatePlacedSpec, initialStatePlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl0, hro0⟩, hpre⟩ := hpre
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨hro0, hcl0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen, hfit⟩, hmem⟩ := hpre
  have hmem1 := lsro_optProtoInnerStateJumpTablePlacedAt hro0 hmem
  have hmem2 := lsro_statesIntoPbJumpTablePlacedAt hro0 hmem1
  have hmem3 : s0.mem ⊨
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack) ∗ R :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_placed hC.shim_ok hC.alloc_ok hC.memcpy_ok
    hC.initInner_ok hC.encodeToVec_ok hC.dropPqRatchetState_ok
    s0 x st0 R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen hfit
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (protoPqRatchetStateAt_eq_pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A.repAlloc F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  exact ⟨_, R, hmem3, sepWPp_of_initialState_v1_placed_wpp s0 x st0 _ R hwpp⟩

/-! ## 5. Top-Level Relocatable `[LibsignalPlacement]` Budget Theorems -/

/-- Proves `InitialStatePlacedOkX` from `InitialStateContractsPlaced`. -/
theorem initialState_placed_ok_x_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsPlaced M A lim F ext) :
    InitialStatePlacedOkX M A lim F ext :=
  initialState_placed_ok_of_versions initialState_v0_placed_ok (initialState_v1_placed_ok hC)

/-- Assemble `InitialStateContractsPlaced M A lim F ext` from external hook contracts and placed
    callee contracts (`InitInnerPlacedOkX`, `PqRatchetStateEncodeToVecPlacedOkExt`, and
    `drop_glue::<PqRatchetState>` on `Block 270`). -/
theorem initialStateContractsPlaced_of_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hInitInner : InitInnerPlacedOkX M A lim F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    InitialStateContractsPlaced M A lim F ext where
  panic_ok := h_panic
  shim_ok := hshim
  alloc_ok := halloc
  memcpy_ok := hmemcpy
  initInner_ok := by
    dsimp only [InitInnerPlacedOkX] at hInitInner
    have hprog : (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext) =
        libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext) :=
      (inferInstance : IsLsBlockProg
        ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        324 (Rust.withPanics ext)).eq_blockProgram
    have hbase : (blkPl_324).base = lsmpl.base 324 := rfl
    rwa [hprog, hbase]
  encodeToVec_ok := hEncodeToVec
  dropPqRatchetState_ok := hdrop

/-- Top-level relocatable `spqr::initial_state` (`Block 327`) budget theorem
    (`InitialStatePlacedOkX M A lim F ext`). -/
theorem initial_state_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hInitInner : InitInnerPlacedOkX M A lim F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    InitialStatePlacedOkX M A lim F ext :=
  initialState_placed_ok_x_of_contracts
    (initialStateContractsPlaced_of_okX h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop)

/-- Top-level relocatable `spqr::initial_state` (`Block 327`) budget theorem on
    `libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext)` at `lsmpl.base 327`. -/
theorem initial_state_placed_ok_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hInitInner : InitInnerPlacedOkX M A lim F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    InitialStatePlacedOkBlockProgram M A lim F ext := by
  have hok := initial_state_placed_ok_x h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop
  dsimp only [InitialStatePlacedOkBlockProgram, InitialStatePlacedOkX] at hok ⊢
  have hprog : initialStatePlacedProg ext =
      libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg (initialStatePlacedProg ext)
      327 (Rust.withPanics ext)).eq_blockProgram
  have hbase : initialStatePlacedEntry = lsmpl.base 327 := rfl
  rwa [hprog, hbase] at hok

theorem withPanics_eq_of_isPanicSymbol {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked) :
    Rust.withPanics ext = ext := by
  funext sym
  unfold Rust.withPanics
  split
  · next h => exact (hp sym h).symm
  · rfl

theorem initial_state_placed_ok_blockProgram_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hInitInner : InitInnerPlacedOkX M A lim F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 327 ext) (lsmpl.base 327)
      (initialStatePlacedSpecX M A lim F) := by
  have hok := initial_state_placed_ok_blockProgram
    h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop
  dsimp only [InitialStatePlacedOkBlockProgram] at hok
  rwa [withPanics_eq_of_isPanicSymbol hp] at hok

/-- Unconditional budget wiring of `spqr::initial_state` (`Block 327`) with internal SPQR blocks
    `init_inner` (`Block 324`), `<States>::into_pb` (`Block 334`),
    `PqRatchetState::encode_to_vec` (`Block 426`), and `drop_glue::<PqRatchetState>` (`Block
    270`) discharged internally. -/
theorem initial_state_placed_ok_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hshim_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (hauth_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_334 : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_334 : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hmemcpy_334 : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hshim_hook : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_hook : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_hook : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hmc_hook : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hdealloc_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hslice_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 288) (dropProtoEpochSliceSpec M A lim))
    (hinner_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec M A lim)) :
    InitialStatePlacedOkBlockProgram M A lim F ext :=
  initial_state_placed_ok_blockProgram
    hA_into.panic_ok hshim_327 halloc_327 hmemcpy_327
    (init_inner_placed_ok_unconditional hshim_324 halloc_324 hmemcpy_324 hauth_324
      hA_into henc_334 hdec_334 hmemcpy_334)
    (pqRatchetStateEncodeToVec_placed_ok_ext hA_into.panic_ok hshim_hook halloc_hook
      hrealloc_hook hmc_hook)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_proto_pq_ratchet_state_placed_ok hdealloc_270 hslice_270 hinner_270))

/-- `initial_state_placed_ok_unconditional` deriving `hmemcpy_334` directly from `hA_into`. -/
theorem initial_state_placed_ok_unconditional_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hshim_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimBudgetSpec)
    (halloc_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (hauth_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F M A lim))
    (hA_into : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_334 : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (encoderIntoPbSpec M A lim))
    (hdec_334 : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (decoderIntoPbSpec M A lim))
    (hshim_hook : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_hook : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_hook : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hmc_hook : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hdealloc_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hslice_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 288) (dropProtoEpochSliceSpec M A lim))
    (hinner_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec M A lim)) :
    InitialStatePlacedOkBlockProgram M A lim F ext :=
  initial_state_placed_ok_blockProgram
    hA_into.panic_ok hshim_327 halloc_327 hmemcpy_327
    (init_inner_placed_ok_unconditional_of_alloc hshim_324 halloc_324 hmemcpy_324 hauth_324
      hA_into henc_334 hdec_334)
    (pqRatchetStateEncodeToVec_placed_ok_ext hA_into.panic_ok hshim_hook halloc_hook
      hrealloc_hook hmc_hook)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_proto_pq_ratchet_state_placed_ok hdealloc_270 hslice_270 hinner_270))

end LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlacedBudget
