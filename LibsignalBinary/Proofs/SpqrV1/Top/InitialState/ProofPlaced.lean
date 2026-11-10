/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.TopPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable Verification of `spqr::initial_state`

Proves `InitialStatePlacedOkX` and `InitialStatePlacedOkBlockProgram` for `spqr::initial_state`
(Block `327`) under `[LibsignalPlacement]` by dispatching on `params.version` (`.v0` and `.v1`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitialState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [-arm64_norm]
  Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp Expand.esp_add_496_sub_496
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688 Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Callee Contract Bundle (`InitialStateContractsPlaced`) -/

/-- Relocatable callee contracts of `spqr::initial_state` (`Block 327`). -/
structure InitialStateContractsPlaced [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop where
  panic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec
  alloc_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A)
  memcpy_ok : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec
  initInner_ok : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
    (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX A F))
  encodeToVec_ok : PqRatchetStateEncodeToVecPlacedOkExt A ext
  dropPqRatchetState_ok : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
    (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))

/-! ## 2. Dispatch on `params.version` -/

/-- `initialStatePlacedSpecX` restricted to `p.version = v`. -/
def initialStateVPlacedSpecX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (v : Version) :
    Spec InitialStateGhost :=
  { initialStatePlacedSpecX A F with
    pre := fun x s => ⌜x.p.version = v⌝ ∗ (initialStatePlacedSpecX A F).pre x s }

/-- `InitialStatePlacedOkX` from its two version cases (`.v0` and `.v1`). -/
theorem initialState_placed_ok_of_versions [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h0 : subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX A F .v0))
    (h1 : subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX A F .v1)) :
    InitialStatePlacedOkX A F ext := by
  dsimp only [InitialStatePlacedOkX]
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have key : ∀ v, x.p.version = v →
      s0.mem ⊨ (initialStateVPlacedSpecX A F v).pre x s0 ∗ R := by
    intro v hv
    dsimp only [initialStateVPlacedSpecX]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hv, hpre⟩
  cases hv : x.p.version with
  | v0 => exact h0.mono_outcome x R s0 hpc hrun (key .v0 hv) hsp fun _ hout => hout
  | v1 => exact h1.mono_outcome x R s0 hpc hrun (key .v1 hv) hsp fun _ hout => hout

/-! ## 3. V0 Path on `Block 327` (`initialState_v0_placed_ok`) -/

private def initialStatePlacedSavedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
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
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private theorem initialStatePlacedSavedCells_entails_memRegion (s0 : State) :
    initialStatePlacedSavedCells s0 ⊢ memRegion (s0.sp - 96#64) 96 := by
  unfold initialStatePlacedSavedCells
  rw [ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  cells_unfold
  refine Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
      (Entails.sepExists_right (s0.readReg64 .x28)
        (Entails.sepExists_right (s0.readReg64 .x27)
          (Entails.sepExists_right (s0.readReg64 .x26)
            (Entails.sepExists_right (s0.readReg64 .x25)
              (Entails.sepExists_right (s0.readReg64 .x24)
                (Entails.sepExists_right (s0.readReg64 .x23)
                  (Entails.sepExists_right (s0.readReg64 .x22)
                    (Entails.sepExists_right (s0.readReg64 .x21)
                      (Entails.sepExists_right (s0.readReg64 .x20)
                        (Entails.sepExists_right (s0.readReg64 .x19) ?_)))))))))))
  exact Entails.of_eq (by simp only [arm64_norm])

private theorem stackAt_initialState_placed_split (sp : BitVec 64) :
    stackAt sp initialStateStack =
      stackAt (sp - 496#64) initialStateCalleeStack ∗
      memRegion (sp - 496#64) 400 ∗
      cells (sp - 96#64) 12 := by
  unfold stackAt initialStateStack initialStateFrame
  rw [ProofLib.memRegion_split'
        (b := sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack))
        (n := initialStateCalleeStack) (k := 496)
        (b' := sp - 496#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 496#64) (n := 400) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 496#64) - BitVec.ofNat 64 initialStateCalleeStack =
      sp - BitVec.ofNat 64 (0x1f0 + initialStateCalleeStack) := by
    dsimp only [initialStateCalleeStack, initInnerStack, initInnerFrame, authNewStackX,
      encodeToVecStackX, dropStack96, allocHookStack]
    bv_omega
  rw [hsub]

private theorem stack_restore_initialState_placed (s0 : State) :
    stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
    memRegion (s0.sp - 496#64) 400 ∗
    initialStatePlacedSavedCells s0 ⊢
    stackAt s0.sp initialStateStack := by
  rw [stackAt_initialState_placed_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initialStatePlacedSavedCells_entails_memRegion s0))

private theorem initialStateResultAt_v0_of_cells_placed (A : RustAlloc) (F : ShaCompress)
    (ret : BitVec 64) (p : CryptoVerification.LibsignalSpqrV1.Params) (hv : p.version = .v0) :
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
    ((ret + 16#64) ↦₆₄ 1#64) ∗ ((ret + 24#64) ↦₆₄ 0#64) ⊢
    initialStateResultAt A ret (initialStateValue F p) := by
  unfold initialStateResultAt initialStateValue
  rw [hv]
  dsimp [emptyState]
  have h16 : (ret + 8#64) + 8#64 = ret + 16#64 := by bv_omega
  have h24 : (ret + 8#64) + 16#64 = ret + 24#64 := by bv_omega
  have hvec := vecU8_nil_of_cells A (ret + 8#64)
  rw [h16, h24] at hvec
  exact sepConj_mono_right hvec

theorem initialState_v0_step_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 : State) (x : InitialStateGhost) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.pA)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hv : x.p.version = .v0) :
    SepWP (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (paramsAt x.pA x.akPtr x.p ∗
       memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗
       Rest)
      (fun sf Pf =>
        (Pf ⊢
          paramsAt x.pA x.akPtr x.p ∗
          initialStateResultAt A x.ret (initialStateValue F x.p) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt s0.sp initialStateStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hrestore :
      paramsAt x.pA x.akPtr x.p ∗
      ((x.ret ↦₆₄ 0#64) ∗ ((x.ret + 8#64) ↦₆₄ 0#64) ∗
       ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64)) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      (stackAt (s0.sp - 496#64) initialStateCalleeStack ∗
       memRegion (s0.sp - 496#64) 400 ∗
       initialStatePlacedSavedCells s0) ∗
      Rest ⊢
      paramsAt x.pA x.akPtr x.p ∗
      initialStateResultAt A x.ret (initialStateValue F x.p) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp initialStateStack ∗
      Rest :=
    sepConj_mono_right (sepConj_mono (initialStateResultAt_v0_of_cells_placed A F x.ret x.p hv)
      (sepConj_mono_right (sepConj_mono_left (stack_restore_initialState_placed s0))))
  refine SepWP.strengthen_entails_const hrestore ?_
  have hsp496_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hv_i32 : x.p.version.toI32 = 0#32 := by rw [hv]; rfl
  dsimp only [initialStatePlacedProg, initialStatePlacedEntry, lsLogFilterAddr,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [ProofLib.memRegion_cells x.ret 4 (by decide),
      stackAt_initialState_placed_split s0.sp]
  unfold paramsAt
  rw [hv_i32]
  dsimp only [initialStatePlacedSavedCells]
  simp only [sepConj_assoc]
  cells_unfold
  dsimp only [ProofLib.cells]
  simp only [sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- `version = .v0` returns `Ok(vec![])` without calls. -/
theorem initialState_v0_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX A F .v0) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hsp0_align => ?_
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, initialStatePlacedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hcrl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, _hak_ne, _hlen⟩, hm⟩
  have hpre_eq :
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ memRegion x.ret 32 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp initialStateStack ∗ ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool)) ∗ R := by
    ac_rfl
  rw [hpre_eq] at hm
  refine ⟨_, R, hm, SepWP.mono (initialState_v0_step_placed (A := A) (F := F) s0 x
    ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool) hsp0_align hpc hrun hx0 hx8 hv) ?_⟩
  rintro sf P_f _ _ ⟨hent, hspf, hcsf, htrf⟩
  refine ⟨fun hmf => ?_, hspf, hcsf⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
  have hpost_eq :
      (paramsAt x.pA x.akPtr x.p ∗ initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp initialStateStack ∗
       ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool)) ∗ R =
      (paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R := by
    ac_rfl
  rwa [hpost_eq] at hmf'

/-! ## 4. V1 Path on `Block 327` (`initialState_v1_placed_ok`) -/

/-- `version = .v1` executes `auth_key.to_vec()`, `spqr::init_inner`,
    `PqRatchetState::encode_to_vec`, and `drop_glue::<PqRatchetState>`. -/
theorem initialState_v1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsPlaced A F ext) :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX A F .v1) := by
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, initialStatePlacedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl0, hro0⟩, hpre⟩ := hpre
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨hro0, hcl0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen⟩, hmem⟩ := hpre
  have hmem1 := lsro_optProtoInnerStateJumpTablePlacedAt hro0 hmem
  have hmem2 := lsro_statesIntoPbJumpTablePlacedAt hro0 hmem1
  have hmem3 : s0.mem ⊨
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_placed hC.panic_ok hC.shim_ok hC.alloc_ok hC.memcpy_ok
    hC.initInner_ok hC.encodeToVec_ok hC.dropPqRatchetState_ok
    s0 x R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (Top.Recv.protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  exact ⟨_, R, hmem3, sepWPp_of_initialState_v1_placed_wpp s0 x _ R hwpp⟩

/-! ## 5. Top-Level Relocatable `[LibsignalPlacement]` Theorems -/

/-- Proves `InitialStatePlacedOkX` from `InitialStateContractsPlaced`. -/
theorem initialState_placed_ok_x_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hC : InitialStateContractsPlaced A F ext) :
    InitialStatePlacedOkX A F ext :=
  initialState_placed_ok_of_versions initialState_v0_placed_ok (initialState_v1_placed_ok hC)

/-- Assemble `InitialStateContractsPlaced A F ext` from external hook contracts and placed
    callee contracts (`InitInnerPlacedOkX`, `PqRatchetStateEncodeToVecPlacedOkExt`, and
    `drop_glue::<PqRatchetState>` on `Block 270`). -/
theorem initialStateContractsPlaced_of_okX [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    InitialStateContractsPlaced A F ext where
  panic_ok := h_panic
  shim_ok := hshim
  alloc_ok := halloc
  memcpy_ok := hmemcpy
  initInner_ok := by
    dsimp only [InitInnerPlacedOkX] at hInitInner
    rwa [IsLsBlockProg.eq_blockProgram (prog := (blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))]
  encodeToVec_ok := hEncodeToVec
  dropPqRatchetState_ok := hdrop

/-- Top-level relocatable `spqr::initial_state` (`Block 327`) theorem (`InitialStatePlacedOkX A
    F ext`). -/
theorem initial_state_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    InitialStatePlacedOkX A F ext :=
  initialState_placed_ok_x_of_contracts
    (initialStateContractsPlaced_of_okX h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop)

/-- Top-level relocatable `spqr::initial_state` (`Block 327`) theorem on
    `libsignalSessionLib.blockProgram lsmpl 327 (Rust.withPanics ext)` at `lsmpl.base 327`. -/
theorem initial_state_placed_ok_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    InitialStatePlacedOkBlockProgram A F ext := by
  have hok := initial_state_placed_ok_x h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop
  dsimp only [InitialStatePlacedOkBlockProgram, InitialStatePlacedOkX] at hok ⊢
  rwa [← IsLsBlockProg.eq_blockProgram (prog := initialStatePlacedProg ext)]

theorem withPanics_eq_of_isPanicSymbol {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked) :
    Rust.withPanics ext = ext := by
  funext sym
  unfold Rust.withPanics
  split
  · next h => exact (hp sym h).symm
  · rfl

theorem initial_state_placed_ok_blockProgram_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 327 ext) (lsmpl.base 327)
      (initialStatePlacedSpecX A F) := by
  have hok := initial_state_placed_ok_blockProgram h_panic hshim halloc hmemcpy hInitInner hEncodeToVec hdrop
  dsimp only [InitialStatePlacedOkBlockProgram] at hok
  rwa [withPanics_eq_of_isPanicSymbol hp] at hok

/-- Unconditional wiring of `spqr::initial_state` (`Block 327`) with internal SPQR blocks
    `init_inner` (`Block 324`), `<States>::into_pb` (`Block 334`),
    `PqRatchetState::encode_to_vec` (`Block 426`), and `drop_glue::<PqRatchetState>` (`Block
    270`) discharged internally. -/
theorem initial_state_placed_ok_unconditional [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy_327 : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym) framelessMemcpySpec)
    (hshim_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ lsMemcpySym) framelessMemcpySpec)
    (hauth_324 : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewSpec F A))
    (hA_into : States.IntoPb.StatesIntoPbAllocPlaced A ext)
    (henc_334 : subroutine_ok ((States.IntoPb.Placed.blkPC_334).rebase (States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (Poly.EncoderIntoPb.encoderIntoPbSpec A))
    (hdec_334 : subroutine_ok ((States.IntoPb.Placed.blkPC_334).rebase (States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (Poly.DecoderPb.decoderIntoPbSpec A))
    (hmemcpy_334 : subroutine_ok ((States.IntoPb.Placed.blkPC_334).rebase (States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hshim_hook : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_hook : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_hook : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hmc_hook : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionSpec)
    (hdealloc_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hslice_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (hinner_270 : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec A)) :
    InitialStatePlacedOkBlockProgram A F ext :=
  initial_state_placed_ok_blockProgram
    hA_into.panic_ok hshim_327 halloc_327 hmemcpy_327
    (init_inner_placed_ok_unconditional hshim_324 halloc_324 hmemcpy_324 hauth_324
      hA_into henc_334 hdec_334 hmemcpy_334)
    (pqRatchetStateEncodeToVec_placed_ok_ext hA_into.panic_ok hshim_hook halloc_hook hrealloc_hook hmc_hook)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_proto_pq_ratchet_state_placed_ok hdealloc_270 hslice_270 hinner_270))

end CryptoVerification.SpqrV1.Top.InitialState
