/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4Placed
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeStatePlaced -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlaced -- shake: keep

/-!
# Relocatable Contract Wiring & Composition for `spqr::recv`

`.rodata` extraction/restoration (`spqrRecvRoPlacedAt`), cross-block `withLsCodeRoLoaded` transfer
combinators, `SpqrRecvPlacedContracts` assembly, and top-level composition (`spqrRecv_placed_ok_of_tails`)
for `spqr::recv` (Block `329`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open CryptoVerification.SpqrV1.Top.Recv.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `.rodata` Extraction and Restoration for `spqrRecvRoPlacedAt` -/

theorem lsro_optProtoInnerStateJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ Drop.optProtoInnerStateJumpTablePlacedAt ∗ P := by
  unfold Drop.optProtoInnerStateJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := Drop.optProtoInnerStateJumpTableSym)
    (bs := Drop.optProtoInnerStateJumpTableBytes)
    hro (by decide +kernel) hP

theorem lsro_v1StateJumpTablesPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ P := by
  unfold Prost.MessageMerge.v1StateJumpTablesPlacedAt
  rw [sepConj_assoc]
  exact Prost.MessageMerge.rodata_v1StateMergeJumpTablePlacedExpanded hro
    (lsro_optProtoInnerStateJumpTablePlacedAt hro hP)

theorem lsro_statesFromPbJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesFromPbJumpTablePlacedAt ∗ P := by
  unfold statesFromPbJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := "spqr:.rodata.<spqr::v1::chunked::states::States>::from_pb")
    (bs := States.FromPb.statesFromPbJumpTableBytes)
    hro (by decide +kernel) hP

theorem lsro_statesRecvJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesRecvJumpTablePlacedAt ∗ P := by
  unfold statesRecvJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := "spqr:.rodata.<spqr::v1::chunked::states::States>::recv")
    (bs := States.Recv.statesRecvJumpTableBytes)
    hro (by decide +kernel) hP

theorem lsro_ctLabelPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ P :=
  lsro_intro_chk
    (sym := "spqr:.rodata..Lanon.137")
    (bs := Authenticator.ctLabel)
    hro (by decide +kernel) hP

theorem lsro_statesIntoPbJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTablePlacedAt ∗ P := by
  unfold statesIntoPbJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := "spqr:.rodata.<spqr::v1::chunked::states::States>::into_pb")
    (bs := States.IntoPb.statesIntoPbJumpTableBytes)
    hro (by decide +kernel) hP

/-- Extract `spqrRecvRoPlacedAt` from `(lsLogFilterAddr ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt
    ∗ P` under `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_spqrRecvRoPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp}
    (hP : s.mem ⊨ (lsLogFilterAddr ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt ∗ P) :
    s.mem ⊨ spqrRecvRoPlacedAt ∗ P := by
  have h1 := GF.UnacceleratedMul.rodata_reduceTable_placed hro hP
  have h2 := lsro_ctLabelPlacedAt hro h1
  have h3 := lsro_statesRecvJumpTablePlacedAt hro h2
  have h4 := lsro_v1StateJumpTablesPlacedAt hro h3
  have h5 := lsro_statesFromPbJumpTablePlacedAt hro h4
  have h6 := lsro_statesIntoPbJumpTablePlacedAt hro h5
  refine Satisfies.mono (Entails.of_eq ?_) h6
  dsimp only [spqrRecvRoPlacedAt, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt]
  ac_rfl

/-- Discard the read-only `.rodata` slices in `spqrRecvRoPlacedAt`, recovering `(lsLogFilterAddr
    ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt ∗ P`. -/
theorem spqrRecvRoPlacedAt_restore {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrRecvRoPlacedAt ∗ P) :
    m ⊨ (lsLogFilterAddr ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt ∗ P := by
  have hm' :
      m ⊨ (Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
           statesFromPbJumpTablePlacedAt ∗
           statesRecvJumpTablePlacedAt ∗
           ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
           GF.UnacceleratedMul.reduceTablePlacedAt ∗
           statesIntoPbJumpTablePlacedAt) ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [spqrRecvRoPlacedAt, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt]
    ac_rfl
  exact Satisfies.of_sep_right hm'

/-! ## 2. Cross-Block `withLsCodeRoLoaded` Transfer Combinators -/

theorem ls_subroutine_ok_cro_of_cro {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro h hi hj hj_unmut

theorem ls_subroutine_ok_cro_of_cl {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  have h_cro_j : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono h
      (fun _ _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withLsCodeLoaded] at hpre ⊢
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
        exact ⟨hpre.1.1, hpre.2⟩)
      (fun _ _ _ _ hpost => hpost)
  exact keys_ls_subroutine_ok_of_block_cro h_cro_j hi hj hj_unmut

theorem ls_subroutine_ok_cro_of_callInv {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCallInv lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  have h_cro_j : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono h
      (fun _ _ _ hpre => by
        dsimp only [withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withLsCallInv] at hpre ⊢
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hpre.1.2, hpre.1.1⟩, hpre.2⟩)
      (fun _ _ _ _ hpost => hpost)
  exact keys_ls_subroutine_ok_of_block_cro h_cro_j hi hj hj_unmut

theorem ls_subroutine_ok_cro_of_plain {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  ls_subroutine_ok_cro_of_cl (subroutine_ok_withLsCodeLoaded_of_plain h) hi hj hj_unmut

theorem ls_subroutine_ok_callInv_of_callInv {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCallInv lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCallInv lsmpl spec) := by
  have h_cro_i : subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
    ls_subroutine_ok_cro_of_callInv h hi hj hj_unmut
  exact subroutine_ok_mono h_cro_i
    (fun _ _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, withLsCallInv] at hpre ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hpre.1.2, hpre.1.1⟩, hpre.2⟩)
    (fun _ _ _ _ hpost => hpost)

/-! ## 3. Constructing `SpqrRecvPlacedContracts` from Placed Callee Theorems & `StatesPlacedSeams` -/

/-- Assemble `SpqrRecvPlacedContracts canonicalV1InnerHeap A F K ext` from placed callee
    contracts and `StatesPlacedSeams A F K ext`. -/
theorem spqrRecvPlacedContracts_of_okX
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpySpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (Drop.dropProtoEpochSliceSpec A)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (Drop.dropOptProtoInnerStatePlacedSpec A)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (Drop.dropOptProtoSpqrChainSpec A)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (Drop.dropSpqrChainSpec A)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (Drop.dropProtoPqRatchetStatePlacedSpec A)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (Drop.dropChunkedStatesLocal2PlacedSpec A F)))
    (hDecodeState : DecodeStatePlacedOkX canonicalV1InnerHeap A ext)
    (hInitInner : InitInnerPlacedOkX A F ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX A))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) A)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) A)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX (spqrHkdfWith F) A)))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX A))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi A ext)
    (hStatesIntoPb : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base (States.IntoPb.statesIntoPbPlacedRoSpecX A F))
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hSeams : StatesPlacedSeams A F K ext) :
    SpqrRecvPlacedContracts canonicalV1InnerHeap A F K ext where
  dealloc_ok := hdealloc
  memcpy_ok := hmemcpy
  dropEpochSlice_ok := hDropEpochSlice
  dropOptProtoInnerState_ok := hDropOptProtoInnerState
  dropOptProtoChain_ok := hDropOptProtoChain
  dropChain_ok := hDropChain
  dropPqRatchetState_ok := hDropPqRatchetState
  dropStates_ok := hDropStates
  decodeState_ok := ls_subroutine_ok_cro_of_cro hDecodeState
  initInner_ok := by
    have hinit_cro : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
        (lsmpl.base 324) (withLsCodeRoLoaded lsmpl (initInnerPlacedSpecX A F)) :=
      subroutine_ok_mono hInitInner
        (fun _ _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
            withLsCodeLoaded, InitInner.initInnerPlacedSpecX, initInnerPlacedSpecX] at hpre ⊢
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
          exact ⟨hpre.1.1, hpre.2⟩)
        (fun _ _ _ _ hpost => hpost)
    exact CryptoVerification.SpqrV1.ls_subroutine_ok_of_blockProgram_cro hinit_cro
  chainFrom_ok := by
    have h_fpb_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
        (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX A)) :=
      ls_subroutine_ok_callInv_of_callInv (subroutine_ok_withLsCallInv_of_plain hChainFromPb)
    have h_new_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
        (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) A)) :=
      ls_subroutine_ok_callInv_of_callInv hChainNew
    exact ls_subroutine_ok_cro_of_callInv (chainFrom_placed_ok_of_contracts_x h_fpb_323 h_new_323)
  chainFromPb_ok := ls_subroutine_ok_cro_of_plain hChainFromPb
  chainNew_ok := ls_subroutine_ok_cro_of_callInv hChainNew
  chainAddEpoch_ok := ls_subroutine_ok_cro_of_callInv hChainAddEpoch
  chainRecvKey_ok := ls_subroutine_ok_cro_of_callInv hChainRecvKey
  chainIntoPb_ok := ls_subroutine_ok_cro_of_plain hChainIntoPb
  messageDeserialize_ok := ls_subroutine_ok_cro_of_callInv hMsgDeser
  statesFromPb_ok := hSeams.statesFromPb_on
  statesRecv_ok := hSeams.statesRecv_on
  statesIntoPb_ok := ls_subroutine_ok_cro_of_plain hStatesIntoPb
  encodeToVec_ok := by
    have henc_cro : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
        (blkPl_426).base (withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A)) :=
      subroutine_ok_mono hEncodeToVec
        (fun _ _ _ hpre => by
          dsimp only [withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
            withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecX] at hpre ⊢
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          refine ⟨hpre.1.2, ?_⟩
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          exact ⟨hpre.1.1, hpre.2⟩)
        (fun _ _ _ _ hpost => hpost)
    exact ls_subroutine_ok_cro_of_cro henc_cro
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A

/-! ## 4. Relocatable Top-Level `spqr::recv` Specifications & Composition from Tails -/

/-- Relocatable raw specification of `spqr::recv` (`Block 329`) with `recvResultExactKeyAt`
    (without `withLsCodeRoLoaded`). -/
def spqrRecvPlacedRawSpecX (A : RustAlloc) (M : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool ∗ stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace ∧ ¬ M.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun (st, msg, _) s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ M.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Relocatable specification of `spqr::recv` (`Block 329`) with `withLsCodeRoLoaded lsmpl`. -/
def spqrRecvPlacedSpecX (A : RustAlloc) (M : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) :=
  withLsCodeRoLoaded lsmpl (spqrRecvPlacedRawSpecX A M)

/-- Relocatable raw specification of `spqr::recv` (`Block 329`) enriched with
    `GF.Mul2U16.tokenInitPlacedAt` and input bounds (`st.bytes.length < 2 ^ 32 ∧
    msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat`). -/
def spqrRecvPlacedRawSpecXT (A : RustAlloc) (M : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvPlacedRawSpecX A M with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecX A M).pre x s
    post := fun x s0 sf => GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecX A M).post x s0 sf }

/-- Relocatable specification of `spqr::recv` (`Block 329`) enriched with
    `GF.Mul2U16.tokenInitPlacedAt`, input bounds, and `withLsCodeRoLoaded lsmpl` (relocatable
    counterpart of `spqrRecvSpecExactKeyBounded`). -/
def spqrRecvPlacedSpecXT (A : RustAlloc) (M : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvPlacedSpecX A M with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedSpecX A M).pre x s
    post := fun x s0 sf => GF.Mul2U16.tokenInitPlacedAt ∗ (spqrRecvPlacedSpecX A M).post x s0 sf }

/-- `SepWPpLS` execution of `spqr::recv` (`Block 329`) from entry to `s0.readReg64 .x30`
    combining `step_prologue_to_312_placed` (`Part4Placed.lean`),
    `step_decode_and_dispatch_placed` (`Part5Placed.lean`), and the 3 version-branch tail
    contracts (`V0ChainPlacedTail`, `InitInnerPlacedTail`, `V1RatchetPlacedTailLS`). -/
theorem spqrRecv_placed_sepWPpLS_of_tails
    (H_inner : V1InnerHeapPred)
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hv0 : V0ChainPlacedTail A F K ext st msg ret s0 R)
    (hinit : InitInnerPlacedTail A F K ext st msg ret s0 R)
    (hv1 : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_prologue_to_312_placed A F K ext st msg ret s0 P R hpc hrun hsp_align hx0 hx1 hx8 hP
    (fun pre msgPtr s1 P1 hpre hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1 =>
      step_decode_and_dispatch_placed H_inner hC st msg ret pre msgPtr hst_len hpre hvalid
        s0 s1 P1 R hv0 hinit hv1 hsp_align
        hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1)

/-- `spqr::recv` (`Block 329`) satisfies `spqrRecvPlacedSpecXT A (spqrV1Recv F K)` on
    `spqrRecvPlacedProg ext` given `SpqrRecvPlacedContracts` and the 3 version-branch tails
    (`V0ChainPlacedTail`, `InitInnerPlacedTail`, `V1RatchetPlacedTailLS`). -/
theorem spqrRecv_placed_ok_of_tails
    (H_inner : V1InnerHeapPred)
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (hv0 : ∀ st msg ret s0 R, st.bytes.length < 2 ^ 32 → s0.spAligned = true →
      V0ChainPlacedTail A F K ext st msg ret s0 R)
    (hinit : ∀ st msg ret s0 R, st.bytes.length < 2 ^ 32 → s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      InitInnerPlacedTail A F K ext st msg ret s0 R)
    (hv1 : ∀ st msg ret s0 R, st.bytes.length < 2 ^ 32 → s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      V1RatchetPlacedTailLS A F K ext st msg ret s0 R) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A (spqrV1Recv F K)) := by
  have hok_core : subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      { spqrRecvPlacedSpecXT A (spqrV1Recv F K) with
        post := fun (st, msg, ret) s0 sf =>
          spqrRecvPlacedCorePost A (spqrV1Recv F K) st msg ret s0 sf } := by
    apply subroutine_ok_of_sepWPp
    intro ⟨st, msg, ret⟩ R s0 hpc hrun hpre hsp_align
    dsimp only [spqrRecvPlacedSpecXT, spqrRecvPlacedSpecX,
      withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      spqrRecvPlacedRawSpecX] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hst_len, _hmsg_len, hsp_lo⟩, hpre⟩
    have hpre1 :
        s0.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret⌝ ∗
            ((lsLogFilterAddr ↦₆₄ 0#64) ∗ GF.Mul2U16.tokenInitPlacedAt ∗
              (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R))) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre1
    rcases hpre1 with ⟨hcrl0, hpre2⟩
    rw [satisfies_pure_sepConj] at hpre2
    rcases hpre2 with ⟨⟨hx0, hx1, hx8⟩, hmem0⟩
    have hmem_ro :
        s0.mem ⊨ spqrRecvRoPlacedAt ∗
          (st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
      lsro_spqrRecvRoPlacedAt hcrl0.2 hmem0
    let P0 :=
      spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
    have hP0 : s0.mem ⊨ P0 ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [P0]; ac_rfl)) hmem_ro
    exact ⟨P0, R, hP0,
      spqrRecv_placed_sepWPpLS_of_tails H_inner hC st msg ret s0 P0 R hst_len
        (hv0 st msg ret s0 R hst_len hsp_align)
        (hinit st msg ret s0 R hst_len hsp_align hsp_lo)
        (hv1 st msg ret s0 R hst_len hsp_align hsp_lo)
        hpc hrun hsp_align hx0 hx1 hx8 rfl hcrl0⟩
  refine subroutine_ok_mono hok_core (fun _ _ _ h => h) ?_
  rintro ⟨st, msg, ret⟩ R s0 sf hcore
  have hro :
      sf.mem ⊨ spqrRecvRoPlacedAt ∗
        (⌜sf.trace = s0.trace ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
          recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
          A.pool ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by dsimp only [spqrRecvPlacedCorePost]; ac_rfl)) hcore
  have hlt := spqrRecvRoPlacedAt_restore hro
  dsimp only [spqrRecvPlacedSpecXT, spqrRecvPlacedSpecX,
    withLsCodeRoLoaded, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
    spqrRecvPlacedRawSpecX]
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hlt

end CryptoVerification.SpqrV1.Top.Recv
