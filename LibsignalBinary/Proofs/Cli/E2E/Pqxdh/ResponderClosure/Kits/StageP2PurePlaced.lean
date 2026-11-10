/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Relocatable Stage P2 Pure and Internal Callee Instantiation

Lifts the Stage P2 pure, drop-glue, and Block `75` (`initialize_bob_session`) internal callees to
`stageP1ProgPlaced ext` (`lsProg_518 ext`) and constructs `StageP2PureCalleesPlaced{,4K}` and
`StageP2BaseCalleesPlaced4K`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding
  bv_sub_add_lit' stackAt_split_top sepWPp_pure_mid
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding sessionRecordEmptyHeaderAt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-! ## 1. `TrapsOnly` Extern-Table Refinement Lifting -/

theorem InitializeBobV1MemInvOkAtPlaced.of_trapsOnly [LibsignalPlacement]
    {Φ : Memory → Prop} {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkAtPlaced Φ P A F ext1 bobV1Stk) :
    InitializeBobV1MemInvOkAtPlaced Φ P A F ext2 bobV1Stk := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  exact SepWPp.of_trapsOnly hT
    (h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)

theorem InitializeBobV1OkAtPlaced.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkAtPlaced P A F ext1 bobV1Stk) :
    InitializeBobV1OkAtPlaced P A F ext2 bobV1Stk :=
  InitializeBobV1MemInvOkAtPlaced.of_trapsOnly hT h

theorem InitializeBobV1FrozenOkAtPlaced.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkAtPlaced P A F ext1 bobV1Stk) :
    InitializeBobV1FrozenOkAtPlaced P A F ext2 bobV1Stk :=
  InitializeBobV1MemInvOkAtPlaced.of_trapsOnly hT h

theorem InitializeBobV1FrozenOkPlaced.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlaced P A F ext1) :
    InitializeBobV1FrozenOkPlaced P A F ext2 :=
  InitializeBobV1MemInvOkAtPlaced.of_trapsOnly hT h

theorem InitializeBobV1FrozenOkPlaced4K.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlaced4K P A F ext1) :
    InitializeBobV1FrozenOkPlaced4K P A F ext2 :=
  InitializeBobV1MemInvOkAtPlaced.of_trapsOnly hT h

theorem InitializeBobV1OkPlaced.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlaced P A F ext1) :
    InitializeBobV1OkPlaced P A F ext2 :=
  InitializeBobV1OkAtPlaced.of_trapsOnly hT h

theorem InitializeBobV1OkPlaced4K.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlaced4K P A F ext1) :
    InitializeBobV1OkPlaced4K P A F ext2 :=
  InitializeBobV1OkAtPlaced.of_trapsOnly hT h

theorem StageP2PureCalleesPlaced.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlaced P A F ext1) :
    StageP2PureCalleesPlaced P A F ext2 where
  publicKeySerialize := subroutine_ok.of_trapsOnly hT h.publicKeySerialize
  promoteMatchingSessionEmpty := subroutine_ok.of_trapsOnly hT h.promoteMatchingSessionEmpty
  curveKeyPairSerde := subroutine_ok.of_trapsOnly hT h.curveKeyPairSerde
  kemKeyPairSerde := subroutine_ok.of_trapsOnly hT h.kemKeyPairSerde
  preKeyRecordKeyPair := subroutine_ok.of_trapsOnly hT h.preKeyRecordKeyPair
  dropSpe2 := subroutine_ok.of_trapsOnly hT h.dropSpe2
  isSameAccount := subroutine_ok.of_trapsOnly hT h.isSameAccount
  initializeBobV1 := InitializeBobV1OkPlaced.of_trapsOnly hT h.initializeBobV1
  initializeBobErr := subroutine_ok.of_trapsOnly hT h.initializeBobErr
  promoteStateEmpty := subroutine_ok.of_trapsOnly hT h.promoteStateEmpty
  dropProcessPrekeyImplState1 := subroutine_ok.of_trapsOnly hT h.dropProcessPrekeyImplState1
  dropSessionStructure3 := subroutine_ok.of_trapsOnly hT h.dropSessionStructure3

theorem StageP2BaseCalleesPlaced4K.of_trapsOnly [LibsignalPlacement]
    {A : RustAlloc} {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2BaseCalleesPlaced4K A ext1) :
    StageP2BaseCalleesPlaced4K A ext2 where
  publicKeySerialize := subroutine_ok.of_trapsOnly hT h.publicKeySerialize
  promoteMatchingSessionEmpty := subroutine_ok.of_trapsOnly hT h.promoteMatchingSessionEmpty
  curveKeyPairSerde := subroutine_ok.of_trapsOnly hT h.curveKeyPairSerde
  kemKeyPairSerde := subroutine_ok.of_trapsOnly hT h.kemKeyPairSerde
  preKeyRecordKeyPair := subroutine_ok.of_trapsOnly hT h.preKeyRecordKeyPair
  dropSpe2 := subroutine_ok.of_trapsOnly hT h.dropSpe2
  isSameAccount := subroutine_ok.of_trapsOnly hT h.isSameAccount
  promoteStateEmpty := subroutine_ok.of_trapsOnly hT h.promoteStateEmpty
  dropProcessPrekeyImplState1 := subroutine_ok.of_trapsOnly hT h.dropProcessPrekeyImplState1
  dropSessionStructure3 := subroutine_ok.of_trapsOnly hT h.dropSessionStructure3

theorem StageP2PureCalleesPlaced4K.of_trapsOnly [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlaced4K P A F ext1) :
    StageP2PureCalleesPlaced4K P A F ext2 :=
  { StageP2BaseCalleesPlaced4K.of_trapsOnly hT h.toStageP2BaseCalleesPlaced4K with
    initializeBobV1 := InitializeBobV1OkPlaced4K.of_trapsOnly hT h.initializeBobV1
    initializeBobErr := subroutine_ok.of_trapsOnly hT h.initializeBobErr }

/-! ## 2. Block-Lifted Pure & Hook-Backed Internal Callees (`stageP1ProgPlaced ext`) -/

/-- `SessionRecord::promote_matching_session` (`lsmpl.base 50`) on `stageP1ProgPlaced ext`. -/
theorem promote_matching_session_empty_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 50)
    (ResponderStore.promote_matching_session_empty_placed_ok ext) (by decide)

/-- `<curve::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 112`) on
`stageP1ProgPlaced ext`. -/
theorem curveKeyPairSerde_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeOkSpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 112)
    (ResponderStore.curveKeyPairSerde_placed_ok ext) (by decide)

/-- `<PreKeyRecord>::key_pair` (`lsmpl.base 67`) on `stageP1ProgPlaced ext`. -/
theorem preKeyRecordKeyPair_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairOkSpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 67)
    (ResponderStore.preKeyRecordKeyPair_placed_ok ext) (by decide)

/-- `SessionRecord::promote_state` (`lsmpl.base 47`, 0-stack `framelessMemcpySpec`) on
`stageP1ProgPlaced ext`. -/
theorem promote_state_empty_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmptySpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 47)
    (ResponderStore.promote_state_empty_placed_ok ext hMemcpy) (by decide)

section Placed4KCallees

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit ResponderStore.bv_sub_add_lit' BitVec.toNat_zero

private theorem p2_cells_sub32_4_merge_placed (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem p2_stackAt_kemKeyPairFromPubPriv_placed (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := ResponderStore.stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

private theorem p2_stackAt_promote_state_split_placed (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 4000 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 := by
  dsimp only [stackAt, allocHookStack]
  rw [show (4096 : Nat) = 4000 + (64 + 32) by decide,
    memRegion_split (sp - 4096#64) 4000 (64 + 32) (by decide),
    show sp - 4096#64 + 4000#64 = sp - 96#64 by bv_omega,
    memRegion_split (sp - 96#64) 64 32 (by decide),
    show sp - 96#64 + 64#64 = sp - 32#64 by bv_omega,
    ProofLib.memRegion_cells (sp - 96#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]

/-- 4 KiB-stacked `SessionRecord::promote_state` (`lsmpl.base 47`, `p2Memcpy4KSpec`) on
`stageP1ProgPlaced ext`. -/
theorem promote_state_empty_4k_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
  have h47 : subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext) (blkPl_47).base
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
    unfold promoteStateEmpty4KSpec
    have harch := ls_subroutine_ok_cl_of_plain
      (callerProg := (blkPC_47).rebase (blkPl_47).base ext) (entry := lsmpl.base 51)
      (ResponderStore.archive_current_state_inner_empty_placed_ok ext)
    have hmc : subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext)
        (lsρ lsMemcpySym) p2Memcpy4KSpec :=
      ls_hook_ok_of_mem hMemcpy
    dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hmc
    wp_init x s0
    obtain ⟨recPtr, srcPtr, bs⟩ := x
    dsimp only [withLsCodeLoaded] at *
    subst h_2 h_3
    rw (occs := .pos [1]) [p2_stackAt_promote_state_split_placed s0.sp]
    have hc4 : cells (s0.sp - 32#64) 4 =
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
      cells_unfold
    rw [hc4]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    wp_steps_lscl (lsmpl.base 51)
    have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
    wp_call harch (s0.readReg64 (.gpr 0#5))
    wp_steps
    apply ProofLib.SepWP.replace_pre (by sep_focus)
      (ResponderStore.pointsTo64_memRegion_336_entails_344
        (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
    apply ProofLib.SepWP.replace_pre (by sep_focus)
      (p2_cells_sub32_4_merge_placed s0.sp _ _ _ _)
    refine SepWP.fold (Entails.of_eq (p2_stackAt_promote_state_split_placed s0.sp).symm)
      (by sep_focus) ?_
    rw [← h_1]
    wp_call hmc (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
    simp only [h_1] at *
    wp_done
  exact ls_subroutine_ok_of_block (i := 518) (j := 47) h47 (by decide)

set_option maxHeartbeats 1200000 in
/-- 4 KiB-stacked `<kem::KeyPair>::from_public_and_private` (`Block 70`) under `noAllocShimSpec`,
`rustAllocSpec A`, `p2Memcpy4KSpec`, and `handle_alloc_error` panic. -/
theorem kemKeyPairFromPubPriv_4k_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPanAlloc : ext Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec A) := by
  unfold kemKeyPairFromPubPrivOkSpec
  simp only [p2_stackAt_kemKeyPairFromPubPriv_placed]
  simp only [cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hshim_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ Keys.lsRustNoAllocShimSym) noAllocShimSpec :=
    ls_hook_ok_of_mem hShim
  have halloc_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ Keys.lsRustAllocSym) (rustAllocSpec A) :=
    ls_hook_ok_of_mem hAlloc
  have hmemcpy_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ lsMemcpySym) p2Memcpy4KSpec :=
    ls_hook_ok_of_mem hMemcpy
  dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hmemcpy_ok
  have hpanic_ok : ((blkPC_70).rebase (blkPl_70).base ext).externAt?
      (lsρ Keys.lsHandleAllocErrorSym) = some Rust.panicked :=
    (ls_externAt?_of_mem (sym := Keys.lsHandleAllocErrorSym)).trans hPanAlloc
  wpp_init g s0
  simp only [sepConj_assoc]
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_3 h_5
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : LayoutOk 1568 1 := ⟨by decide, hpow2, by decide⟩
  have hlay2 : LayoutOk 3168 1 := ⟨by decide, hpow2, by decide⟩
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  apply SepWPp.of_sepWP (mid := (blkPl_70).base + 76#64)
  wp_steps
  wp_call hshim_ok ()
  wp_steps
  wp_call halloc_ok (1568, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine ResponderStore.sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ Keys.lsHandleAllocErrorSym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply.SepWPp_panic_oom
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic_ok (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine ResponderStore.sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_70).base + 140#64)
    wp_steps
    rw [← h_6]
    wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 0#5) + 1#64, pk)
    simp only [h_6] at *
    wp_steps
    wp_call hshim_ok ()
    wp_steps
    wp_call halloc_ok (3168, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine ResponderStore.sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ Keys.lsHandleAllocErrorSym)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply.SepWPp_panic_oom
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic_ok (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine ResponderStore.sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← h]
      wp_call hmemcpy_ok (sf_4.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 2#5) + 1#64, sk)
      simp only [h] at *
      wp_steps
      wp_done

/-- 4 KiB-stacked `<kem::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 113`) on
`stageP1ProgPlaced ext`. -/
theorem kemKeyPairSerde_4k_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPanAlloc : ext Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A)) := by
  have h113 : subroutine_ok ((blkPC_113).rebase (blkPl_113).base ext) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A)) := by
    have hinner := ls_subroutine_ok_of_block
      (callerProg := (blkPC_113).rebase (blkPl_113).base ext)
      (entry := lsmpl.base 70)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (kemKeyPairFromPubPriv_4k_placed_ok hShim hAlloc hMemcpy hPanAlloc))
    exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm])
      rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)
  exact ls_subroutine_ok_of_block (i := 518) (j := 113) h113 (by decide)

/-- 0-stack `<kem::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 113`,
`sessionShimSpec` + `sessionMemcpyRegionSpec`) on `stageP1ProgPlaced ext`. -/
theorem kemKeyPairSerde_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym sessionShimSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustAllocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hPanAlloc : ext ResponderStore.lsAllocHandleErrorSym = some Rust.panicked) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec A)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 113)
    (ResponderStore.kemKeyPairSerde_placed_ok hShim hAlloc hMemcpy hPanAlloc) (by decide)

end Placed4KCallees

/-! ## 3. Drop Glue & `is_same_account` Bridges on `stageP1ProgPlaced ext` -/

/-- `drop_glue::<SignalProtocolError> [local#2]` (`lsmpl.base 511`) on `stageP1ProgPlaced ext`. -/
theorem drop_spe2_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (Getters.withLsRoLoaded lsmpl (Getters.dropSpeSpec A))) :=
  Getters.drop_spe2_placed_ok_at hDealloc (by decide)

/-- `drop_glue::<SessionStructure> [local#4]` (`lsmpl.base 512`) on `stageP1ProgPlaced ext`. -/
theorem drop_session_structure3_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) :=
  GenP3.drop_session_structure4_placed_ok_at hDealloc (by decide)

/-- `<IdentityKey>::is_same_account` (`lsmpl.base 17`) on `stageP1ProgPlaced ext`. -/
theorem isSameAccount_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : ext lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec A uuidTryParse)) :=
  WireEntries.isSameAccountEqDistinct_placed_ok_at A hBb hUuid (by decide)

/-- 4K/`Ext` `<IdentityKey>::is_same_account` (`lsmpl.base 17`) on `stageP1ProgPlaced ext`. -/
theorem isSameAccount_4k_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : ext lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A
          uuidTryParse)) :=
  isSameAccountDistinctSpec_lscl_to_ext (isSameAccount_placed_ok_on_stageP1 hBb hUuid)

/-! ## 4. Cross-Block `initialize_bob_session` (`Block 75`) Bridges on `stageP1ProgPlaced ext` -/

/-- Cross-block `SepWPp` transfer from a non-mutated callee block `j` (`calleeProg`) to any
`callerProg` sharing `H` when `LibsignalCodeLoaded lsmpl s.mem` holds. -/
theorem ls_sepWPp_of_block [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee : IsLsBlockProg calleeProg j H]
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp calleeProg ret s P Q Qp oom)
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWPp callerProg ret s P Q Qp oom := by
  intro R hm _hcallerL
  have hQL : calleeProg.CodeLoaded s.mem :=
    hcallee.eq_blockProgram ▸ hcl j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout⟩ := h R hm hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact ⟨sf, Steps.of_sameHooks hext hsvc hstepsQ, hout⟩

/-- Rejecting run of `initialize_bob_session` (`lsmpl.base 75`, `initializeBobSessionErrPlacedSpec`)
on `stageP1ProgPlaced ext` from `h_accept` on `lsProg_75 ext`. -/
theorem initializeBobSession_err_placed_ok_on_stageP1 [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrPlacedSpec P A) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
    (LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (ResponderCore.initializeBobSession_err_placed_ok_of_accept h_accept)
      (by decide) (by decide) (by decide))

/-- 4K/`Ext` rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`initializeBobSessionErr4KPlacedSpec`) on `stageP1ProgPlaced ext` from `h_accept`. -/
theorem initializeBobSession_err_4k_placed_ok_on_stageP1 [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErr4KPlacedSpec P A) :=
  initializeBobSessionErrPlacedSpec_to_4K (initializeBobSession_err_placed_ok_on_stageP1 h_accept)

/-- Owned-error rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`ResponderCore.initializeBobSessionErrOwnedPlacedSpec`) on `stageP1ProgPlaced ext` from `h_accept`. -/
theorem initializeBobSession_err_owned_placed_ok_on_stageP1 [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptErrOwnedPlacedSpec P A)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A) :=
  LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
    (LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (ResponderCore.initializeBobSession_err_owned_placed_ok_of_accept h_accept)
      (by decide) (by decide) (by decide))

private theorem p2_initBobErrOwnedAt_to_initBobErrAt_placed (A : RustAlloc) (outPtr : BitVec 64) :
    ResponderCore.initBobErrOwnedAt A outPtr ∗ anyHeap ⊢ initBobErrAt outPtr ∗ anyHeap := by
  unfold ResponderCore.initBobErrOwnedAt
  conv =>
    lhs
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  rw [sepConj_left_comm]
  refine Entails.pure_left fun herr => ?_
  have h1 :
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        (((outPtr + 8#64) ↦₆₄ errTag) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗
          (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
            (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
              (ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
                (memRegion (outPtr + 56#64) 288 ∗ anyHeap)))))))) =
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        ((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 288) ∗
      (anyHeap ∗ ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4) := by ac_rfl
  rw [h1]
  exact sepConj_mono (initBobErrAt_merge outPtr errTag w2 w3 w4 w5 w6 herr) (entails_anyHeap _)

/-- Weaken `ResponderCore.initializeBobSessionErrOwnedPlacedSpec` to unowned
`initializeBobSessionErrPlacedSpec`. -/
theorem initializeBobSession_err_of_err_owned_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A)) :
    subroutine_ok prog entry (initializeBobSessionErrPlacedSpec P A) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        LibsignalTripleRatchet.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
        LibsignalTripleRatchet.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
    LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hnone : Model.acceptKeys P g.inp = none := hpre.1.2.2.2.2.2.2.2.2.2
  refine ⟨g, R, ?_, fun sf hpost => ?_, fun sf hpan => hpan⟩
  · dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact hpre
  · dsimp only [ResponderCore.initializeBobSessionErrOwnedPlacedSpec,
      ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec,
      initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionInnerPlacedSpec,
      LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost ⊢
    rw [hnone]
    refine Arm64.Satisfies.mono ?_ hpost
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
    exact sepConj_mono_left (p2_initBobErrOwnedAt_to_initBobErrAt_placed A g.outPtr)

/-- 4K/`Ext` weakening from `ResponderCore.initializeBobSessionErrOwnedPlacedSpec` to
`initializeBobSessionErr4KPlacedSpec`. -/
theorem initializeBobSession_err_4k_of_err_owned_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {P : Primitives} {A : RustAlloc}
    (h : subroutine_ok prog entry (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A)) :
    subroutine_ok prog entry (initializeBobSessionErr4KPlacedSpec P A) :=
  initializeBobSessionErrPlacedSpec_to_4K (initializeBobSession_err_of_err_owned_placed h)

/-- SPQR V1 `initialize_bob_session` success (`InitializeBobV1OkPlaced`) on `stageP1ProgPlaced ext`
from `h_accept` and `hinit` on `lsProg_75 ext`. -/
theorem initializeBobSession_ok_v1_placed_on_stageP1 [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    InitializeBobV1OkPlaced P A F ext := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  exact ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) hCode.1
    (CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_placed_of_accept
      hWF hShim hAlloc hDealloc hMemcpy hPan h_accept hinit
      s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)

/-- 4K/`Ext` SPQR V1 `initialize_bob_session` success (`InitializeBobV1OkPlaced4K`) on
`stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_4k_placed_on_stageP1 [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    InitializeBobV1OkPlaced4K P A F ext :=
  InitializeBobV1OkPlaced.to_4K
    (initializeBobSession_ok_v1_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpy hPan h_accept hinit)

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec`) on
`stageP1ProgPlaced ext`, discharging Block `79` (`Pqxdh::accept`) via `withLsFrozen`. -/
theorem initializeBobSession_err_owned_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec P A)) := by
  have hbase :=
    ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (ResponderCore.initializeBobSession_err_owned_full_placed_ok hWF hP hH h_memcpy)
  refine subroutine_ok_map_panic hbase ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec, withLsFrozen] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec, withLsFrozen] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost, fun _ hpan => hpan⟩
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec`) on
`stageP1ProgPlaced ext`. -/
theorem initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec P A) :=
  Sub5Placed.of_responderCore_errOwned_to_4K_frozen_placed
    (initializeBobSession_err_owned_full_placed_ok_on_stageP1 hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` SPQR V1 `initialize_bob_session` success
(`InitializeBobV1FrozenOkPlaced`) on `stageP1ProgPlaced ext`, discharging Block `79`
(`Pqxdh::accept`) via `withLsFrozen` and taking only the `spqr::initial_state` seam. -/
theorem initializeBobSession_ok_v1_full_placed_on_stageP1 [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    InitializeBobV1FrozenOkPlaced P A F ext := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  exact ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_full_placed
      hWF hP hH h_memcpy hMemcpySess hinit
      s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` SPQR V1 `initialize_bob_session` success
(`InitializeBobV1FrozenOkPlaced4K`) on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1 [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    InitializeBobV1FrozenOkPlaced4K P A F ext :=
  InitializeBobV1MemInvOkPlaced.to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1 hWF hP hH h_memcpy hMemcpySess hinit)

/-! ## 5. `StageP2BaseCalleesPlaced4K`, `StageP2PureCalleesPlaced`, and `StageP2PureCalleesPlaced4K` Bundle Constructors -/

/-- Construct `StageP2BaseCalleesPlaced4K` directly on `stageP1ProgPlaced ext` under
`[LibsignalPlacement]` with zero Block `79` (`Pqxdh::accept`) or Block `327` (`spqr::initial_state`)
seams. -/
theorem StageP2BaseCalleesPlaced4K.of_hooks [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked)
    (hPanAlloc : ext Keys.lsHandleAllocErrorSym = some Rust.panicked)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A
          uuidTryParse))) :
    StageP2BaseCalleesPlaced4K A ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc hPan
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K hPanAlloc
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  promoteStateEmpty := promote_state_empty_4k_placed_ok_at hMemcpy4K
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

abbrev stageP2BaseCalleesPlaced4K_of_hooks := @StageP2BaseCalleesPlaced4K.of_hooks

/-- Construct `StageP2PureCalleesPlaced` on `stageP1ProgPlaced ext` from contract-backed hook
hypotheses and the Block `79` (`Pqxdh::accept`) + Block `327` (`spqr::initial_state`) seams. -/
theorem StageP2PureCalleesPlaced.of_hooks [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked)
    (hPanAlloc : ext Keys.lsHandleAllocErrorSym = some Rust.panicked)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec A uuidTryParse)))
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    StageP2PureCalleesPlaced P A F ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc hPan
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K hPanAlloc
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  initializeBobV1 :=
    initializeBobSession_ok_v1_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpySess hPan h_accept hinit
  initializeBobErr := initializeBobSession_err_placed_ok_on_stageP1 h_accept
  promoteStateEmpty := promote_state_empty_placed_ok_at hMemcpy
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

/-- Construct `StageP2PureCalleesPlaced4K` directly on `stageP1ProgPlaced ext` from 4 KiB
contract-backed hook hypotheses (`p2Memcpy4KSpec` + `sessionMemcpyRegionSpec` for `BobTailV1Placed`)
and the Block `79` (`Pqxdh::accept`) + Block `327` (`spqr::initial_state`) seams. -/
theorem StageP2PureCalleesPlaced4K.of_hooks [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext Keys.lsRustNoAllocShimSym noAllocShimSpec)
    (hAlloc : HookSat ext Keys.lsRustAllocSym (rustAllocSpec A))
    (hDealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A))
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hPan : ext lsHandleErrorSym = some Rust.panicked)
    (hPanAlloc : ext Keys.lsHandleAllocErrorSym = some Rust.panicked)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A
          uuidTryParse)))
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A))
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    StageP2PureCalleesPlaced4K P A F ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc hPan
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K hPanAlloc
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  initializeBobV1 :=
    initializeBobSession_ok_v1_4k_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpySess hPan h_accept hinit
  initializeBobErr := initializeBobSession_err_4k_placed_ok_on_stageP1 h_accept
  promoteStateEmpty := promote_state_empty_4k_placed_ok_at hMemcpy4K
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

abbrev stageP2PureCalleesPlaced4K_of_hooks := @StageP2PureCalleesPlaced4K.of_hooks

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
