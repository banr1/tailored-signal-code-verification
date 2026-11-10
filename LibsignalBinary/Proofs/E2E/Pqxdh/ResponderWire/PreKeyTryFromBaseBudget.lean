/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Base Specifications and Callees for `PreKeySignalMessage::try_from`

Provides `VmPreserved` contracts for Blocks `211` (`pkTryFromOk40`), `201` (`PublicKey::deserialize`),
and `116` (`IdentityKey::try_from`), together with allocator event envelopes and
`RustCliAllocBudget M` specifications for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`
(Block `111`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement IsLsBlockProg lsmpl lsLogFilterAddr
  withLsCodeLoaded withLsCl sepWP_seq_lscl
  ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_plain
  subroutine_ok_withLsCodeLoaded_of_plain
  blkPC_111 blkPl_111 blkLib_eq_111
  blkPC_116 blkPl_116 blkLib_eq_116
  blkPC_201 blkPl_201 blkLib_eq_201
  blkPC_211 blkPl_211
)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (
  lsLogOff pkTryFromPlacedSpec pkTryFromSpec pkTryFromResultAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (
  DeserGhost publicKey_deserialize_ok_inversion pointsToBytes_deserialize_split
)
open CryptoVerification.E2E.Pqxdh.ResponderWire (
  PreKeyTryFromArgs preKeyTryFromStack preKeyResultAt
  psmRem2 psmRem3 psmRem4 psmRem8
  bytes32At exists_bytes32_of_vector32 pointsTo64_eq_extract_bytes8
  memRegion_8_bytes memRegion_8_bytes_mr_rhs memRegion_8_bytes_mr
  memRegion_40_words bv_sub_add_lit'
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv
  RustCliAllocBudget VmPreserved rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  intoBoxedSliceEvents TryCloneFromRefEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

private theorem cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    memRegion_split (sp - 96#64) 8 88 (by decide),
    memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

private theorem memRegion_40_identityKey_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗
      memRegion_8_bytes_mr_rhs (sp - 87#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 79#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 71#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 63#64) ∗
      memRegion (sp - 55#64) 7 := by
  rw [memRegion_split (sp - 88#64) 1 39 (by decide),
    memRegion_split (sp - 88#64 + 1#64) 8 31 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64) 8 23 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64) 8 15 (by decide),
    memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64 + 8#64) 8 7 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [memRegion_8_bytes_mr (sp - 87#64),
      memRegion_8_bytes_mr (sp - 79#64),
      memRegion_8_bytes_mr (sp - 71#64),
      memRegion_8_bytes_mr (sp - 63#64)]

private theorem memRegion_33_eq (sret : BitVec 64) :
    memRegion sret 33 =
      ∃∗ tag0 : BitVec 8, ∃∗ out32 : List (BitVec 8),
        ⌜out32.length = 32⌝ ∗ (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 1) (k := 32)
      (b' := sret + 1#64) rfl (by rfl) (by decide),
    memRegion_one,
    memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
  rw [sepExists_sepConj_left]
  apply congrArg sepExists; funext tag0
  rw [sepExists_sepConj_right]
  apply congrArg sepExists; funext out32
  rw [← sepConj_assoc, sepConj_comm (sret ↦₈ tag0), sepConj_assoc]

/-! ## `pkTryFromOk40PlacedSpec` (Block `211`) -/

def pkTryFromOk40PlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderWire.pkTryFromOk40PlacedSpec

theorem pkTryFromOk40_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (lsmpl.base 211)
      pkTryFromOk40PlacedSpec := by
  have hprog_eq :
      (blkPC_211).rebase (blkPl_211).base H =
        (CryptoVerification.LibsignalTripleRatchet.Getters.blkPC_211).rebase
          (CryptoVerification.LibsignalTripleRatchet.Getters.blkPl_211).base H :=
    (IsLsBlockProg.eq_blockProgram (i := 211) (H := H)).trans
      (IsLsBlockProg.eq_blockProgram (i := 211) (H := H)).symm
  rw [hprog_eq]
  refine subroutine_ok_map
    (LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.pkTryFrom_placed_ok H) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40PlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.pkTryFromOk40PlacedSpec,
    lsLogOff, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.pkTryFromPlacedBudgetSpec,
      withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.pkTryFromPlacedBudgetSpec,
      withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, htr, hpost⟩
    simp only [pkTryFromOk40PlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderWire.pkTryFromOk40PlacedSpec,
      lsLogOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, htr, hpost⟩

/-! ## `deserializeOk33PlacedSpec` (Block `201`) -/

def deserializePlacedBudgetSpec [LibsignalPlacement] : Spec DeserGhost :=
  withVmPreserved CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec

set_option maxHeartbeats 800000 in
theorem deserializePlacedBudget_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializePlacedBudgetSpec := by
  simp only [deserializePlacedBudgetSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec]
  wp_init g s0
  obtain ⟨ptr, bs, pk, sret, tag0, out32⟩ := g
  dsimp only at *
  subst h_1 h_3
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h_5
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ :=
    exists_unpack64_of_length_32 (bs := out32) h
  apply sepWP_seg_ls_vm (Q := (blkPC_201).rebase (blkPl_201).base (hooksException H))
    blkLib_eq_201 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) h_5,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
    hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      h_2, decide_eq_true_eq] at hcs
    omega
  · wp_step
    wp_if hcbz9
    · wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
      have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm ⊢
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done
    · wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
      have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm ⊢
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done

def deserializeOk33PlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderWire.deserializeOk33PlacedSpec

theorem deserialize_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (lsmpl.base 201)
      deserializeOk33PlacedSpec := by
  refine subroutine_ok_map (deserializePlacedBudget_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeOk33PlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.deserializeOk33PlacedSpec,
    lsLogOff, memRegion_33_eq sret,
    sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc, satisfies_sepExists, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨tag0, out32, ⟨hx0, hx1, hx8, hlt, hdes⟩, hrest⟩
  have hrest' : s0.mem ⊨ ⌜out32.length = 32⌝ ∗
      ((ptr ↦ₛ bs) ∗ (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ R) := by
    convert hrest using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hrest'
  rcases hrest' with ⟨hlen32, hmem⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, fun sf hpost => ?_⟩
  · simp only [deserializePlacedBudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt, hdes, hlen32⟩, hmem⟩
  · simp only [deserializePlacedBudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, htr, hpost⟩
    simp only [deserializeOk33PlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderWire.deserializeOk33PlacedSpec,
      lsLogOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, htr, hpost⟩

/-! ## `identityKeyTryFromSliceOkPlacedSpec` (Block `116`) -/

def identityKeyTryFromSliceOkPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec

set_option maxHeartbeats 3200000 in
theorem identityKeyTryFromSlice_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_116).rebase (blkPl_116).base H)
      (blkPl_116).base
      (withLsCodeLoaded lsmpl identityKeyTryFromSliceOkPlacedSpec) := by
  simp only [withLsCodeLoaded, identityKeyTryFromSliceOkPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec]
  have hpk := ls_subroutine_ok_of_block (callerProg := (blkPC_116).rebase (blkPl_116).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFromOk40_placed_ok H))
  simp only [withLsCodeLoaded, pkTryFromOk40PlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.pkTryFromOk40PlacedSpec] at hpk
  wp_init x s0
  rcases x with ⟨p, bs, pk, outPtr⟩
  dsimp only at *
  subst h_2 h_4
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes⟩ := exists_bytes32_of_vector32 pk.bytes
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := lsmpl.base 211)
  apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
    blkLib_eq_116 (mid := lsmpl.base 211)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  have hvm_call : VmPreserved _ _ := ‹_›
  have hvm_after_call : VmPreserved s0 _ := hvm1.trans hvm_call
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_pre s0.sp,
      memRegion_40_identityKey_post s0.sp,
      memRegion_8_bytes_mr (s0.sp - 48#64),
      memRegion_8_bytes_mr (s0.sp - 40#64),
      memRegion_8_bytes_mr (s0.sp - 8#64)]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
    blkLib_eq_116 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
  have hvm2 : VmPreserved _ _ := hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
  clear hvm1 hvm_call hvm_after_call hvm2
  wp_done

/-! ## Allocator Event Envelopes and Contracts for Block `111` -/

/-- Exact allocator event list of the 4 `bytes::merge` field decodes (`bk`, `ik`, `inner`,
`kyber`) in `PreKeySignalMessage::try_from`'s protobuf decode loop on `x : PreKeyTryFromArgs`. -/
def preKeyLoopEvents (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.bkBytes ++ psmRem2 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.ikBytes ++ psmRem3 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64
      (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner ++ psmRem4 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64
      (encodeVarint 1569#64 ++ x.kyberBytes ++ psmRem8 x)

def PreKeyLoopEnv (x : PreKeyTryFromArgs) (evs : List AllocEvent) : Prop :=
  evs = preKeyLoopEvents x

/-- Allocator event envelope of Segment 2 (`<Vec<u8>>::into_boxed_slice` on `kyberBytes` with
some `1569 ≤ cap.toNat < 2 ^ 63`). -/
def PreKeySeg2Env (x : PreKeyTryFromArgs) (evs : List AllocEvent) : Prop :=
  ∃ cap : BitVec 64, 1569 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
    evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, x.kyberBytes⟩

/-- Allocator event envelope of Segment 4's `.ok` branch (`try_clone_from_ref_in` on `x.bytes`
followed by cleanup deallocations). -/
def PreKeySeg4OkEnv (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  SeqEnv (TryCloneFromRefEnv ⟨x.ptr, x.bytes⟩) FreeOnlyEvs

/-- Allocator event envelope of Segment 4 (`.error` cleanup `FreeOnlyEvs`, or `.ok` clone +
cleanup `PreKeySeg4OkEnv x`). -/
def PreKeySeg4Env (x : PreKeyTryFromArgs) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ PreKeySeg4OkEnv x evs

def FromSeg3Env (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  SeqEnv (sigEnv x.inner) (PreKeySeg4Env x)

def FromSeg2Env (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  SeqEnv (PreKeySeg2Env x) (FromSeg3Env sigEnv x)

def PreKeyPostEnv (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs (FromSeg2Env sigEnv x)

/-- Full allocator event envelope of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`,
parameterized by the inner `SignalMessage::try_from` callee envelope `sigEnv`. -/
def PreKeyTryFromEnv (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (x : PreKeyTryFromArgs) : List AllocEvent → Prop :=
  SeqEnv (PreKeyLoopEnv x) (PreKeyPostEnv sigEnv x)

/-- Parametric-envelope raw budget contract of `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`
(Block `111`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def preKeyTryFromPlacedRawEnvSpec [LibsignalPlacement]
    (Env : PreKeyTryFromArgs → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PreKeyTryFromArgs × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ptr ∧
      (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧
      s.readReg64 .x8 = x.sret ∧
      FitsEnv M lim st (Env x)⌝ ∗
    (x.ptr ↦ₛ x.bytes) ∗
    memRegion x.sret 248 ∗
    lsLogOff ∗
    stackAt s.sp preKeyTryFromStack ∗
    A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      preKeyResultAt A.repAlloc x.sret x ∗
      (x.ptr ↦ₛ x.bytes) ∗
      lsLogOff ∗
      stackAt s0.sp preKeyTryFromStack ∗
      A.pool lim (M.stepEvents evs st) sf

def preKeyTryFromPlacedEnvSpec [LibsignalPlacement]
    (Env : PreKeyTryFromArgs → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PreKeyTryFromArgs × M.σ) :=
  withLsCodeLoaded lsmpl (preKeyTryFromPlacedRawEnvSpec Env M A lim)

abbrev preKeyTryFromPlacedRawSpec [LibsignalPlacement]
    (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PreKeyTryFromArgs × M.σ) :=
  preKeyTryFromPlacedRawEnvSpec (PreKeyTryFromEnv sigEnv) M A lim

abbrev preKeyTryFromPlacedSpec [LibsignalPlacement]
    (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PreKeyTryFromArgs × M.σ) :=
  withLsCodeLoaded lsmpl (preKeyTryFromPlacedRawSpec sigEnv M A lim)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
