/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# Budget-Threaded Helpers and Base Contracts for `KeyPairCallees`

Provides stack/memory framing bridges, `VmPreserved` curve key-pair contracts (Blocks `209`, `112`,
`67`), `privKeySerdeSerialize_placed_ok` (Block `107`), ML-KEM key-pair contracts (Blocks `70`,
`113`), and budget-threaded tail-call `__rust_dealloc` contracts (`48`-B and `64`-B frames).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl withLsCodeLoaded
   blkPC_67 blkPl_67 blkLib_eq_67
   blkPC_70 blkPl_70 blkLib_eq_70
   blkPC_107 blkPl_107
   blkPC_112 blkPl_112 blkLib_eq_112
   blkPC_113 blkPl_113
   blkPC_205 blkPl_205
   blkPC_208 blkPl_208
   blkPC_209 blkPl_209 blkLib_eq_209
   lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsMemcpySym
   ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain ls_subroutine_ok_of_block
   subroutine_ok_withLsCodeLoaded_of_plain lsρ)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecHeader vecU8 vecU8At vecU8Buf vecU8At_eq_header_sep_buf)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack publicKeySerializeStack sessionShimSpec sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply (stackAt_sub_split)
open CryptoVerification.E2E.Pqxdh.ResponderStore
  (bv_sub_add_lit' stackAt_split_top bytes32At exists_bytes32_of_length_32
   pointsTo64_eq_extract_bytes8 memRegion_65_cells
   cells_8_sub176 memRegion_8_bytes memRegion_65_bytes8 cells_14_curveKeyPairSerde
   cells_8_sub176_mr memRegion_8_bytes_mr_rhs cells_14_curveKeyPairSerde_mr
   curveKeyPairFromPubPrivOkSpec curveKeyPairSerdeOkSpec preKeyRecordKeyPairOkSpec
   zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
   zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
   clamp_lo_byte_norm clamp_lo_byte_norm'
   clamp_hi_byte_norm clamp_hi_byte_norm' clamp_hi_byte_norm'' clamp_hi_bfm_norm
   bv64_mask_low32_orr_zext32 bv64_mask_high32_orr_lsl32 bv64_mask_low16_orr_zext16)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   AllocCallPreserved PoolPreserved VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec publicKeySerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
  (shimSpecWithStack shimWithStack_of_noAllocShim)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (privSerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget
  (privSerialize_placed_ok)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv16_setWidth_8
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv8_setWidth_8
  zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  clamp_lo_byte_norm clamp_lo_byte_norm'
  clamp_hi_byte_norm clamp_hi_byte_norm' clamp_hi_byte_norm'' clamp_hi_bfm_norm
  bv64_mask_low32_orr_zext32 bv64_mask_high32_orr_lsl32 bv64_mask_low16_orr_zext16

/-! ## Stack, Memory, and Hook-Bridge Helpers -/

theorem pointsToBytes_cons_fold (a : BitVec 64) (b0 : BitVec 8) (bs : List (BitVec 8)) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ bs)) ⊢ (a ↦ₛ (b0 :: bs)) :=
  Entails.of_eq (pointsToBytes_cons a b0 bs).symm

theorem stackAt_kemKeyPairFromPubPriv (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

private theorem stackAt_add_48 (sp : BitVec 64) :
    stackAt sp (allocHookStack + 48) =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  simpa using ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

private theorem stackAt_add_48_comm (sp : BitVec 64) :
    stackAt sp (allocHookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 allocHookStack) 48 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hsplit :=
    memRegion_split (sp - BitVec.ofNat 64 (48 + allocHookStack)) 48 allocHookStack (by decide)
  have h0 : allocHookStack + 48 = 48 + allocHookStack := rfl
  have h1 : sp - BitVec.ofNat 64 (48 + allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack - 48#64 := by bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + allocHookStack) + 48#64 =
      sp - BitVec.ofNat 64 allocHookStack := by bv_lin
  rw [h0, hsplit, h2, h1]

private theorem stackAt_add_64 (sp : BitVec 64) :
    stackAt sp (allocHookStack + 64) =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  simpa using ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)

private theorem stackAt_add_64_comm (sp : BitVec 64) :
    stackAt sp (allocHookStack + 64) =
      stackAt (sp - BitVec.ofNat 64 allocHookStack) 64 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hsplit :=
    memRegion_split (sp - BitVec.ofNat 64 (64 + allocHookStack)) 64 allocHookStack (by decide)
  have h0 : allocHookStack + 64 = 64 + allocHookStack := rfl
  have h1 : sp - BitVec.ofNat 64 (64 + allocHookStack) =
      sp - BitVec.ofNat 64 allocHookStack - 64#64 := by bv_lin
  have h2 : sp - BitVec.ofNat 64 (64 + allocHookStack) + 64#64 =
      sp - BitVec.ofNat 64 allocHookStack := by bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists_single _ v5)))))

private theorem pointsTo64_8_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5) ∗
      ((base + 48#64) ↦₆₄ v6) ∗ ((base + 56#64) ↦₆₄ v7)) ⊢ cells base 8 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists _ v5
              (pointsTo64_entails_exists _ v6
                (pointsTo64_entails_exists_single _ v7)))))))

theorem stackAt_publicKeySerialize_sub48 (sp : BitVec 64) :
    memRegion (sp - 4176#64) 32 ∗ stackAt (sp - 48#64) allocHookStack =
      stackAt (sp - 48#64) publicKeySerializeStack := by
  unfold stackAt publicKeySerializeStack allocHookStack
  have hsplit := memRegion_split (sp - 4176#64) 32 4096 (by decide)
  have h1 : sp - 48#64 - BitVec.ofNat 64 (32 + 4096) = sp - 4176#64 := by bv_lin
  have h2 : sp - 4176#64 + 32#64 = sp - 48#64 - 4096#64 := by bv_lin
  rw [h1, hsplit, h2]

theorem stackAt_publicKeySerialize_sub48_assoc (sp : BitVec 64) (R : SepProp) :
    memRegion (sp - 4176#64) 32 ∗ (stackAt (sp - 48#64) allocHookStack ∗ R) =
      stackAt (sp - 48#64) publicKeySerializeStack ∗ R := by
  rw [← sepConj_assoc, stackAt_publicKeySerialize_sub48]

theorem memRegion_1569_cons (a : BitVec 64) :
    memRegion a 1569 = (∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 1568) := by
  rw [memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one, sepExists_sepConj_left]

theorem memRegion_3169_cons (a : BitVec 64) :
    memRegion a 3169 = (∃∗ b0 : BitVec 8, (a ↦₈ b0) ∗ memRegion (a + 1#64) 3168) := by
  rw [memRegion_split a 1 3168 (by decide), ProofLib.memRegion_one, sepExists_sepConj_left]

theorem stackAt_112_ext_to (sp : BitVec 64) (k : Nat) (hk : k ≤ extHookStack := by decide) :
    stackAt (sp - 112#64) extHookStack ⊢
      memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt (sp - 112#64) k := by
  rw [stackAt_sub_split (sp - 112#64) extHookStack k hk (by decide)]
  have heq : sp - 112#64 - BitVec.ofNat 64 extHookStack = sp - 16496#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq]
  exact Entails.refl _

theorem stackAt_112_to_ext (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hsp : sp' = sp - 112#64) (hk : k ≤ extHookStack := by decide) :
    (memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt sp' k) ⊢
      stackAt (sp - 112#64) extHookStack := by
  subst hsp
  have h := (stackAt_sub_split (sp - 112#64) extHookStack k hk (by decide)).symm
  have heq : sp - 112#64 - BitVec.ofNat 64 extHookStack = sp - 16496#64 := by
    simp only [extHookStack]; bv_omega
  rw [heq] at h
  exact Entails.of_eq h

theorem SepWP_fold_stack_112_to_ext {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (sp : BitVec 64) {sp' : BitVec 64} (k : Nat)
    (hk : k ≤ extHookStack)
    (hf : P = (memRegion (sp - 16496#64) (extHookStack - k) ∗ stackAt sp' k) ∗ F)
    (hsp : sp' = sp - 112#64)
    (h : SepWP prog ret s (stackAt (sp - 112#64) extHookStack ∗ F) Q) :
    SepWP prog ret s P Q :=
  SepWP.fold (stackAt_112_to_ext sp k hsp hk) hf h

theorem stack_24_to_memRegion_104 (sp v0 v1 v2 : BitVec 64) :
    (((sp - 104#64) ↦₆₄ v0) ∗ ((sp - 96#64) ↦₆₄ v1) ∗ ((sp - 88#64) ↦₆₄ v2)) ⊢
      memRegion (sp - 104#64) 24 := by
  rw [memRegion_split (sp - 104#64) 8 16 (by decide),
      memRegion_split (sp - 104#64 + 8#64) 8 8 (by decide)]
  have h1 : sp - 104#64 + 8#64 = sp - 96#64 := by bv_omega
  have h2 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  rw [h1, h2]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem vecU8At_priv_expose_104 (A : RustAlloc) (sp cap ptr : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    vecU8At A (sp - 104#64) cap ptr k.toList ⊢
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
      ((sp - 104#64) ↦₆₄ cap) ∗ ((sp - 96#64) ↦₆₄ ptr) ∗ ((sp - 88#64) ↦₆₄ 32#64) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have hlen : k.toList.length = 32 := k.toList_length
  have h1 : sp - 104#64 + 8#64 = sp - 96#64 := by bv_omega
  have h2 : sp - 104#64 + 16#64 = sp - 88#64 := by bv_omega
  rw [hlen, h1, h2]
  simp only [BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hptr⟩
  have hc0 : cap ≠ 0#64 := by intro h; subst h; simp at hle
  have hc0_beq : (cap == 0#64) = false := beq_false_of_ne hc0
  apply Entails.pure_right ⟨hle, hlt, hc0_beq, hptr⟩
  rw [ite_eq_right_iff.mpr (fun h => (hc0 h).elim)]
  exact Entails.refl _

theorem vecU8_priv_expose_104 (A : RustAlloc) (sp : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    vecU8 A (sp - 104#64) k.toList ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ (cap == 0#64) = false ∧ ptr ≠ 0⌝ ∗
        ((sp - 104#64) ↦₆₄ cap) ∗ ((sp - 96#64) ↦₆₄ ptr) ∗ ((sp - 88#64) ↦₆₄ 32#64) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ k.toList) ∗ memRegion (ptr + 32#64) (cap.toNat - 32) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (vecU8At_priv_expose_104 A sp cap ptr k))

theorem sepWP_pure_focus {prog : Program} {tgt : BitVec 64} {s : State}
    {P B : SepProp} {φ : Prop} {Q : State → SepProp → Prop}
    (hf : P = ⌜φ⌝ ∗ B) (h : φ → SepWP prog tgt s B Q) :
    SepWP prog tgt s P Q :=
  hf ▸ SepWP.pure_elim h

theorem subroutine_ok_shimAllocHook_of_sessionShimBudget {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionShimBudgetSpec) :
    subroutine_ok prog addr (shimSpecWithStack allocHookStack) := by
  refine shimWithStack_of_noAllocShim allocHookStack ?_
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _hL => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [pure_sepConj_pure] at hpost
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun ⟨hvm, htr⟩ => ⟨htr, hvm⟩)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem public_key_serialize_placed_ok_of_sessionShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpec M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (subroutine_ok_shimAllocHook_of_sessionShimBudget (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

/-! ## `VmPreserved` Curve `KeyPair` Contracts (Blocks `209`, `112`, `67`) -/

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

def curveKeyPairFromPubPrivBudgetSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved curveKeyPairFromPubPrivOkSpec

set_option maxHeartbeats 1200000 in
theorem curveKeyPairFromPubPriv_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_209).rebase (blkPl_209).base H) (blkPl_209).base
      curveKeyPairFromPubPrivBudgetSpec := by
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only [curveKeyPairFromPubPrivOkSpec] at *
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub] at *
  by_vm_steps (
    wp_pull_exists
    refine SepWP.pure_elim ?_
    rintro ⟨rfl, hx1, rfl, hx3, rfl, hpk_len, hsk_len⟩
    obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
      pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
      hpk, _⟩ := exists_bytes32_of_length_32 hpk_len
    obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
      sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
      hsk, hsk_clamp⟩ := exists_bytes32_of_length_32 hsk_len
    rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
      hsk (s0.readReg64 (.gpr 2#5)),
      hpk (s0.readReg64 (.gpr 8#5) + 1#64),
      hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
      pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
    dsimp only [bytes32At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    wp_done
  )

attribute [local irreducible] VmPreserved

def curveKeyPairSerdeBudgetSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved curveKeyPairSerdeOkSpec

set_option maxHeartbeats 1200000 in
theorem curveKeyPairSerde_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_112).rebase (blkPl_112).base H) (blkPl_112).base
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec) := by
  unfold curveKeyPairSerdeBudgetSpec withVmPreserved curveKeyPairSerdeOkSpec
  have hinner := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_112).rebase (blkPl_112).base H) (entry := lsmpl.base 209)
    (curveKeyPairFromPubPriv_placed_ok H)
  simp only [withLsCl, curveKeyPairFromPubPrivBudgetSpec, withVmPreserved,
    curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  wp_init x s0
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_4 h_6
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_7
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h_1
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) h (mid := lsmpl.base 209)
  apply sepWP_seg_ls_vm (Q := (blkPC_112).rebase (blkPl_112).base (hooksException H))
    blkLib_eq_112 (mid := lsmpl.base 209)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
  wp_call hinner (s0.readReg64 (.gpr 0#5), pk, s0.readReg64 (.gpr 2#5), sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_112).rebase (blkPl_112).base (hooksException H))
    blkLib_eq_112 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm_f : VmPreserved s0 _ :=
    (hvm1.trans (by assumption)).trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  simp only [wp_norm, arm64_norm] at hvm_f
  wp_done

def preKeyRecordKeyPairBudgetSpec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved preKeyRecordKeyPairOkSpec

set_option maxHeartbeats 1200000 in
theorem preKeyRecordKeyPair_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_67).rebase (blkPl_67).base H) (blkPl_67).base
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec) := by
  unfold preKeyRecordKeyPairBudgetSpec withVmPreserved preKeyRecordKeyPairOkSpec
  have hinner := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_67).rebase (blkPl_67).base H) (entry := lsmpl.base 209)
    (curveKeyPairFromPubPriv_placed_ok H)
  simp only [withLsCl, curveKeyPairFromPubPrivBudgetSpec, withVmPreserved,
    curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  wp_init x s0
  obtain ⟨recPtr, pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_3
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_4
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h_1
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_pull_exists
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) h (mid := lsmpl.base 209)
  apply sepWP_seg_ls_vm (Q := (blkPC_67).rebase (blkPl_67).base (hooksException H))
    blkLib_eq_67 (mid := lsmpl.base 209)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
  wp_call hinner (pubPtr, pk, privPtr, sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seg_ls_vm (Q := (blkPC_67).rebase (blkPl_67).base (hooksException H))
    blkLib_eq_67 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm_f : VmPreserved s0 _ :=
    (hvm1.trans (by assumption)).trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  simp only [wp_norm, arm64_norm] at hvm_f
  wp_done

/-! ## `privKeySerdeSerialize_placed_ok` (Block `107`) -/

private theorem setPC_pool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (pc : BitVec 64) :
    A.pool lim st (s.setPC pc) = A.pool lim st s :=
  A.pool_of_vmPreserved (s0 := s) (sf := s.setPC pc)
    (by delta VmPreserved; cases s; exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩)

theorem privKeySerdeSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_107).rebase (blkPl_107).base H) (blkPl_107).base
      (withLsCodeLoaded lsmpl (privSerializeSpec M A lim)) := by
  have hinner := ls_subroutine_ok_of_block
    (callerProg := (blkPC_107).rebase (blkPl_107).base H)
    (entry := lsmpl.base 208)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (privSerialize_placed_ok hshim halloc))
  exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    rfl (by
      intro x s pc
      dsimp only [withLsCodeLoaded, privSerializeSpec,
        LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget.privSerializeSpecWithStack]
      rw [setPC_pool_eq A lim x.2.2.2 s pc]
      cases s; rfl)
    hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

/-! ## `kemKeyPairFromPubPriv_placed_ok` (Block `70`) and `kemKeyPairSerde_placed_ok` (Block `113`) -/

def kemKeyPairFromPubPrivEvents : List AllocEvent :=
  rustAllocEvents 1568 1 ++ rustAllocEvents 3168 1

def KemKeyPairFromPubPrivEnv (evs : List AllocEvent) : Prop :=
  evs = kemKeyPairFromPubPrivEvents

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

def kemKeyPairFromPubPrivOkSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st KemKeyPairFromPubPrivEnv⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    (CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec
      (A.atState lim (M.stepEvents kemKeyPairFromPubPrivEvents st) sf)).post x s0 sf

set_option maxHeartbeats 1200000 in

def kemKeyPairFromPubPrivOkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st KemKeyPairFromPubPrivEnv ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    (CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec
      (A.atState lim (M.stepEvents kemKeyPairFromPubPrivEvents st) sf)).post x s0 sf

set_option maxHeartbeats 1200000 in
theorem kemKeyPairFromPubPriv_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base H) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec M A lim) := by
  simp only [kemKeyPairFromPubPrivOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
    stackAt_kemKeyPairFromPubPriv, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  have hshim_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem hshim
  have halloc_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_of_mem hmemcpy
  dsimp only [sessionShimBudgetSpec, sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy_ok
  wp_init xst s0
  obtain ⟨⟨pubPtr, pk, privPtr, sk, outPtr⟩, st⟩ := xst
  dsimp only at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = pubPtr := by assumption
  have hx2_eq : s0.readReg64 .x2 = privPtr := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  subst hx0_eq hx2_eq hx8_eq
  have hfit_all : FitsEvents M lim st kemKeyPairFromPubPrivEvents :=
    ‹FitsEnv M lim st KemKeyPairFromPubPrivEnv› _ rfl
  rw [kemKeyPairFromPubPrivEvents, fitsEvents_append] at hfit_all
  rcases hfit_all with ⟨hfit1, hfit2⟩
  have hfe1 : FitsEvents M lim st [.alloc 1568] := by simpa [rustAllocEvents] using hfit1
  rcases hfe1 with ⟨⟨hwma1, henf1, hram1, hva1⟩, -⟩
  have hfe2 : FitsEvents M lim (M.stepEvents (rustAllocEvents 1568 1) st) [.alloc 3168] := by
    simpa [rustAllocEvents] using hfit2
  rcases hfe2 with ⟨⟨hwma2, henf2, hram2, hva2⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : RustLayoutOk 1568 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hlay2 : RustLayoutOk 3168 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hpk_len : pk.length = 1568 := by assumption
  have hsk_len : sk.length = 3168 := by assumption
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (1568, 1, st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hpk_len]
  wp_apply
  simp only [hpk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (3168, 1, M.stepEvents (rustAllocEvents 1568 1) st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hsk_len]
  wp_apply
  simp only [hsk_len] at *
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  simp only [kemKeyPairFromPubPrivEvents, AllocCostModel.stepEvents_append]
  wp_done

theorem kemKeyPairSerde_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok ((blkPC_113).rebase (blkPl_113).base H) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)) := by
  have hinner := ls_subroutine_ok_of_block
    (callerProg := (blkPC_113).rebase (blkPl_113).base H)
    (entry := lsmpl.base 70)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (kemKeyPairFromPubPriv_placed_ok hshim halloc hmemcpy))
  exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm])
    rfl (by
      intro x s pc
      dsimp only [withLsCodeLoaded, kemKeyPairFromPubPrivOkSpec,
        CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
        RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
      rw [setPC_pool_eq A lim x.2 s pc]
      cases s; rfl)
    hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

/-! ## Budget Tail-Call `__rust_dealloc` Contracts -/

abbrev DeallocTail48BudgetGhost (σ : Type) :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def rustDeallocTail48BudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeallocTail48BudgetGhost M.σ) where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) allocHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun (_, bs, align, _, _, _, _, _, _, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6

def rustDeallocTail48BudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeallocTail48BudgetGhost M.σ) where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) allocHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun (_, bs, align, _, _, _, _, _, _, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6

theorem dealloc_tail48_of_dealloc [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hdealloc : subroutine_ok prog addr (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog addr (rustDeallocTail48BudgetSpec M A lim) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5, st⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (p, bs.length, align, st) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) := by
    unfold rustDeallocTail48BudgetSpec at hpre
    unfold rustCliDeallocBudgetSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48, stackAt_add_48_comm] at h1
    exact (by sep_ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R))) ▸ h1
  refine (hdealloc.to_outcome (p, bs.length, align, st)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail48BudgetSpec
    unfold rustCliDeallocBudgetSpec at hpost
    dsimp only [AllocCallPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨⟨_, htr⟩, _⟩, hpost_rest⟩
    rw [← stackAt_add_48, stackAt_add_48_comm]
    have hpost' : sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R) := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htr.1, by simpa [sepConj_assoc] using hpost_rest⟩
    exact (by sep_ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 48 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost'
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

abbrev DeallocTail64BudgetGhost (σ : Type) :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × σ

def rustDeallocTail64BudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeallocTail64BudgetGhost M.σ) where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 64#64) allocHookStack ∗
      ((s.sp - 64#64) ↦₆₄ v0) ∗ ((s.sp - 56#64) ↦₆₄ v1) ∗
      ((s.sp - 48#64) ↦₆₄ v2) ∗ ((s.sp - 40#64) ↦₆₄ v3) ∗
      ((s.sp - 32#64) ↦₆₄ v4) ∗ ((s.sp - 24#64) ↦₆₄ v5) ∗
      ((s.sp - 16#64) ↦₆₄ v6) ∗ ((s.sp - 8#64) ↦₆₄ v7)
  post := fun (_, bs, align, _, _, _, _, _, _, _, _, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
      stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8

def rustDeallocTail64BudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DeallocTail64BudgetGhost M.σ) where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 64#64) allocHookStack ∗
      ((s.sp - 64#64) ↦₆₄ v0) ∗ ((s.sp - 56#64) ↦₆₄ v1) ∗
      ((s.sp - 48#64) ↦₆₄ v2) ∗ ((s.sp - 40#64) ↦₆₄ v3) ∗
      ((s.sp - 32#64) ↦₆₄ v4) ∗ ((s.sp - 24#64) ↦₆₄ v5) ∗
      ((s.sp - 16#64) ↦₆₄ v6) ∗ ((s.sp - 8#64) ↦₆₄ v7)
  post := fun (_, bs, align, _, _, _, _, _, _, _, _, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
      stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8

theorem dealloc_tail64_of_dealloc [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hdealloc : subroutine_ok prog addr (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog addr (rustDeallocTail64BudgetSpec M A lim) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5, v6, v7, st⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 64#64) ↦₆₄ v0) ∗ ((s0.sp - 56#64) ↦₆₄ v1) ∗
        ((s0.sp - 48#64) ↦₆₄ v2) ∗ ((s0.sp - 40#64) ↦₆₄ v3) ∗
        ((s0.sp - 32#64) ↦₆₄ v4) ∗ ((s0.sp - 24#64) ↦₆₄ v5) ∗
        ((s0.sp - 16#64) ↦₆₄ v6) ∗ ((s0.sp - 8#64) ↦₆₄ v7)) ⊢ cells (s0.sp - 64#64) 8 := by
    have h := pointsTo64_8_entails_cells (s0.sp - 64#64) v0 v1 v2 v3 v4 v5 v6 v7
    have ha1 : s0.sp - 64#64 + 8#64 = s0.sp - 56#64 := by bv_lin
    have ha2 : s0.sp - 64#64 + 16#64 = s0.sp - 48#64 := by bv_lin
    have ha3 : s0.sp - 64#64 + 24#64 = s0.sp - 40#64 := by bv_lin
    have ha4 : s0.sp - 64#64 + 32#64 = s0.sp - 32#64 := by bv_lin
    have ha5 : s0.sp - 64#64 + 40#64 = s0.sp - 24#64 := by bv_lin
    have ha6 : s0.sp - 64#64 + 48#64 = s0.sp - 16#64 := by bv_lin
    have ha7 : s0.sp - 64#64 + 56#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5, ha6, ha7] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre2 : s0.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (p, bs.length, align, st) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) := by
    unfold rustDeallocTail64BudgetSpec at hpre
    unfold rustCliDeallocBudgetSpec
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 64#64) allocHookStack ∗ cells (s0.sp - 64#64) 8)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_64, stackAt_add_64_comm] at h1
    exact (by sep_ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ stackAt s0.sp allocHookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R))) ▸ h1
  refine (hdealloc.to_outcome (p, bs.length, align, st)
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) s0 hpc hrun hpre2 hsp).mono_outcome
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTail64BudgetSpec
    unfold rustCliDeallocBudgetSpec at hpost
    dsimp only [AllocCallPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨⟨_, htr⟩, _⟩, hpost_rest⟩
    rw [← stackAt_add_64, stackAt_add_64_comm]
    have hpost' : sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R) := by
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htr.1, by simpa [sepConj_assoc] using hpost_rest⟩
    exact (by sep_ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        stackAt s0.sp allocHookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗
        A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
        (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) 64 ∗
          stackAt s0.sp allocHookStack)) ∗ R)) ▸ hpost'
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)
  · exact False.elim (not_satisfies_false_sepConj hpost)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
