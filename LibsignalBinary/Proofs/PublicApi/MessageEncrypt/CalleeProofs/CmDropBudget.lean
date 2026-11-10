/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDrop
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# Budget-Threaded `drop_glue::<CiphertextMessage>`

Proves `subroutine_ok (lsProg_135 H) (blkPl_135).base (CalleesBudget.cmDropSpec M A lim)` under
`[LibsignalPlacement]` (`FreeOnlyEvs`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDropBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (cmDropSpec)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (KyberPayload PreKeySignalMessage CiphertextMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustDeallocSym ls_hook_ok_of_mem lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At vecU8At_entails_dealloc)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost boxU8At optBoxU8At signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (SepWP.instantiate_post_exists)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
  (vecPinDealloc header_cells_entails_memRegion_24)
open CryptoVerification.LibsignalPublicApiRepr
  (PreKeyMsgGhost ctSignalTag optU32At optKyberAt preKeyMsgAt apiEncResultAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_135 blkPC_135 blkPl_135 blkLib_eq_135)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] conditionHolds_mi_subsPState64 conditionHolds_eq_subsPState64

/-! ## Stack, Event, and Deallocation Helpers -/

private abbrev cmActiveStack : Nat := allocHookStack + 32

private theorem stackAt_cmDrop_outer (sp : BitVec 64) :
    stackAt sp (allocHookStack + 0x40) =
      memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack :=
  stackAt_split_bottom sp cmActiveStack 32 (by decide)

private theorem stackAt_cmActive_split (sp : BitVec 64) :
    stackAt sp cmActiveStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem tail_stack_32_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom sp allocHookStack 32 (by decide),
      ← stackAt_cmActive_split sp]

private theorem cells4_entails_stack_bottom (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_32_from_bottom sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem stack_restore_32_cm (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp cmActiveStack := by
  rw [stackAt_cmActive_split sp, ← tail_stack_32_from_bottom sp]
  exact cells4_entails_stack_bottom sp fp lr x20 x19

@[reducible]
private def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s.sp = fsp ∧
  s.trace = s0.trace

private def optBoxDealloc (A : RustAlloc) (p0 l0 : BitVec 64) : SepProp :=
  if (p0 == 0#64) = true then emp
  else vecPinDealloc A ⟨l0, p0⟩

@[reducible]
private def vecPinEvs (cap : BitVec 64) : List AllocEvent :=
  if (cap == 0#64) = true then [] else rustDeallocEvents cap.toNat 1

@[reducible]
private def optBoxEvs (p0 l0 : BitVec 64) : List AllocEvent :=
  if (p0 == 0#64) = true then [] else vecPinEvs l0

private theorem freeOnlyEvs_vecPinEvs (cap : BitVec 64) : FreeOnlyEvs (vecPinEvs cap) := by
  unfold vecPinEvs rustDeallocEvents
  by_cases h : (cap == 0#64) = true <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

private theorem freeOnlyEvs_optBoxEvs (p0 l0 : BitVec 64) : FreeOnlyEvs (optBoxEvs p0 l0) := by
  unfold optBoxEvs
  by_cases h : (p0 == 0#64) = true <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
  · exact FreeOnlyEvs.nil
  · exact freeOnlyEvs_vecPinEvs l0

private theorem apiEncResultAt_ok_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (p : BitVec 64) (m : CiphertextMessage) :
    apiEncResultAt (A.atState lim st s) p (.ok m) = apiEncResultAt A.repAlloc p (.ok m) := by
  cases m <;> rfl

private theorem vecU8At_entails_pin_dealloc_bound (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap, _⟩
  refine Entails.pure_right hcap ?_
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

private theorem boxU8At_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢
      ∃∗ len : BitVec 64,
        (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗
        vecPinDealloc A ⟨len, ptr⟩ := by
  have hpure : boxU8At A a ptr bs =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
      ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))) := by
    unfold boxU8At; sep_ac_rfl
  rw [hpure]
  apply Entails.pure_left; rintro ⟨_, hlen⟩
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_
  unfold vecPinDealloc
  have h64 : bs.length < 2 ^ 64 := by omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  have hbeq : ((BitVec.ofNat 64 bs.length == 0#64) = true) ↔ bs = [] := by
    rw [beq_iff_eq, ← List.length_eq_zero_iff]
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      simpa [htoNat] using ht
    · intro h; simp [h]
  simp only [hbeq, htoNat]
  by_cases hbs : bs = []
  · simp only [hbs, ↓reduceIte]
    exact Entails.refl _
  · simp only [hbs, ↓reduceIte]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (pointsToBytes_entails_memRegion ptr bs)))

private theorem optBoxU8At_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optBoxU8At A a ptr opt ⊢
      ∃∗ p0 : BitVec 64, ∃∗ l0 : BitVec 64,
        (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ l0) ∗ optBoxDealloc A p0 l0 := by
  cases opt with
  | none =>
    unfold optBoxU8At optBoxDealloc
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro l0
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right l0 ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    unfold optBoxU8At optBoxDealloc
    have hptr : boxU8At A a ptr bs ⊢ ⌜ptr ≠ 0#64⌝ ∗ boxU8At A a ptr bs := by
      have hpure : boxU8At A a ptr bs =
          ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
          ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))) := by
        unfold boxU8At; sep_ac_rfl
      rw [hpure]
      apply Entails.pure_left; intro h
      exact Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))
    refine Entails.trans hptr ?_
    apply Entails.pure_left; intro hne
    refine Entails.trans (boxU8At_entails_dealloc A a ptr bs) ?_
    apply Entails.sepExists_elim; intro l0
    refine Entails.sepExists_right ptr (Entails.sepExists_right l0 ?_)
    have hbeq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact Entails.refl _

private theorem u32_pad4_entails_memRegion_8 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ∗ memRegion (a + 4#64) 4 ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 4) (b' := a + 4#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion a v)

private theorem optU32At_entails_memRegion_8 (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢ memRegion a 8 := by
  cases opt with
  | none =>
    unfold optU32At
    exact u32_pad4_entails_memRegion_8 a 0#32
  | some v =>
    unfold optU32At
    refine Entails.trans (sepConj_mono_right (pointsTo32_entails_memRegion (a + 4#64) v)) ?_
    exact u32_pad4_entails_memRegion_8 a 1#32

private theorem optKyberAt_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64)
    (kp : Option KyberPayload) :
    optKyberAt A a ptr kp ⊢
      ∃∗ p0 : BitVec 64, ∃∗ l0 : BitVec 64,
        (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ l0) ∗ memRegion (a + 16#64) 8 ∗ optBoxDealloc A p0 l0 := by
  have hred : optKyberAt A a ptr kp ⊢
      optBoxU8At A a ptr (kp.map (·.ciphertext)) ∗ memRegion (a + 16#64) 8 := by
    cases kp with
    | none =>
      dsimp only [optKyberAt, optBoxU8At, Option.map]
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8)
            (b' := a + 16#64) rfl (by bv_omega) (by decide),
          sepConj_assoc]
      exact Entails.refl _
    | some k =>
      dsimp only [optKyberAt, optBoxU8At, Option.map]
      have h8 : ((a + 16#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 20#64) 4 ⊢ memRegion (a + 16#64) 8 := by
        have h20 : (a + 16#64) + 4#64 = a + 20#64 := by bv_omega
        simpa [h20] using u32_pad4_entails_memRegion_8 (a + 16#64) k.preKeyId
      exact sepConj_mono_right h8
  refine Entails.trans hred ?_
  refine Entails.trans (sepConj_mono_left (optBoxU8At_entails_dealloc A a ptr (kp.map (·.ciphertext)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro l0
  refine Entails.sepExists_right p0 (Entails.sepExists_right l0 ?_)
  exact Entails.of_eq (by sep_ac_rfl)

private theorem u64x2_entails_memRegion_16 (a w1 w2 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ⊢ memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w1)
    (pointsTo64_entails_memRegion (a + 8#64) w2)

private theorem u32x2_u8_pad7_entails_memRegion_16 (a : BitVec 64) (v1 v2 : BitVec 32) (b : BitVec 8) :
    (a ↦₃₂ v1) ∗ ((a + 4#64) ↦₃₂ v2) ∗ ((a + 8#64) ↦₈ b) ∗ memRegion (a + 9#64) 7 ⊢
      memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 12) (b' := a + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 4) (k := 8) (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 7) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion a v1)
    (sepConj_mono (pointsTo32_entails_memRegion (a + 4#64) v2)
      (sepConj_mono_left
        (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) b) (IsBlock.memRegion (a + 8#64) 1) fun _ _ => trivial)))

private theorem vec32_entails_memRegion_32 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) ⊢ memRegion a 32 := by
  have h := pointsToBytes_entails_memRegion a v.toList
  rwa [List.Vector.toList_length] at h

@[reducible]
private def smHeadersAt (a : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) : SepProp :=
  (a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
  ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
  memRegion (a + 56#64) 32 ∗
  ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ∗
  memRegion (a + 104#64) 16

private theorem smHeadersAt_entails_memRegion_120 (a : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    smHeadersAt a g ctLen serLen addrP addrL ⊢ memRegion a 120 := by
  unfold smHeadersAt
  have h0 := header_cells_entails_memRegion_24 a g.pqCap g.pqPtr
  have h1 : ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ⊢ memRegion (a + 24#64) 16 := by
    have ha : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 24#64) g.ctPtr ctLen
  have h2 : ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ⊢ memRegion (a + 40#64) 16 := by
    have ha : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 40#64) g.serPtr serLen
  have h4 : ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ⊢ memRegion (a + 88#64) 16 := by
    have ha : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 88#64) addrP addrL
  have hgroup :
      ((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
        ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
        memRegion (a + 56#64) 32 ∗
        ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ∗
        memRegion (a + 104#64) 16) =
      (((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen)) ∗
       (((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen)) ∗
       memRegion (a + 56#64) 32 ∗
       (((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL)) ∗
       memRegion (a + 104#64) 16) := by sep_ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 96) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 16) (k := 80) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 16) (k := 64) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 32) (k := 32) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 16) (k := 16) (b' := a + 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right (sepConj_mono_left h4))))

private theorem signalMessageAt_entails_dealloc (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A g a m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
        smHeadersAt a g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
  unfold signalMessageAt
  apply Entails.pure_left; intro _
  have hpq := vecU8At_entails_pin_dealloc_bound A a ⟨g.pqCap, g.pqPtr⟩ m.pqRatchet
  have hct := boxU8At_entails_dealloc A (a + 24#64) g.ctPtr m.ciphertext
  have hser := boxU8At_entails_dealloc A (a + 40#64) g.serPtr m.serialized
  have hsrk := vec32_entails_memRegion_32 (a + 56#64) m.senderRatchetKey.bytes
  have haddr := optBoxU8At_entails_dealloc A (a + 88#64) g.addrPtr m.addresses
  have htail :
      ((a + 104#64) ↦₃₂ m.counter) ∗ ((a + 108#64) ↦₃₂ m.previousCounter) ∗
        ((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7 ⊢
      memRegion (a + 104#64) 16 := by
    have ha1 : (a + 104#64) + 4#64 = a + 108#64 := by bv_omega
    have ha2 : (a + 104#64) + 8#64 = a + 112#64 := by bv_omega
    have ha3 : (a + 104#64) + 9#64 = a + 113#64 := by bv_omega
    simpa [ha1, ha2, ha3] using u32x2_u8_pad7_entails_memRegion_16 (a + 104#64) m.counter m.previousCounter m.messageVersion
  refine Entails.trans (sepConj_mono hpq (sepConj_mono hct (sepConj_mono hser (sepConj_mono hsrk (sepConj_mono haddr htail))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro ctLen
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
  unfold smHeadersAt
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h48 : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
  have h96 : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
  rw [h32, h48, h96]
  exact Entails.of_eq (by sep_ac_rfl)

@[reducible]
private def sigHeadersAt (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) : SepProp :=
  (p ↦₆₄ ctSignalTag) ∗
  ((p + 8#64) ↦₆₄ g.pqCap) ∗ ((p + 16#64) ↦₆₄ g.pqPtr) ∗ memRegion (p + 24#64) 8 ∗
  ((p + 32#64) ↦₆₄ g.ctPtr) ∗ ((p + 40#64) ↦₆₄ ctLen) ∗
  ((p + 48#64) ↦₆₄ g.serPtr) ∗ ((p + 56#64) ↦₆₄ serLen) ∗
  memRegion (p + 64#64) 32 ∗
  ((p + 96#64) ↦₆₄ addrP) ∗ ((p + 104#64) ↦₆₄ addrL) ∗
  memRegion (p + 112#64) 16 ∗
  memRegion (p + 128#64) 120

private theorem sigHeadersAt_eq (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    (p ↦₆₄ ctSignalTag) ∗ smHeadersAt (p + 8#64) g ctLen serLen addrP addrL ∗
      memRegion (p + 128#64) 120 =
    sigHeadersAt p g ctLen serLen addrP addrL := by
  unfold smHeadersAt sigHeadersAt
  have h16 : (p + 8#64) + 8#64 = p + 16#64 := by bv_omega
  have h24 : (p + 8#64) + 16#64 = p + 24#64 := by bv_omega
  have h32 : (p + 8#64) + 24#64 = p + 32#64 := by bv_omega
  have h40 : (p + 8#64) + 32#64 = p + 40#64 := by bv_omega
  have h48 : (p + 8#64) + 40#64 = p + 48#64 := by bv_omega
  have h56 : (p + 8#64) + 48#64 = p + 56#64 := by bv_omega
  have h64 : (p + 8#64) + 56#64 = p + 64#64 := by bv_omega
  have h96 : (p + 8#64) + 88#64 = p + 96#64 := by bv_omega
  have h104 : (p + 8#64) + 96#64 = p + 104#64 := by bv_omega
  have h112 : (p + 8#64) + 104#64 = p + 112#64 := by bv_omega
  rw [h16, h24, h32, h40, h48, h56, h64, h96, h104, h112]
  sep_ac_rfl

private theorem sigHeadersAt_entails_memRegion_248 (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    sigHeadersAt p g ctLen serLen addrP addrL ⊢ memRegion p 248 := by
  rw [← sigHeadersAt_eq p g ctLen serLen addrP addrL,
      ProofLib.memRegion_split' (b := p) (n := 8) (k := 240) (b' := p + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 120) (k := 120) (b' := p + 128#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p ctSignalTag)
    (sepConj_mono_left (smHeadersAt_entails_memRegion_120 (p + 8#64) g ctLen serLen addrP addrL))

private theorem apiEncResultAt_signal_entails_dealloc (A : RustAlloc) (p : BitVec 64)
    (m : SignalMessage) :
    apiEncResultAt A p (.ok (.signalMessage m)) ⊢
      ∃∗ g : SignalMessageGhost, ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64,
      ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        sigHeadersAt p g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
  dsimp only [apiEncResultAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  have hsm : signalMessageAt A g (p + 8#64) m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        smHeadersAt (p + 8#64) g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
    refine Entails.trans (signalMessageAt_entails_dealloc A g (p + 8#64) m) ?_
    apply Entails.sepExists_elim; intro ctLen
    apply Entails.sepExists_elim; intro serLen
    apply Entails.sepExists_elim; intro addrP
    apply Entails.sepExists_elim; intro addrL
    refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
      (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
    exact Entails.pure_left fun _ => Entails.refl _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsm)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ctLen
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
  rw [← sigHeadersAt_eq p g ctLen serLen addrP addrL]
  exact Entails.of_eq (by sep_ac_rfl)

@[reducible]
private def preKeyMsgHeadersAt (p : BitVec 64) (g : PreKeyMsgGhost)
    (ctLen serLen addrP addrL pserLen kyP kyL : BitVec 64) : SepProp :=
  smHeadersAt p g.msg ctLen serLen addrP addrL ∗
  memRegion (p + 120#64) 8 ∗
  ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ∗
  ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ∗
  memRegion (p + 160#64) 88

private theorem preKeyMsgHeadersAt_entails_memRegion_248 (p : BitVec 64) (g : PreKeyMsgGhost)
    (ctLen serLen addrP addrL pserLen kyP kyL : BitVec 64) :
    preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ⊢ memRegion p 248 := by
  unfold preKeyMsgHeadersAt
  have hsm := smHeadersAt_entails_memRegion_120 p g.msg ctLen serLen addrP addrL
  have hser : ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ⊢ memRegion (p + 128#64) 16 := by
    have ha : (p + 128#64) + 8#64 = p + 136#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (p + 128#64) g.serPtr pserLen
  have hky : ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ⊢ memRegion (p + 144#64) 16 := by
    have ha : (p + 144#64) + 8#64 = p + 152#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (p + 144#64) kyP kyL
  have hgroup :
      (smHeadersAt p g.msg ctLen serLen addrP addrL ∗
        memRegion (p + 120#64) 8 ∗
        ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ∗
        ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ∗
        memRegion (p + 160#64) 88) =
      (smHeadersAt p g.msg ctLen serLen addrP addrL ∗
        memRegion (p + 120#64) 8 ∗
        (((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen)) ∗
        (((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL)) ∗
        memRegion (p + 160#64) 88) := by sep_ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := p) (n := 120) (k := 128) (b' := p + 120#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := p + 120#64) (n := 8) (k := 120) (b' := p + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 128#64) (n := 16) (k := 104) (b' := p + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 144#64) (n := 16) (k := 88) (b' := p + 160#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono hsm (sepConj_mono_right (sepConj_mono hser (sepConj_mono_left hky)))

private theorem preKeyMsgAt_entails_dealloc (A : RustAlloc) (g : PreKeyMsgGhost)
    (p : BitVec 64) (m : PreKeySignalMessage) :
    preKeyMsgAt A g p m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
      ∃∗ pserLen : BitVec 64, ∃∗ kyP : BitVec 64, ∃∗ kyL : BitVec 64,
        ⌜g.msg.pqCap.toNat < 2 ^ 63⌝ ∗
        preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
        optBoxDealloc A kyP kyL ∗
        vecPinDealloc A ⟨ctLen, g.msg.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
        vecPinDealloc A ⟨pserLen, g.serPtr⟩ := by
  unfold preKeyMsgAt
  have hsm := signalMessageAt_entails_dealloc A g.msg p m.message
  have hpk := optU32At_entails_memRegion_8 (p + 120#64) m.preKeyId
  have hpser := boxU8At_entails_dealloc A (p + 128#64) g.serPtr m.serialized
  have hky := optKyberAt_entails_dealloc A (p + 144#64) g.kyberPtr m.kyberPayload
  have hbk := vec32_entails_memRegion_32 (p + 168#64) m.baseKey.bytes
  have hik := vec32_entails_memRegion_32 (p + 200#64) m.identityKey.publicKey.bytes
  have htail :
      ((p + 232#64) ↦₃₂ m.registrationId) ∗ ((p + 236#64) ↦₃₂ m.signedPreKeyId) ∗
        ((p + 240#64) ↦₈ m.messageVersion) ∗ memRegion (p + 241#64) 7 ⊢
      memRegion (p + 232#64) 16 := by
    have ha1 : (p + 232#64) + 4#64 = p + 236#64 := by bv_omega
    have ha2 : (p + 232#64) + 8#64 = p + 240#64 := by bv_omega
    have ha3 : (p + 232#64) + 9#64 = p + 241#64 := by bv_omega
    simpa [ha1, ha2, ha3] using u32x2_u8_pad7_entails_memRegion_16 (p + 232#64) m.registrationId m.signedPreKeyId m.messageVersion
  refine Entails.trans (sepConj_mono hsm (sepConj_mono hpk (sepConj_mono hpser (sepConj_mono hky (sepConj_mono hbk (sepConj_mono hik htail)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyP
  apply Entails.sepExists_elim; intro kyL
  apply Entails.sepExists_elim; intro pserLen
  apply Entails.sepExists_elim; intro ctLen
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL
      (Entails.sepExists_right pserLen (Entails.sepExists_right kyP (Entails.sepExists_right kyL ?_))))))
  unfold preKeyMsgHeadersAt
  have h136 : (p + 128#64) + 8#64 = p + 136#64 := by bv_omega
  have h152 : (p + 144#64) + 8#64 = p + 152#64 := by bv_omega
  have h160 : (p + 144#64) + 16#64 = p + 160#64 := by bv_omega
  have hm88 :
      memRegion (p + 160#64) 88 =
        memRegion (p + 160#64) 8 ∗ (memRegion (p + 168#64) 32 ∗ (memRegion (p + 200#64) 32 ∗ memRegion (p + 232#64) 16)) := by
    rw [ProofLib.memRegion_split' (b := p + 160#64) (n := 8) (k := 80) (b' := p + 168#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := p + 168#64) (n := 32) (k := 48) (b' := p + 200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := p + 200#64) (n := 32) (k := 16) (b' := p + 232#64) rfl (by bv_omega) (by decide)]
  rw [h136, h152, h160, hm88]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem cm_cap0_weaken {Hdr : SepProp} (p : BitVec 64)
    (hHdr : Hdr ⊢ memRegion p 248)
    (Pool : SepProp) (sp fp lr x20 x19 : BitVec 64) :
    Hdr ∗ Pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
      memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Pool ∗ (memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack) := by
  have hst := stack_restore_32_cm sp fp lr x20 x19
  have hgroup :
      (Hdr ∗ Pool ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
        memRegion (sp - 4160#64) 32) =
      (Hdr ∗ Pool ∗ memRegion (sp - 4160#64) 32 ∗
        (stackAt (sp - 32#64) allocHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hgroup]
  exact sepConj_mono hHdr (sepConj_mono_right (sepConj_mono_right hst))

private theorem cm_tail_dealloc_pre_weaken {Hdr : SepProp} (p : BitVec 64)
    (hHdr : Hdr ⊢ memRegion p 248)
    (Live Pool : SepProp) (sp fp lr x20 x19 : BitVec 64) :
    Hdr ∗ Live ∗ Pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
      memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Live ∗ Pool ∗
      memRegion (sp - 4128#64) 32 ∗ memRegion (sp - 4160#64) 32 ∗ stackAt sp allocHookStack := by
  have hst := cells4_entails_stack_bottom sp fp lr x20 x19
  have hgroup :
      (Hdr ∗ Live ∗ Pool ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
        memRegion (sp - 4160#64) 32) =
      (Hdr ∗ Live ∗ Pool ∗ memRegion (sp - 4160#64) 32 ∗
        (stackAt (sp - 32#64) allocHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono hHdr (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hst)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem cm_tail_dealloc_post (p : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion p 248 ∗
      memRegion (sp - 4128#64) 32 ∗ memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Pool ∗ (memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack) := by
  rw [stackAt_cmActive_split sp, ← tail_stack_32_from_bottom sp]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem seq_clean_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) oom)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post oom) :
    SepWP prog target s P post oom :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

private theorem SepWP.align_pre_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {oom : State → SepProp}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) oom) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) oom :=
  heq ▸ h

attribute [local semireducible] SepWP in
private theorem SepWP.pure_elim_left {prog : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWP prog target s P post oom) :
    SepWP prog target s (⌜φ⌝ ∗ P) post oom := by
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

private theorem msb_eq_false_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap.msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  omega

/-! ## Relocatable `[LibsignalPlacement]` Proof -/

attribute [local irreducible] FreeOnlyEvs

set_option maxHeartbeats 1600000 in
theorem cmDrop_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_135 H) (blkPl_135).base (cmDropSpec M A lim) := by
  simp only [cmDropSpec, CryptoVerification.LibsignalPublicApi.MessageEncrypt.cmDropSpec,
    stackAt_cmDrop_outer]
  have hdealloc : subroutine_ok (lsProg_135 H) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_of_mem hdealloc_sat
  dsimp only [rustCliDeallocBudgetSpec, AllocCallPreserved] at hdealloc
  wp_init x s0
  obtain ⟨p, m, st⟩ := x
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = p›
  let p := s0.readReg64 (Reg.gpr 0#5)
  rw [apiEncResultAt_ok_atState_eq A lim st s0 p m]
  simp only [RustCliAllocBudget.atState_pool]
  nth_rw 1 [stackAt_cmActive_split s0.sp]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro)
  cases m with
  | signalMessage sm =>
    refine SepWP.weaken_pre
      (sepConj_mono_left (apiEncResultAt_signal_entails_dealloc A.repAlloc p sm)) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro)
    rename_i g ctLen serLen addrP addrL
    have hfree : FreeOnlyEvs
        (vecPinEvs ctLen ++ vecPinEvs g.pqCap ++ optBoxEvs addrP addrL ++ vecPinEvs serLen) :=
      ((freeOnlyEvs_vecPinEvs ctLen).append (freeOnlyEvs_vecPinEvs g.pqCap)).append
        (freeOnlyEvs_optBoxEvs addrP addrL) |>.append (freeOnlyEvs_vecPinEvs serLen)
    have hfree' : FreeOnlyEvs
        (vecPinEvs ctLen ++ (vecPinEvs g.pqCap ++ (optBoxEvs addrP addrL ++ vecPinEvs serLen))) := by
      simpa only [List.append_assoc] using hfree
    apply SepWP.instantiate_post_exists
      (vecPinEvs ctLen ++ vecPinEvs g.pqCap ++ optBoxEvs addrP addrL ++ vecPinEvs serLen)
    let st1 := M.stepEvents (vecPinEvs ctLen) st
    let st2 := M.stepEvents (vecPinEvs g.pqCap) st1
    let st3 := M.stepEvents (optBoxEvs addrP addrL) st2
    let st4 := M.stepEvents (vecPinEvs serLen) st3
    have hst_all :
        M.stepEvents
          (vecPinEvs ctLen ++ vecPinEvs g.pqCap ++ optBoxEvs addrP addrL ++ vecPinEvs serLen) st =
        st4 := by
      simp only [M.stepEvents_append, st1, st2, st3, st4]
    rw [hst_all]
    refine seq_clean_state (mid := (blkPl_135).base + 264#64) (P_mid := fun s1 =>
      (sigHeadersAt p g ctLen serLen addrP addrL ∗
        vecPinDealloc A.repAlloc ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A.repAlloc addrP addrL ∗
        vecPinDealloc A.repAlloc ⟨serLen, g.serPtr⟩) ∗
      A.pool lim st1 s1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
       memRegion (s0.sp - 4160#64) 32))
      (Q := fun s1 => Saved32Preserved s0 s1 (s0.sp - 32#64) ∧ s1.readReg64 .x19 = p)
      ?_ ?_
    · dsimp only [sigHeadersAt, ctSignalTag]
      nth_rw 1 [vecPinDealloc]
      dsimp only [RustCliAllocBudget.repAlloc]
      by_cases hct : (ctLen == 0#64) = true <;>
        simp only [hct, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · have hst1 : st1 = st := by simp [st1, vecPinEvs, hct]
        wp_steps_sync_pool ((blkPl_135).base + 264#64)
        refine SepWP.align_pre_state (by simp only [hst1]; sep_ac_rfl) ?_
        wp_done
      · have hst1 : st1 = M.stepEvents (rustDeallocEvents ctLen.toNat 1) st := by
          simp [st1, vecPinEvs, hct]
        wp_steps_sync_pool (lsρ lsRustDeallocSym)
        wp_simp_pre [wp_norm]
        wp_apply with (g.ctPtr, ctLen.toNat, 1, st)
        refine SepWP.align_pre_state (by simp only [← hst1, wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1, hsp_1, htrace_1⟩, hx19_1⟩
      refine seq_clean_state (mid := (blkPl_135).base + 284#64) (P_mid := fun s2 =>
        (sigHeadersAt p g ctLen serLen addrP addrL ∗
          optBoxDealloc A.repAlloc addrP addrL ∗
          vecPinDealloc A.repAlloc ⟨serLen, g.serPtr⟩) ∗
        A.pool lim st2 s2 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         memRegion (s0.sp - 4160#64) 32))
        (Q := fun s2 => Saved32Preserved s0 s2 (s0.sp - 32#64) ∧ s2.readReg64 .x19 = p)
        ?_ ?_
      · dsimp only [sigHeadersAt]
        nth_rw 1 [vecPinDealloc]
        dsimp only [RustCliAllocBudget.repAlloc]
        by_cases hpq : (g.pqCap == 0#64) = true <;>
          simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · have hst2 : st2 = st1 := by simp [st2, vecPinEvs, hpq]
          wp_steps_sync_pool ((blkPl_135).base + 284#64)
          refine SepWP.align_pre_state (by simp only [hst2]; sep_ac_rfl) ?_
          wp_done
        · have hst2 : st2 = M.stepEvents (rustDeallocEvents g.pqCap.toNat 1) st1 := by
            simp [st2, vecPinEvs, hpq]
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          wp_simp_pre [wp_norm]
          wp_apply with (g.pqPtr, g.pqCap.toNat, 1, st1)
          refine SepWP.align_pre_state
            (by simp only [← hst2, wp_norm, arm64_norm, hsp_1]; sep_ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2, hsp_2, htrace_2⟩, hx19_2⟩
        refine seq_clean_state (mid := (blkPl_135).base + 308#64) (P_mid := fun s3 =>
          (sigHeadersAt p g ctLen serLen addrP addrL ∗
            vecPinDealloc A.repAlloc ⟨serLen, g.serPtr⟩) ∗
          A.pool lim st3 s3 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
           memRegion (s0.sp - 4160#64) 32))
          (Q := fun s3 => Saved32Preserved s0 s3 (s0.sp - 32#64) ∧ s3.readReg64 .x19 = p)
          ?_ ?_
        · dsimp only [sigHeadersAt]
          nth_rw 1 [optBoxDealloc]
          by_cases hp0 : (addrP == 0#64) = true <;>
            simp only [hp0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · have hst3 : st3 = st2 := by simp [st3, optBoxEvs, hp0]
            wp_steps_sync_pool ((blkPl_135).base + 308#64)
            refine SepWP.align_pre_state (by simp only [hst3]; sep_ac_rfl) ?_
            wp_done
          · nth_rw 1 [vecPinDealloc]
            dsimp only [RustCliAllocBudget.repAlloc]
            by_cases hl0 : (addrL == 0#64) = true <;>
              simp only [hl0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · have hst3 : st3 = st2 := by simp [st3, optBoxEvs, vecPinEvs, hp0, hl0]
              wp_steps_sync_pool ((blkPl_135).base + 308#64)
              refine SepWP.align_pre_state (by simp only [hst3]; sep_ac_rfl) ?_
              wp_done
            · have hst3 : st3 = M.stepEvents (rustDeallocEvents addrL.toNat 1) st2 := by
                simp [st3, optBoxEvs, vecPinEvs, hp0, hl0]
              wp_steps_sync_pool (lsρ lsRustDeallocSym)
              wp_simp_pre [wp_norm]
              wp_apply with (addrP, addrL.toNat, 1, st2)
              refine SepWP.align_pre_state
                (by simp only [← hst3, wp_norm, arm64_norm, hsp_2]; sep_ac_rfl) ?_
              wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hvregs_3, hsp_3, htrace_3⟩, hx19_3⟩
          dsimp only [sigHeadersAt, vecPinDealloc, RustCliAllocBudget.repAlloc]
          by_cases hser : (serLen == 0#64) = true <;>
            simp only [hser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · have hst4 : st4 = st3 := by simp [st4, vecPinEvs, hser]
            wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
            simp only [hst4]
            refine SepWP.weaken_pre
              (Entails.trans
                (Entails.of_eq (by dsimp only [sigHeadersAt]; sep_ac_rfl))
                (cm_cap0_weaken p
                  (sigHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL)
                  (A.pool lim st3 _) s0.sp
                  (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19))) ?_
            wp_done
          · have hst4 : st4 = M.stepEvents (rustDeallocEvents serLen.toNat 1) st3 := by
              simp [st4, vecPinEvs, hser]
            wp_steps_sync_pool (lsρ lsRustDeallocSym)
            wp_simp_pre [wp_norm]
            refine SepWP.weaken_pre
              (Entails.trans
                (Entails.of_eq (by dsimp only [sigHeadersAt]; sep_ac_rfl))
                (cm_tail_dealloc_pre_weaken p
                  (sigHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL)
                  (A.live g.serPtr serLen.toNat 1 ∗ memRegion g.serPtr serLen.toNat)
                  (A.pool lim st3 _) s0.sp
                  (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19))) ?_
            wp_apply with (g.serPtr, serLen.toNat, 1, st3)
            simp only [hst4]
            refine SepWP.weaken_pre
              (Entails.trans (Entails.of_eq (by sep_ac_rfl))
                (cm_tail_dealloc_post p (A.pool lim _ _) s0.sp)) ?_
            wp_done
  | preKeySignalMessage psm =>
    dsimp only [apiEncResultAt]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro)
    rename_i g
    refine SepWP.weaken_pre
      (sepConj_mono_left (preKeyMsgAt_entails_dealloc A.repAlloc g p psm)) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro)
    rename_i ctLen serLen addrP addrL pserLen kyP kyL
    refine SepWP.pure_elim_left fun hpq_lt => ?_
    have hmsb : g.msg.pqCap.msb = false := msb_eq_false_of_lt hpq_lt
    have hfree : FreeOnlyEvs
        (optBoxEvs kyP kyL ++ vecPinEvs ctLen ++ vecPinEvs g.msg.pqCap ++
          optBoxEvs addrP addrL ++ vecPinEvs serLen ++ vecPinEvs pserLen) :=
      ((((freeOnlyEvs_optBoxEvs kyP kyL).append (freeOnlyEvs_vecPinEvs ctLen)).append
        (freeOnlyEvs_vecPinEvs g.msg.pqCap)).append
        (freeOnlyEvs_optBoxEvs addrP addrL)).append
        (freeOnlyEvs_vecPinEvs serLen) |>.append
        (freeOnlyEvs_vecPinEvs pserLen)
    have hfree' : FreeOnlyEvs
        (optBoxEvs kyP kyL ++ (vecPinEvs ctLen ++ (vecPinEvs g.msg.pqCap ++
          (optBoxEvs addrP addrL ++ (vecPinEvs serLen ++ vecPinEvs pserLen))))) := by
      simpa only [List.append_assoc] using hfree
    apply SepWP.instantiate_post_exists
      (optBoxEvs kyP kyL ++ vecPinEvs ctLen ++ vecPinEvs g.msg.pqCap ++
        optBoxEvs addrP addrL ++ vecPinEvs serLen ++ vecPinEvs pserLen)
    let st1 := M.stepEvents (optBoxEvs kyP kyL) st
    let st2 := M.stepEvents (vecPinEvs ctLen) st1
    let st3 := M.stepEvents (vecPinEvs g.msg.pqCap) st2
    let st4 := M.stepEvents (optBoxEvs addrP addrL) st3
    let st5 := M.stepEvents (vecPinEvs serLen) st4
    let st6 := M.stepEvents (vecPinEvs pserLen) st5
    have hst_all :
        M.stepEvents
          (optBoxEvs kyP kyL ++ vecPinEvs ctLen ++ vecPinEvs g.msg.pqCap ++
            optBoxEvs addrP addrL ++ vecPinEvs serLen ++ vecPinEvs pserLen) st =
        st6 := by
      simp only [M.stepEvents_append, st1, st2, st3, st4, st5, st6]
    rw [hst_all]
    refine seq_clean_state (mid := (blkPl_135).base + 128#64) (P_mid := fun s1 =>
      (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
        vecPinDealloc A.repAlloc ⟨ctLen, g.msg.ctPtr⟩ ∗
        vecPinDealloc A.repAlloc ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
        optBoxDealloc A.repAlloc addrP addrL ∗
        vecPinDealloc A.repAlloc ⟨serLen, g.msg.serPtr⟩ ∗
        vecPinDealloc A.repAlloc ⟨pserLen, g.serPtr⟩) ∗
      A.pool lim st1 s1 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
       memRegion (s0.sp - 4160#64) 32))
      (Q := fun s1 => Saved32Preserved s0 s1 (s0.sp - 32#64) ∧
        s1.readReg64 .x19 = p ∧ s1.readReg64 .x20 = g.msg.pqCap)
      ?_ ?_
    · dsimp only [preKeyMsgHeadersAt, smHeadersAt]
      nth_rw 1 [optBoxDealloc]
      by_cases hkyP : (kyP == 0#64) = true <;>
        simp only [hkyP, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · have hst1 : st1 = st := by simp [st1, optBoxEvs, hkyP]
        wp_steps_sync_pool ((blkPl_135).base + 128#64)
        refine SepWP.align_pre_state (by simp only [hst1]; sep_ac_rfl) ?_
        wp_done
      · nth_rw 1 [vecPinDealloc]
        dsimp only [RustCliAllocBudget.repAlloc]
        by_cases hkyL : (kyL == 0#64) = true <;>
          simp only [hkyL, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · have hst1 : st1 = st := by simp [st1, optBoxEvs, vecPinEvs, hkyP, hkyL]
          wp_steps_sync_pool ((blkPl_135).base + 128#64)
          refine SepWP.align_pre_state (by simp only [hst1]; sep_ac_rfl) ?_
          wp_done
        · have hst1 : st1 = M.stepEvents (rustDeallocEvents kyL.toNat 1) st := by
            simp [st1, optBoxEvs, vecPinEvs, hkyP, hkyL]
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          wp_simp_pre [wp_norm]
          wp_apply with (kyP, kyL.toNat, 1, st)
          refine SepWP.align_pre_state
            (by simp only [← hst1, wp_norm, arm64_norm]; sep_ac_rfl) ?_
          wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1, hsp_1, htrace_1⟩, hx19_1, hx20_1⟩
      refine seq_clean_state (mid := (blkPl_135).base + 148#64) (P_mid := fun s2 =>
        (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
          vecPinDealloc A.repAlloc ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
          optBoxDealloc A.repAlloc addrP addrL ∗
          vecPinDealloc A.repAlloc ⟨serLen, g.msg.serPtr⟩ ∗
          vecPinDealloc A.repAlloc ⟨pserLen, g.serPtr⟩) ∗
        A.pool lim st2 s2 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         memRegion (s0.sp - 4160#64) 32))
        (Q := fun s2 => Saved32Preserved s0 s2 (s0.sp - 32#64) ∧
          s2.readReg64 .x19 = p ∧ s2.readReg64 .x20 = g.msg.pqCap)
        ?_ ?_
      · dsimp only [preKeyMsgHeadersAt, smHeadersAt]
        nth_rw 1 [vecPinDealloc]
        dsimp only [RustCliAllocBudget.repAlloc]
        by_cases hct : (ctLen == 0#64) = true <;>
          simp only [hct, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · have hst2 : st2 = st1 := by simp [st2, vecPinEvs, hct]
          wp_steps_sync_pool ((blkPl_135).base + 148#64)
          refine SepWP.align_pre_state (by simp only [hst2]; sep_ac_rfl) ?_
          wp_done
        · have hst2 : st2 = M.stepEvents (rustDeallocEvents ctLen.toNat 1) st1 := by
            simp [st2, vecPinEvs, hct]
          wp_steps_sync_pool (lsρ lsRustDeallocSym)
          wp_simp_pre [wp_norm]
          wp_apply with (g.msg.ctPtr, ctLen.toNat, 1, st1)
          refine SepWP.align_pre_state
            (by simp only [← hst2, wp_norm, arm64_norm, hsp_1]; sep_ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
        refine seq_clean_state (mid := (blkPl_135).base + 168#64) (P_mid := fun s3 =>
          (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
            optBoxDealloc A.repAlloc addrP addrL ∗
            vecPinDealloc A.repAlloc ⟨serLen, g.msg.serPtr⟩ ∗
            vecPinDealloc A.repAlloc ⟨pserLen, g.serPtr⟩) ∗
          A.pool lim st3 s3 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
           memRegion (s0.sp - 4160#64) 32))
          (Q := fun s3 => Saved32Preserved s0 s3 (s0.sp - 32#64) ∧ s3.readReg64 .x19 = p)
          ?_ ?_
        · dsimp only [preKeyMsgHeadersAt, smHeadersAt]
          nth_rw 1 [vecPinDealloc]
          dsimp only [RustCliAllocBudget.repAlloc]
          by_cases hpq : (g.msg.pqCap == 0#64) = true <;>
            simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · have hst3 : st3 = st2 := by simp [st3, vecPinEvs, hpq]
            wp_steps_sync_pool ((blkPl_135).base + 168#64)
            refine SepWP.align_pre_state (by simp only [hst3]; sep_ac_rfl) ?_
            wp_done
          · have hst3 : st3 = M.stepEvents (rustDeallocEvents g.msg.pqCap.toNat 1) st2 := by
              simp [st3, vecPinEvs, hpq]
            wp_steps_sync_pool (lsρ lsRustDeallocSym)
            wp_simp_pre [wp_norm]
            wp_apply with (g.msg.pqPtr, g.msg.pqCap.toNat, 1, st2)
            refine SepWP.align_pre_state
              (by simp only [← hst3, wp_norm, arm64_norm, hsp_2]; sep_ac_rfl) ?_
            wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hvregs_3, hsp_3, htrace_3⟩, hx19_3⟩
          refine seq_clean_state (mid := (blkPl_135).base + 192#64) (P_mid := fun s4 =>
            (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
              vecPinDealloc A.repAlloc ⟨serLen, g.msg.serPtr⟩ ∗
              vecPinDealloc A.repAlloc ⟨pserLen, g.serPtr⟩) ∗
            A.pool lim st4 s4 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
             memRegion (s0.sp - 4160#64) 32))
            (Q := fun s4 => Saved32Preserved s0 s4 (s0.sp - 32#64) ∧ s4.readReg64 .x19 = p)
            ?_ ?_
          · dsimp only [preKeyMsgHeadersAt, smHeadersAt]
            nth_rw 1 [optBoxDealloc]
            by_cases hp0 : (addrP == 0#64) = true <;>
              simp only [hp0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · have hst4 : st4 = st3 := by simp [st4, optBoxEvs, hp0]
              wp_steps_sync_pool ((blkPl_135).base + 192#64)
              refine SepWP.align_pre_state (by simp only [hst4]; sep_ac_rfl) ?_
              wp_done
            · nth_rw 1 [vecPinDealloc]
              dsimp only [RustCliAllocBudget.repAlloc]
              by_cases hl0 : (addrL == 0#64) = true <;>
                simp only [hl0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · have hst4 : st4 = st3 := by simp [st4, optBoxEvs, vecPinEvs, hp0, hl0]
                wp_steps_sync_pool ((blkPl_135).base + 192#64)
                refine SepWP.align_pre_state (by simp only [hst4]; sep_ac_rfl) ?_
                wp_done
              · have hst4 : st4 = M.stepEvents (rustDeallocEvents addrL.toNat 1) st3 := by
                  simp [st4, optBoxEvs, vecPinEvs, hp0, hl0]
                wp_steps_sync_pool (lsρ lsRustDeallocSym)
                wp_simp_pre [wp_norm]
                wp_apply with (addrP, addrL.toNat, 1, st3)
                refine SepWP.align_pre_state
                  (by simp only [← hst4, wp_norm, arm64_norm, hsp_3]; sep_ac_rfl) ?_
                wp_done
          · intro s4 hpc4 hrun4 ⟨⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hvregs_4, hsp_4, htrace_4⟩, hx19_4⟩
            refine seq_clean_state (mid := (blkPl_135).base + 212#64) (P_mid := fun s5 =>
              (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
                vecPinDealloc A.repAlloc ⟨pserLen, g.serPtr⟩) ∗
              A.pool lim st5 s5 ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
               ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
               memRegion (s0.sp - 4160#64) 32))
              (Q := fun s5 => Saved32Preserved s0 s5 (s0.sp - 32#64) ∧ s5.readReg64 .x19 = p)
              ?_ ?_
            · dsimp only [preKeyMsgHeadersAt, smHeadersAt]
              nth_rw 1 [vecPinDealloc]
              dsimp only [RustCliAllocBudget.repAlloc]
              by_cases hser : (serLen == 0#64) = true <;>
                simp only [hser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · have hst5 : st5 = st4 := by simp [st5, vecPinEvs, hser]
                wp_steps_sync_pool ((blkPl_135).base + 212#64)
                refine SepWP.align_pre_state (by simp only [hst5]; sep_ac_rfl) ?_
                wp_done
              · have hst5 : st5 = M.stepEvents (rustDeallocEvents serLen.toNat 1) st4 := by
                  simp [st5, vecPinEvs, hser]
                wp_steps_sync_pool (lsρ lsRustDeallocSym)
                wp_simp_pre [wp_norm]
                wp_apply with (g.msg.serPtr, serLen.toNat, 1, st4)
                refine SepWP.align_pre_state
                  (by simp only [← hst5, wp_norm, arm64_norm, hsp_4]; sep_ac_rfl) ?_
                wp_done
            · intro s5 hpc5 hrun5 ⟨⟨hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hvregs_5, hsp_5, htrace_5⟩, hx19_5⟩
              dsimp only [preKeyMsgHeadersAt, smHeadersAt, vecPinDealloc,
                RustCliAllocBudget.repAlloc]
              by_cases hpser : (pserLen == 0#64) = true <;>
                simp only [hpser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · have hst6 : st6 = st5 := by simp [st6, vecPinEvs, hpser]
                wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
                simp only [hst6]
                refine SepWP.weaken_pre
                  (Entails.trans
                    (Entails.of_eq (by dsimp only [preKeyMsgHeadersAt, smHeadersAt]; sep_ac_rfl))
                    (cm_cap0_weaken p
                      (preKeyMsgHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL pserLen kyP kyL)
                      (A.pool lim st5 _) s0.sp
                      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19))) ?_
                wp_done
              · have hst6 : st6 = M.stepEvents (rustDeallocEvents pserLen.toNat 1) st5 := by
                  simp [st6, vecPinEvs, hpser]
                wp_steps_sync_pool (lsρ lsRustDeallocSym)
                wp_simp_pre [wp_norm]
                refine SepWP.weaken_pre
                  (Entails.trans
                    (Entails.of_eq (by dsimp only [preKeyMsgHeadersAt, smHeadersAt]; sep_ac_rfl))
                    (cm_tail_dealloc_pre_weaken p
                      (preKeyMsgHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL pserLen kyP kyL)
                      (A.live g.serPtr pserLen.toNat 1 ∗ memRegion g.serPtr pserLen.toNat)
                      (A.pool lim st5 _) s0.sp
                      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19))) ?_
                wp_apply with (g.serPtr, pserLen.toNat, 1, st5)
                simp only [hst6]
                refine SepWP.weaken_pre
                  (Entails.trans (Entails.of_eq (by sep_ac_rfl))
                    (cm_tail_dealloc_post p (A.pool lim _ _) s0.sp)) ?_
                wp_done

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDropBudget
