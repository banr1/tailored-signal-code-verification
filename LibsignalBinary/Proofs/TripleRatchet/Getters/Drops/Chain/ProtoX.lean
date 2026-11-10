/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WPp

/-!
# Extended-Stack Contracts for `drop_glue<session_structure::Chain>` (`AllocContractsX`)

Proves `drop_proto_chain_ok_x` and `drop_chain_ok_x` (`dropChainStackX = 48 + extHookStack`) for
`core::ptr::drop_glue::<session_structure::Chain>` (`0x35dc8`) under `AllocContractsX`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem chain_memRegions_entails_104 (a : BitVec 64) :
    memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32 ⊢ memRegion a 104 :=
  DropGlueFacts.chain_memRegions_entails_104 a

private theorem vecAt_expose_loop_at_48 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (a cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (a + 48#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      arrayAt elem sz ptr xs ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz)) := by
  have h := vecAt_expose_loop A sz align elem (a + 48#64) cap ptr xs
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rwa [h1, h2] at h

private theorem post_loop_weaken_at_48 (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (Rest : SepProp) :
    ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion ptr (n * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) ∗
      Rest ⊢
    ((a + 48#64) ↦₆₄ cap) ∗ (((a + 48#64) + 8#64) ↦₆₄ ptr) ∗ memRegion ((a + 48#64) + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
      Rest := by
  have h := post_loop_weaken A (a + 48#64) cap ptr n hle hcap_lt Rest
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [h1, h2] at h
  rw [h1, h2]
  exact h

/-! ## 4. `drop_proto_chain_ok_x` and `drop_chain_ok_x` (`AllocContractsX` / `extHookStack`) -/

@[local wp_norm] private theorem frozenLoaded_writeReg64 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) ↔ img.FrozenLoaded s := by
  have hmem : (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPC (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPState (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPState ps).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by
  cases s; cases r <;> rfl

@[local wp_norm] private theorem symtab_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by
  cases s; rfl

@[local wp_norm] private theorem symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by
  cases s; rfl

@[local wp_norm] private theorem exists_two_pow_one : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem exists_two_pow_eight : (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

private theorem SepWP.seq_callInv {prog : Program} {img : Obj.Image} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid_pc s P (fun sm P_m =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm P_m post)) :
    SepWP prog target_pc s P post :=
  ProofLib.SepWP.of_sepWP_inv hfrozen hsym h1

private theorem seq_cleanX {prog : Program} {img : Obj.Image} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  refine SepWP.seq_callInv hfrozen hsym (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hent, hQ⟩ hfrozen_m hsym_m
  exact SepWP.weaken_pre hent (h2 sm hpc hrun hfrozen_m hsym_m hQ)

private theorem stackAt_dropChainX_split (sp : BitVec 64) :
    stackAt sp dropChainStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp extHookStack 6 (by decide)

private theorem tail_stack_48_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  rw [show (16432#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 48) from rfl,
      ← stackAt_split_bottom sp extHookStack 48 (by decide),
      show extHookStack + 48 = dropChainStackX from rfl,
      ← stackAt_dropChainX_split sp]

private theorem stack_restore_48_extHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) extHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropChainStackX := by
  rw [stackAt_dropChainX_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

private theorem chain_cap0_weakenX (a cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    ((a + 48#64) ↦₆₄ cap) ∗ (((a + 48#64) + 8#64) ↦₆₄ ptr) ∗ memRegion ((a + 48#64) + 16#64) 8 ∗
      (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗
      Pool ∗ stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion a 104 ∗ Pool ∗ stackAt sp dropChainStackX := by
  refine Entails.trans (header24_weaken (a + 48#64) cap ptr _) ?_
  rw [← sepConj_assoc (memRegion (a + 48#64) 24)]
  refine sepConj_mono (DropGlueFacts.chain_memRegions_entails_104 a) ?_
  exact sepConj_mono_right (stack_restore_48_extHook sp fp lr x22 x21 x20 x19)

private theorem tail_dealloc_chain_pre_weakenX (v cap ptr : BitVec 64)
    (live outer pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      live ∗ outer ∗ pool ∗
      stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ outer ∗ pool ∗
      memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack ∗ live := by
  have h1 := header_cells_entails_memRegion_24 v cap ptr
  have h2 :
      stackAt (sp - 48#64) extHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack := by
    rw [tail_stack_48_from_bottomX sp]
    exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)
  have hreord :
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
        live ∗ outer ∗ pool ∗
        stackAt (sp - 48#64) extHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗
        (live ∗ outer ∗ pool ∗
         (stackAt (sp - 48#64) extHookStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem chain_tail_dealloc_postX (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ memRegion (a + 48#64) 24 ∗
      memRegion a 48 ∗ memRegion (a + 72#64) 32 ∗ memRegion (sp - 16432#64) 48 ⊢
    memRegion a 104 ∗ Pool ∗ stackAt sp dropChainStackX := by
  have heq :
      (Pool ∗ stackAt sp extHookStack ∗ memRegion (a + 48#64) 24 ∗
        memRegion a 48 ∗ memRegion (a + 72#64) 32 ∗ memRegion (sp - 16432#64) 48) =
      ((memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗
        Pool ∗ (memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack)) := by ac_rfl
  rw [heq]
  refine sepConj_mono (DropGlueFacts.chain_memRegions_entails_104 a) ?_
  rw [stackAt_dropChainX_split sp, ← tail_stack_48_from_bottomX sp]
  exact Entails.of_eq (by ac_rfl)

@[reducible]
private def vecPinDeallocX (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗ A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

@[reducible]
private def ckDeallocX (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

private theorem vecU8At_entails_pin_deallocX (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDeallocX
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases h0 : pin.cap = 0
  · simp only [h0, ↓reduceIte]; exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < pin.cap.toNat :=
      Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
    exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)

private theorem vecGhostAt_entails_pin_deallocX (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_deallocX A a ⟨g.cap, g.ptr⟩ g.bytes

private theorem optChainKeyAt_entails_deallocX (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        ckDeallocX A cap ptr := by
  unfold ckDeallocX
  cases ck with
  | none =>
    unfold optChainKeyAt
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right optChainKeyNone (Entails.sepExists_right ptr ?_)
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some c =>
    unfold optChainKeyAt
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : pin.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        have hpos : 0 < pin.cap.toNat :=
          Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
        exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢
          memRegion (a + 16#64) 16 := by
      rw [ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
            (b' := a + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := a + 24#64) (n := 4) (k := 4)
            (b' := a + 28#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
    have hpull :
        (((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) =
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
            ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

private theorem messageKeyAt_entails_deallocX (A : RustAlloc) (cur : BitVec 64)
    (pin : MessageKeyGhost) (mk : MessageKeyGenerator) :
    messageKeyAt A (pin, mk) cur ⊢
      mkHeadersAt cur pin ∗
      vecPinDeallocX A pin.cipher ∗ vecPinDeallocX A pin.mac ∗
      vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed := by
  unfold messageKeyAt mkHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecU8At_entails_pin_deallocX A cur pin.cipher []
  have h2 := vecU8At_entails_pin_deallocX A (cur + 24#64) pin.mac []
  have h3 := vecU8At_entails_pin_deallocX A (cur + 48#64) pin.iv []
  have h4 := vecU8At_entails_pin_deallocX A (cur + 72#64) pin.seed mk.seed
  have h5 : ((cur + 96#64) ↦₃₂ mk.counter) ∗ memRegion (cur + 100#64) 4 ⊢ memRegion (cur + 96#64) 8 := by
    rw [ProofLib.memRegion_split' (b := cur + 96#64) (n := 4) (k := 4)
          (b' := cur + 100#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion _ _)
  have ha1 : (cur + 24#64) + 8#64 = cur + 32#64 := by bv_omega
  have ha2 : (cur + 24#64) + 16#64 = cur + 40#64 := by bv_omega
  have hb1 : (cur + 48#64) + 8#64 = cur + 56#64 := by bv_omega
  have hb2 : (cur + 48#64) + 16#64 = cur + 64#64 := by bv_omega
  have hc1 : (cur + 72#64) + 8#64 = cur + 80#64 := by bv_omega
  have hc2 : (cur + 72#64) + 16#64 = cur + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 h5)))) ?_
  apply Entails.of_eq
  ac_rfl

private theorem protoChainAt_entails_deallocX (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    protoChainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold protoChainAt chainOuterHeadersAt
  apply Entails.pure_left; intro _
  have h1 := vecGhostAt_entails_pin_deallocX A g.srk a
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_deallocX A g.ck c.chainKey (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckCap
  rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckPtr
  refine Entails.sepExists_right ckCap (Entails.sepExists_right ckPtr ?_)
  apply Entails.of_eq
  ac_rfl

private theorem pos_of_beq_zero_false {cap : BitVec 64} (h : ¬(cap == 0#64) = true) :
    0 < cap.toNat := by
  have hne : cap ≠ 0#64 := fun heq => h (beq_iff_eq.mpr heq)
  exact Nat.pos_of_ne_zero (fun h0 => hne (BitVec.eq_of_toNat_eq h0))

private theorem drop_chain_outer_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (s0 : State) (fsp a : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 16#64 →
      s.status = .Running →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDeallocX A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro g ckCap ckPtr s Frame hpc hrun hfrozen hsym hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_cleanX (mid := entry + bv% (40)) (P_mid :=
    (chainOuterHeadersAt a g ckCap ckPtr ∗
      vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDeallocX A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
    hfrozen hsym ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDeallocX, ckDeallocX]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos, hlt⟩
      wp_steps
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_cleanX (mid := entry + bv% (60)) (P_mid :=
      (chainOuterHeadersAt a g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
      hfrozen1 hsym1 ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDeallocX, ckDeallocX]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · refine SepWP.focus_pure (by sep_focus) ?_
        rintro ⟨hpos, hlt⟩
        wp_steps
        wp_call hdealloc (g.priv.ptr, g.priv.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (84)) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDeallocX]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · refine SepWP.focus_pure (by sep_focus) ?_
          rintro ⟨hpos, hlt⟩
          wp_steps
          wp_call hdealloc (ckPtr, ckCap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem drop_chain_body_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 112#64 →
      s.status = .Running →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 100#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64) := by
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_deallocX A cur pin mk)) ?_
  refine seq_cleanX (mid := entry + bv% (132)) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.mac ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
    A.pool ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    hfrozen hsym ?_ ?_
  · dsimp only [mkHeadersAt, vecPinDeallocX]
    by_cases hcap : (pin.cipher.cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos, hlt⟩
      wp_steps
      wp_call hdealloc (pin.cipher.ptr, pin.cipher.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_cleanX (mid := entry + bv% (152)) (P_mid :=
      (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.iv ∗ vecPinDeallocX A pin.seed) ∗
      A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      hfrozen1 hsym1 ?_ ?_
    · dsimp only [mkHeadersAt, vecPinDeallocX]
      by_cases hcap : (pin.mac.cap == 0#64) = true <;>
        simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · refine SepWP.focus_pure (by sep_focus) ?_
        rintro ⟨hpos, hlt⟩
        wp_steps
        wp_call hdealloc (pin.mac.ptr, pin.mac.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_cleanX (mid := entry + bv% (172)) (P_mid :=
        (mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗
        A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        hfrozen2 hsym2 ?_ ?_
      · dsimp only [mkHeadersAt, vecPinDeallocX]
        by_cases hcap : (pin.iv.cap == 0#64) = true <;>
          simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · refine SepWP.focus_pure (by sep_focus) ?_
          rintro ⟨hpos, hlt⟩
          wp_steps
          wp_call hdealloc (pin.iv.ptr, pin.iv.cap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 hfrozen3 hsym3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (100)) s3
            ((mkHeadersAt cur pin ∗ vecPinDeallocX A pin.seed) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          dsimp only [mkHeadersAt, vecPinDeallocX]
          by_cases hcap : (pin.seed.cap == 0#64) = true <;>
            simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · refine SepWP.focus_pure (by sep_focus) ?_
            rintro ⟨hpos, hlt⟩
            wp_steps
            wp_call hdealloc (pin.seed.ptr, pin.seed.cap.toNat, 1)
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_chain_loop_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 112#64 →
      s.status = .Running →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + 196#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_chain_body_x hdealloc s0 fsp v ptr hfsp_align
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_cleanX (mid := entry + bv% (100)) hfrozen hsym
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hfrozen4 hsym4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

theorem drop_proto_chain_ok_x_of_dealloc {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName)
      ((dropProtoChainSpecX A).inImage img) := by
  simp only [Spec.inImage, dropProtoChainSpecX]
  have hdealloc := hdealloc_raw
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  have houter := drop_chain_outer_x (img := img) (ext := ext) hdealloc_raw
  have hloop := drop_chain_loop_x (img := img) (ext := ext) hdealloc_raw
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at hdealloc houter hloop ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, g, c⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoChainAt_entails_deallocX A (s0.readReg64 (Reg.gpr 0#5)) g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  refine seq_cleanX (mid := entry + bv% (16))
    (P_mid :=
      (chainOuterHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
        (g.keys.zip c.messageKeys) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    h_2 h_1 ?_ ?_
  · wp_steps
    refine DropGlueFacts.align_pre (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨hpres1, hx0_1⟩
    refine seq_cleanX (mid := entry + bv% (84))
      (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      hfrozen1 hsym1 ?_ ?_
    · dsimp only [chainOuterHeadersAt]
      simp only [sepConj_assoc]
      refine SepWP.mono
        (houter s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align g ckCap ckPtr s1
          (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          hpc1 hrun1 hfrozen1 hsym1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq
      ac_rfl
    · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A 104 8 (messageKeyAt A)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      refine seq_cleanX (mid := entry + bv% (196))
        (P_mid :=
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104)) ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x20 = g.mkPtr)
        hfrozen2 hsym2 ?_ ?_
      · cases mks with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          wp_steps
          wp_done
        | cons hd tl =>
          have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
          wp_steps
          have hpre_eq :
              (((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
                (if g.mkCap = 0 then emp
                 else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
                   memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
              (arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
                (((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if g.mkCap = 0 then emp
                   else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
                     memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                  (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
            ac_rfl
          rw [hpre_eq]
          refine SepWP.mono
            (hloop s0 (s0.sp - 48#64) g.mkPtr (s0.readReg64 (Reg.gpr 0#5)) hfsp_align (hd :: tl) g.mkPtr _ _
              (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
              (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
              ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩
              hx19_2 rfl rfl rfl) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          apply Entails.of_eq
          ac_rfl
      · intro sm hpcm hrunm hfrozenm hsymm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (chain_cap0_weakenX (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr A.pool s0.sp _ _ _ _ _ _) ?_
          wp_done
        · have hcap_pos := pos_of_beq_zero_false hcap
          have hsz_pos : 0 < g.mkCap.toNat * 104 := Nat.mul_pos hcap_pos (by decide)
          wp_steps
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weakenX (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ _ s0.sp _ _ _ _ _ _) ?_
          wp_call hdealloc (g.mkPtr, g.mkCap.toNat * 104, 8)
          refine SepWP.weaken_pre
            (chain_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
          wp_done

theorem drop_proto_chain_ok_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName)
      ((dropProtoChainSpecX A).inImage img) :=
  drop_proto_chain_ok_x_of_dealloc
    (hA.dealloc_ok_at dropChainName
      (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      (by fnoff_eq))

theorem drop_chain_ok_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName)
      ((dropChainSpecX A).inImage img) :=
  subroutine_ok_mono (drop_proto_chain_ok_x hA)
    (fun x _ _ hpre => by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      simp only [Spec.inImage, dropChainSpecX, dropProtoChainSpecX]
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A x.gc x.a))))
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

end CryptoVerification.LibsignalTripleRatchet.Getters
