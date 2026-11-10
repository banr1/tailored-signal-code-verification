/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.X
import ProofLib.SepLogic.WPp

/-!
# `AllocContractsX` Verification of `drop_glue<Vec<Chain>>`

Proves the `extHookStack` contract `dropVecChainSpecX` for
`core::ptr::drop_glue::<alloc::vec::Vec<...::Chain>>` under `AllocContractsX`.
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


private theorem fnAddr_dropVecMessageKey_eq_dropVecChain_add (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecMessageKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 180#64 := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")]
  bv_omega

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


private theorem chainAt_entails_deallocX (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    chainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) :=
  Entails.trans (chainAt_entails_protoChainAt A (g, c) a) (protoChainAt_entails_deallocX A a g c)

private theorem stackAt_dropVecChainX_split (sp : BitVec 64) :
    stackAt sp dropVecChainStackX =
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp dropVecMessageKeyStackX 6 (by decide)

private theorem stackAt_dropVecMessageKeyX_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStackX =
      memRegion (fsp - 16432#64) 48 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 48 (by decide)

private theorem tail_stack_96_from_bottomX (sp : BitVec 64) :
    memRegion (sp - 16480#64) 96 ∗ stackAt sp extHookStack =
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_dropVecChainX_split sp]
  exact (stackAt_split_bottom sp extHookStack 96 (by decide)).symm

private theorem stack_restore_48_vecChainX (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropVecChainStackX := by
  rw [stackAt_dropVecChainX_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

private theorem cap0_weaken_48_vecChainX (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  exact sepConj_mono_right (sepConj_mono_right (stack_restore_48_vecChainX sp fp lr x22 x21 x20 x19))

private theorem cells6_vecChain_entails_stack_bottomX (sp : BitVec 64)
    (fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 16480#64) 96 ∗ stackAt sp extHookStack := by
  rw [tail_stack_96_from_bottomX sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

private theorem tail_dealloc_vecChain_pre_weakenX (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion v 24 ∗ memRegion (sp - 16480#64) 96) := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  have hstk := cells6_vecChain_entails_stack_bottomX sp fp lr x22 x21 x20 x19
  have hgroup :
      (memRegion v 24 ∗ Live ∗ Pool ∗
        stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((stackAt (sp - 48#64) dropVecMessageKeyStackX ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗
        (Pool ∗ Live ∗ memRegion v 24)) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_left hstk) ?_
  apply Entails.of_eq
  ac_rfl

private theorem vecChain_tail_dealloc_postX (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ memRegion v 24 ∗ memRegion (sp - 16480#64) 96 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStackX := by
  rw [show dropVecChainStackX = extHookStack + 96 from rfl,
      stackAt_split_bottom sp extHookStack 96 (by decide)]
  exact Entails.of_eq (by ac_rfl)

private theorem drop_vec_chain_body_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = cnt →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 44#64)
        s
        (chainAt A (g, c) cur ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧
          sm.readReg64 .x22 = cnt) := by
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  simp only [Spec.inImage, dropVecMessageKeySpecX] at hdrop_mk
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro cur cnt g c s Frame hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_deallocX A cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
  refine seq_cleanX (mid := entry + bv% (76)) (P_mid :=
    (chainOuterHeadersAt cur g ckCap ckPtr ∗
      vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDeallocX A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp extHookStack ∗
    (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
      memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
    hfrozen hsym ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDeallocX, ckDeallocX]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine DropGlueFacts.align_pre (by ac_rfl) ?_
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos, hlt⟩
      wp_steps
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_cleanX (mid := entry + bv% (96)) (P_mid :=
      (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp extHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
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
    · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_cleanX (mid := entry + bv% (36)) (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
        ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
        hfrozen2 hsym2 ?_ ?_
      · have hstep3 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (36)) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A ckCap ckPtr) ∗
              A.pool ∗ stackAt fsp extHookStack ∗
              (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 16432#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool ∗ stackAt fsp extHookStack ∗
                (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          dsimp only [chainOuterHeadersAt, ckDeallocX]
          by_cases hcap : ckCap.slt 1#64 = true <;>
            simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · refine SepWP.focus_pure (by sep_focus) ?_
            rintro ⟨hpos, hlt⟩
            wp_steps
            wp_call hdealloc (ckPtr, ckCap.toNat, 1)
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
        apply Entails.of_eq
        ac_rfl
      · intro s3 hpc3 hrun3 hfrozen3 hsym3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        rw [← stackAt_dropVecMessageKeyX_split_bottom fsp]
        have hstep4 : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (44)) s3
            (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          wp_steps
          wp_call hdrop_mk ⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩
          refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_loop_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 124#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_body_x hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_cleanX (mid := entry + bv% (44)) hfrozen hsym
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hfrozen hsym hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hfrozen4 hsym4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
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
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
          rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

theorem drop_vec_chain_ok_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName)
      ((dropVecChainSpecX A).inImage img) := by
  simp only [Spec.inImage, dropVecChainSpecX]
  have hdealloc_raw := hA.dealloc_ok_at dropVecChainName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")]; simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  have hdrop_mk_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName + 180#64)
      ((dropVecMessageKeySpecX A).inImage img) := by
    rw [← fnAddr_dropVecMessageKey_eq_dropVecChain_add]
    exact drop_vec_message_key_ok_x hA
  have hloop := drop_vec_chain_loop_x (img := img) (ext := ext) hdealloc_raw hdrop_mk_raw
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, cs⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine seq_cleanX (mid := entry + bv% (124))
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    h_2 h_1 ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine SepWP.seq_callInv (mid_pc := entry + bv% (56)) h_2 h_1 ?_
      wp_steps
      refine SepWP.done rfl (by assumption) fun hfrozen_pro hsym_pro => ?_
      have hpre_eq :
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              (if cap = 0 then emp
               else A.live ptr (cap.toNat * 104) 8 ∗
                 memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      refine SepWP.mono
        (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
          hfrozen_pro hsym_pro
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl rfl rfl rfl) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq
      ac_rfl
  · intro sm hpcm hrunm hfrozenm hsymm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (cap0_weaken_48_vecChainX (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_pos := pos_of_beq_zero_false hcap
      have hsz_pos : 0 < cap.toNat * 104 := Nat.mul_pos hcap_pos (by decide)
      wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weakenX (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat * 104, 8)
      refine SepWP.weaken_pre (vecChain_tail_dealloc_postX (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

end CryptoVerification.LibsignalTripleRatchet.Getters
