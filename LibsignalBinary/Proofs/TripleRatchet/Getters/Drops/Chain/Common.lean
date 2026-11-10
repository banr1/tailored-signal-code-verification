/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common

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

namespace DropGlueFacts

theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 := by
  unfold chainOuterHeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.srk.cap g.srk.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.priv.cap g.priv.ptr
  have h3 := header_cells_entails_memRegion_32 (a + 72#64) ckCap ckPtr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hc1, hc2] at h3
  have hgroup :
      ((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8 ∗
        ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16) =
      (((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8) ∗
       (((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 24) (b' := a + 24#64) rfl rfl (by decide),
      show (memRegion a 24 ∗ memRegion (a + 24#64) 24) ∗ memRegion (a + 72#64) 32 =
        memRegion a 24 ∗ memRegion (a + 24#64) 24 ∗ memRegion (a + 72#64) 32 from sepConj_assoc _ _ _]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem chain_memRegions_entails_104 (a : BitVec 64) :
    memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32 ⊢ memRegion a 104 := by
  have heq :
      (memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32) =
      (memRegion a 48 ∗ memRegion (a + 48#64) 24 ∗ memRegion (a + 72#64) 32) := by ac_rfl
  rw [heq,
      ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 24) (k := 32) (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem chain_cap0_weaken (a cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    ((a + 48#64) ↦₆₄ cap) ∗ (((a + 48#64) + 8#64) ↦₆₄ ptr) ∗ memRegion ((a + 48#64) + 16#64) 8 ∗
      (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗
      Pool ∗ stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion a 104 ∗ Pool ∗ stackAt sp dropChainStack := by
  refine Entails.trans (header24_weaken (a + 48#64) cap ptr _) ?_
  rw [← sepConj_assoc (memRegion (a + 48#64) 24)]
  refine sepConj_mono (chain_memRegions_entails_104 a) ?_
  rw [show dropChainStack = dropVecMessageKeyStack from rfl]
  exact sepConj_mono_right (stack_restore_48_allocHook sp fp lr x22 x21 x20 x19)

theorem chain_tail_dealloc_post (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion (a + 48#64) 24 ∗
      memRegion a 48 ∗ memRegion (a + 72#64) 32 ∗ memRegion (sp - 4144#64) 48 ⊢
    memRegion a 104 ∗ Pool ∗ stackAt sp dropChainStack := by
  have heq :
      (Pool ∗ stackAt sp allocHookStack ∗ memRegion (a + 48#64) 24 ∗
        memRegion a 48 ∗ memRegion (a + 72#64) 32 ∗ memRegion (sp - 4144#64) 48) =
      ((memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗
        Pool ∗ (memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack)) := by ac_rfl
  rw [heq]
  refine sepConj_mono (chain_memRegions_entails_104 a) ?_
  rw [show dropChainStack = dropVecMessageKeyStack from rfl,
      stackAt_dropVecMessageKey_split sp, ← tail_stack_48_from_bottom sp]
  exact Entails.of_eq (by ac_rfl)

theorem vecChain_tail_dealloc_post (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion v 24 ∗ memRegion (sp - 4192#64) 96 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStack := by
  rw [show dropVecChainStack = allocHookStack + 96 from rfl,
      stackAt_split_bottom sp allocHookStack 96 (by decide)]
  exact Entails.of_eq (by ac_rfl)

end DropGlueFacts


theorem chainAt_entails_protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a ⊢ protoChainAt A gc a := by
  unfold chainAt protoChainAt
  apply Entails.pure_left; rintro ⟨h1, h2, h3, _, _⟩
  exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _)


end CryptoVerification.LibsignalTripleRatchet.Getters
