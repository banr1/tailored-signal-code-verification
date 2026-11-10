/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common

/-!
# In-Image Verification of `drop_glue::<Chain> [local#2]` (`0x7114c`)

Proves `drop_chain2_ok` for `core::ptr::drop_glue::<session_structure::Chain> [local#2]` at image
offset `0x7114c`.
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

abbrev dropChain2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]"

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem chain_memRegions_entails_104 (a : BitVec 64) :
    memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32 ⊢ memRegion a 104 :=
  DropGlueFacts.chain_memRegions_entails_104 a

private theorem drop6_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro x_4; refine Entails.sepExists_right x_4 ?_
  apply Entails.sepExists_elim; intro x_5; refine Entails.sepExists_right x_5 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

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

private theorem tail_dealloc_chain_pre_weaken (v cap ptr : BitVec 64)
    (live outer pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      live ∗ outer ∗ pool ∗
      stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ outer ∗ pool ∗
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 := header_cells_entails_memRegion_24 v cap ptr
  have h2 :
      stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_48_from_bottom sp]
    exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)
  have hreord :
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
        live ∗ outer ∗ pool ∗
        stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗
        (live ∗ outer ∗ pool ∗
         (stackAt (sp - 48#64) allocHookStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalTripleRatchet.Getters
