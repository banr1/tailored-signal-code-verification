/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase -- shake: keep

/-!
# Stage P3 Error-Drop and OOM-Aware Allocation Wrappers for `message_decrypt_prekey::{closure#0}`

Proves `drop_spe2_ver_ok` (`UnrecognizedMessageVersion` tag `6`) and OOM-aware `__rust_alloc`
wrappers (`p3_alloc_179c_ok` .. `p3_alloc_33b0_ok`) for Stage P3 of
`message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

export CryptoVerification.E2E.Pqxdh.ResponderClosure (
  cond_eq_subs32_4_0
  cond_ne_subs32_4_4
  cond_ne_subs32_4_of_ne
)

/-! ## 1. `drop_spe2_ver_ok` (`UnrecognizedMessageVersion` Tag `6`) -/

theorem speJumpTable_adrp_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + 462088#64) :
    (entry + 40#64 &&& 18446744073709547520#64) = base + 458752#64 := by
  subst he
  have hadd : base + 462088#64 + 40#64 = base + 462128#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned hb]
  rfl

theorem spe_ver_entails_48 (a : BitVec 64) (msgVer : BitVec 32) :
    (a ↦₆₄ 0x8000000000000006#64) ∗ ((a + 8#64) ↦₃₂ msgVer) ∗ memRegion (a + 12#64) 36 ⊢
      memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono (pointsTo64_entails_memRegion a 0x8000000000000006#64)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) msgVer) (IsBlock.memRegion (a + 8#64) 4)
        fun _ _ => trivial))

theorem cells4_entails_dropSpeStack (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp dropSpeStack := by
  rw [stackAt_dropSpe_split sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

def dropSpeVerSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 32) where
  pre := fun (a, msgVer) s =>
    ⌜s.readReg64 .x0 = a⌝ ∗
    (a ↦₆₄ 0x8000000000000006#64) ∗
    ((a + 8#64) ↦₃₂ msgVer) ∗
    memRegion (a + 12#64) 36 ∗
    A.pool ∗
    stackAt s.sp dropSpeStack
  post := fun (a, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    memRegion a 48 ∗
    A.pool ∗
    stackAt s0.sp dropSpeStack

/-! ## 2. OOM-Aware `__rust_alloc` Wrappers (`+0x179c`, `+0x18fc`, `+0x1938`, `+0x1b48`, `+0x2eac`, `+0x33b0`) -/

theorem CalleeSavedPreserved.trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩
  rcases h12 with ⟨k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, kv⟩
  exact ⟨k19.trans h19, k20.trans h20, k21.trans h21, k22.trans h22, k23.trans h23,
    k24.trans h24, k25.trans h25, k26.trans h26, k27.trans h27, k28.trans h28, k29.trans h29,
    kv.trans hv⟩

theorem pull_pure_alloc_oom (P1 P2 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ ⌜φ⌝) ∗ F = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ F) := by ac_rfl

theorem pull_pure_alloc_ok (P1 P2 P3 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3)) ∗ F = ⌜φ⌝ ∗ ((P3 ∗ P1 ∗ P2) ∗ F) := by ac_rfl

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
