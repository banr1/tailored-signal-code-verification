/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `drop_glue<session_structure::Chain>` (`0x35dc8`, Block `142`)

Proves fixed-image (`drop_proto_chain_ok_ext`, `drop_chain_ok`) and relocatable `[LibsignalPlacement]`
(`drop_proto_chain_placed_ok`, `drop_chain_placed_ok`) contracts for
`core::ptr::drop_glue::<session_structure::Chain>`.
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

/-! ## 2. `drop_chain_ok` (`0x35dc8`) -/

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem chain_memRegions_entails_104 (a : BitVec 64) :
    memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32 ⊢ memRegion a 104 :=
  DropGlueFacts.chain_memRegions_entails_104 a

private theorem drop6_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
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
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem drop_chain_outer {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      (rustDeallocSpec A))
    (s0 : State) (fsp a : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropChainName + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro g ckCap ckPtr s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropGlueFacts.seq_clean (mid := entry + bv% (40)) (P_mid :=
    (chainOuterHeadersAt a g ckCap ckPtr ∗
      vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + bv% (60)) (P_mid :=
      (chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (84)) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDealloc]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem drop_chain_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropChainName + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + 100#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A cur pin mk)) ?_
  refine DropGlueFacts.seq_clean (mid := entry + bv% (132)) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDealloc A pin.mac ∗ vecPinDealloc A pin.iv ∗ vecPinDealloc A pin.seed) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    ?_ ?_
  · dsimp only [mkHeadersAt, vecPinDealloc]
    by_cases hcap : (pin.cipher.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + bv% (152)) (P_mid :=
      (mkHeadersAt cur pin ∗ vecPinDealloc A pin.iv ∗ vecPinDealloc A pin.seed) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      ?_ ?_
    · dsimp only [mkHeadersAt, vecPinDealloc]
      by_cases hcap : (pin.mac.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + bv% (172)) (P_mid :=
        (mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        ?_ ?_
      · dsimp only [mkHeadersAt, vecPinDealloc]
        by_cases hcap : (pin.iv.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (100)) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          dsimp only [mkHeadersAt, vecPinDealloc]
          by_cases hcap : (pin.seed.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · wp_steps
            wp_apply
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_chain_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropChainName + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropChainName + 196#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_chain_body hdealloc s0 fsp v ptr hfsp_align
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]" =
    entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine DropGlueFacts.seq_clean (mid := entry + bv% (100))
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
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

theorem drop_proto_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainName)
      (dropProtoChainSpec A) := by
  simp only [dropProtoChainSpec]
  have hdealloc_raw := hA.dealloc_ok_at dropChainName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")]; simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have houter := drop_chain_outer (b := b) (ext := ext) hdealloc_raw
  have hloop := drop_chain_loop (b := b) (ext := ext) hdealloc_raw
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]") (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]")) 252
  dsimp only [tripleRatchetProgAtExt, dropChainName, BitVec.ofNat_eq_ofNat] at hdealloc houter hloop ⊢
  generalize_entry (libsignalSessionCode.rebase b
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
  nth_rw 1 [show dropChainStack = dropVecMessageKeyStack from rfl]
  nth_rw 1 [stackAt_dropVecMessageKey_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoChainAt_entails_dealloc A (s0.readReg64 (Reg.gpr 0#5)) g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  refine DropGlueFacts.seq_clean (mid := entry + bv% (16))
    (P_mid :=
      (chainOuterHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g ckCap ckPtr ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
        (g.keys.zip c.messageKeys) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · wp_steps
    refine DropGlueFacts.align_pre (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + bv% (84))
      (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
        A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · dsimp only [chainOuterHeadersAt]
      simp only [sepConj_assoc]
      refine SepWP.mono
        (houter s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align g ckCap ckPtr s1
          (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq
      ac_rfl
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A 104 8 (messageKeyAt A)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      refine DropGlueFacts.seq_clean (mid := entry + bv% (196))
        (P_mid :=
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104)) ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x20 = g.mkPtr)
        ?_ ?_
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
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
              (arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
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
              ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩
              hx19_2 rfl rfl rfl) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          apply Entails.of_eq
          ac_rfl
      · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_cap0_weaken (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr A.pool s0.sp _ _ _ _ _ _) ?_
          wp_done
        · wp_steps
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weaken (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ _ s0.sp _ _ _ _ _ _) ?_
          wp_apply
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
          wp_done

theorem drop_proto_chain_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropChainName)
      (dropProtoChainSpec A) :=
  drop_proto_chain_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

theorem drop_proto_chain_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropChainName)
      (dropProtoChainSpec A) :=
  subroutine_ok_kit_of_trTrap (drop_proto_chain_ok_trap hA)

theorem drop_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainName)
      (dropChainSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    (drop_proto_chain_ok_ext hA).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hpre
  simp only [dropChainSpec, dropProtoChainSpec]
  exact sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A x.gc x.a))

theorem drop_chain_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropChainName)
      (dropChainSpec A) :=
  drop_chain_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

theorem drop_chain_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropChainName)
      (dropChainSpec A) :=
  subroutine_ok_kit_of_trTrap (drop_chain_ok_trap hA)

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Block `142`) -/

open Arm64.Obj CryptoVerification

private theorem drop_chain_placed_outer [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_142).rebase (blkPl_142).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp a : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (blkPl_142).base + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP ((blkPC_142).rebase (blkPl_142).base H)
        ((blkPl_142).base + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [rustDeallocSpec] at hdealloc
  intro g ckCap ckPtr s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 40#64) (P_mid :=
    (chainOuterHeadersAt a g ckCap ckPtr ∗
      vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 60#64) (P_mid :=
      (chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_142).rebase (blkPl_142).base H) ((blkPl_142).base + 84#64) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDealloc]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem drop_chain_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_142).rebase (blkPl_142).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_142).base + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_142).rebase (blkPl_142).base H)
        ((blkPl_142).base + 100#64)
        s
        (messageKeyAt A (pin, mk) cur ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A cur pin mk)) ?_
  refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 132#64) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDealloc A pin.mac ∗ vecPinDealloc A pin.iv ∗ vecPinDealloc A pin.seed) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    ?_ ?_
  · dsimp only [mkHeadersAt, vecPinDealloc]
    by_cases hcap : (pin.cipher.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 152#64) (P_mid :=
      (mkHeadersAt cur pin ∗ vecPinDealloc A pin.iv ∗ vecPinDealloc A pin.seed) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      ?_ ?_
    · dsimp only [mkHeadersAt, vecPinDealloc]
      by_cases hcap : (pin.mac.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 172#64) (P_mid :=
        (mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        ?_ ?_
      · dsimp only [mkHeadersAt, vecPinDealloc]
        by_cases hcap : (pin.iv.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_142).rebase (blkPl_142).base H) ((blkPl_142).base + 100#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          dsimp only [mkHeadersAt, vecPinDealloc]
          by_cases hcap : (pin.seed.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_chain_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_142).rebase (blkPl_142).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_142).base + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_142).rebase (blkPl_142).base H)
        ((blkPl_142).base + 196#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_chain_placed_body hdealloc s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A (pin, mk) cur ∗ arrayAt (messageKeyAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 100#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps; wp_done
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
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4 rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

/-- Block `142` (`core::ptr::drop_glue::<...::Chain> [local#1]`)
meets `dropProtoChainSpec A` under `[LibsignalPlacement]`, given `subroutine_ok` for `__rust_dealloc`. -/
theorem drop_proto_chain_placed_ok_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_142).rebase (blkPl_142).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_142).rebase (blkPl_142).base H) (blkPl_142).base
      (dropProtoChainSpec A) := by
  simp only [dropProtoChainSpec]
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have houter := drop_chain_placed_outer hdealloc_raw
  have hloop := drop_chain_placed_loop hdealloc_raw
  wp_init x s0
  obtain ⟨a, g, c⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [show dropChainStack = dropVecMessageKeyStack from rfl]
  nth_rw 1 [stackAt_dropVecMessageKey_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoChainAt_entails_dealloc A (s0.readReg64 (Reg.gpr 0#5)) g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 16#64)
    (P_mid :=
      (chainOuterHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g ckCap ckPtr ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
        (g.keys.zip c.messageKeys) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · wp_steps
    refine DropGlueFacts.align_pre (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 84#64)
      (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
        A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · dsimp only [chainOuterHeadersAt]
      simp only [sepConj_assoc]
      refine SepWP.mono
        (houter s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align g ckCap ckPtr s1
          (vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq; ac_rfl
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A 104 8 (messageKeyAt A)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      refine DropGlueFacts.seq_clean (mid := (blkPl_142).base + 196#64)
        (P_mid :=
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104)) ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x20 = g.mkPtr)
        ?_ ?_
      · cases mks with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          wp_steps; wp_done
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
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
              (arrayAt (messageKeyAt A) 104 g.mkPtr (hd :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
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
              ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩
              hx19_2 rfl rfl rfl) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          apply Entails.of_eq; ac_rfl
      · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_cap0_weaken (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr A.pool s0.sp _ _ _ _ _ _) ?_
          wp_done
        · wp_steps
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weaken (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ _ s0.sp _ _ _ _ _ _) ?_
          wp_apply
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
          wp_done

/-- Block `142` (`core::ptr::drop_glue::<...::Chain> [local#1]`)
meets `dropProtoChainSpec A` under `[LibsignalPlacement]`. -/
theorem drop_proto_chain_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_142).rebase (blkPl_142).base H) (blkPl_142).base
      (dropProtoChainSpec A) :=
  drop_proto_chain_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

/-- Block `142` (`core::ptr::drop_glue::<...::Chain> [local#1]`)
meets `dropChainSpec A` under `[LibsignalPlacement]`, given `subroutine_ok` for `__rust_dealloc`. -/
theorem drop_chain_placed_ok_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_142).rebase (blkPl_142).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_142).rebase (blkPl_142).base H) (blkPl_142).base
      (dropChainSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    (drop_proto_chain_placed_ok_of_dealloc hdealloc_raw).mono_outcome x R s0 hpc hrun ?_ hsp
      fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hpre
  simp only [dropChainSpec, dropProtoChainSpec]
  exact sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A x.gc x.a))

/-- Block `142` (`core::ptr::drop_glue::<...::Chain> [local#1]`)
meets `dropChainSpec A` under `[LibsignalPlacement]`. -/
theorem drop_chain_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_142).rebase (blkPl_142).base H) (blkPl_142).base
      (dropChainSpec A) :=
  drop_chain_placed_ok_of_dealloc (ls_hook_ok_rustDealloc h_dealloc)

end CryptoVerification.LibsignalTripleRatchet.Getters
