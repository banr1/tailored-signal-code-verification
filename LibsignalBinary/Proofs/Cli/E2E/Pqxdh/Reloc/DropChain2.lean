/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.DropGlueChainL4
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WPp

/-!
# `drop_glue::<Chain>` Proof on `tripleRatchetProgAt`

Verifies `core::ptr::drop_glue::<session_structure::Chain>` against `dropProtoChainSpec A`
and `dropChainSpec A` on `tripleRatchetProgAt` and `trTrapProgAt`.
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

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]"

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

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

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_outer_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp a : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [trTrapProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro g ckCap ckPtr s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine DropGlueFacts.seq_clean (mid := entry + 40#64) (P_mid :=
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
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 60#64) (P_mid :=
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
        wp_call hdealloc (g.priv.ptr, g.priv.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (trTrapExterns C abs))) (entry + 84#64) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗ A.pool ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDealloc]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (ckPtr, ckCap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_outer {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp a : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDealloc A ckCap ckPtr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
            Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [tripleRatchetProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (tripleRatchetExterns C ctl abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro g ckCap ckPtr s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine DropGlueFacts.seq_clean (mid := entry + 40#64) (P_mid :=
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
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 60#64) (P_mid :=
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
        wp_call hdealloc (g.priv.ptr, g.priv.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (tripleRatchetExterns C ctl abs))) (entry + 84#64) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗ A.pool ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDealloc]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (ckPtr, ckCap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_body_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 100#64)
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
  dsimp only [trTrapProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A cur pin mk)) ?_
  refine DropGlueFacts.seq_clean (mid := entry + 132#64) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDealloc A pin.mac ∗ vecPinDealloc A pin.iv ∗
      vecPinDealloc A pin.seed) ∗
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
      wp_call hdealloc (pin.cipher.ptr, pin.cipher.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1,
    hx20_1, hx21_1, hx22_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 152#64) (P_mid :=
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
        wp_call hdealloc (pin.mac.ptr, pin.mac.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 172#64) (P_mid :=
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
          wp_call hdealloc (pin.iv.ptr, pin.iv.cap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩,
        hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
          (trTrapExterns C abs))) (entry + 100#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗ A.pool ∗
              stackAt fsp allocHookStack ∗ Frame)
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
            wp_call hdealloc (pin.seed.ptr, pin.seed.cap.toNat, 1)
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_body {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 100#64)
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
  dsimp only [tripleRatchetProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (tripleRatchetExterns C ctl abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A cur pin mk)) ?_
  refine DropGlueFacts.seq_clean (mid := entry + 132#64) (P_mid :=
    (mkHeadersAt cur pin ∗ vecPinDealloc A pin.mac ∗ vecPinDealloc A pin.iv ∗
      vecPinDealloc A pin.seed) ∗
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
      wp_call hdealloc (pin.cipher.ptr, pin.cipher.cap.toNat, 1)
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1,
    hx20_1, hx21_1, hx22_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 152#64) (P_mid :=
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
        wp_call hdealloc (pin.mac.ptr, pin.mac.cap.toNat, 1)
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + 172#64) (P_mid :=
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
          wp_call hdealloc (pin.iv.ptr, pin.iv.cap.toNat, 1)
          refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩,
        hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
          (tripleRatchetExterns C ctl abs))) (entry + 100#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A pin.seed) ∗ A.pool ∗
              stackAt fsp allocHookStack ∗ Frame)
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
            wp_call hdealloc (pin.seed.ptr, pin.seed.cap.toNat, 1)
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_loop_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 196#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_body_trap hdealloc s0 fsp v ptr hfsp_align
  dsimp only [trTrapProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
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
    refine DropGlueFacts.seq_clean (mid := entry + 100#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4,
      hx20_4, hx21_4, hx22_4⟩
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
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩
          hx19_4 hx20_4
          rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit,
        ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

private theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_loop {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 196#64)
        s
        (arrayAt (messageKeyAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_body hdealloc s0 fsp v ptr hfsp_align
  dsimp only [tripleRatchetProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (tripleRatchetExterns C ctl abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
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
    refine DropGlueFacts.seq_clean (mid := entry + 100#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4,
      hx20_4, hx21_4, hx22_4⟩
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
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩
          hx19_4 hx20_4
          rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit,
        ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpec A) := by
  simp only [dropProtoChainSpec]
  have hdealloc_raw := (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA).dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name
    (num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")]; simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have houter := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_outer_trap (b := b) (C := C) hdealloc_raw
  have hloop := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_loop_trap (b := b) (C := C) hdealloc_raw
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  dsimp only [trTrapProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at hdealloc houter hloop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
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
  refine DropGlueFacts.seq_clean (mid := entry + 16#64)
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
    refine DropGlueFacts.align_pre
      (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21,
            Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 84#64)
      (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A 104 8 (messageKeyAt A)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      refine DropGlueFacts.seq_clean (mid := entry + 196#64)
        (P_mid :=
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104))
               ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
                   memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                     ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
                     memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                       ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                  (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
            ac_rfl
          rw [hpre_eq]
          refine SepWP.mono
            (hloop s0 (s0.sp - 48#64) g.mkPtr (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
              (hd :: tl) g.mkPtr _ _
              (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
              ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩
              hx19_2 rfl rfl rfl) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          apply Entails.of_eq
          ac_rfl
      · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A (s0.readReg64
            (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_cap0_weaken (s0.readReg64
              (Reg.gpr 0#5)) g.mkCap g.mkPtr A.pool s0.sp _ _ _ _ _ _) ?_
          wp_done
        · wp_steps
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weaken (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ _ s0.sp _ _ _ _ _ _) ?_
          wp_call hdealloc (g.mkPtr, g.mkCap.toNat * 104, 8)
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
          wp_done

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpec A) := by
  simp only [dropProtoChainSpec]
  have hdealloc_raw := DropGlueFacts.dealloc_ok_at (b := b) (C := C) (ctl := ctl)
    hA (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]"))) (by decide)
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have houter := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_outer (b := b) (C := C) (ctl := ctl) hdealloc_raw
  have hloop := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_loop (b := b) (C := C) (ctl := ctl) hdealloc_raw
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  dsimp only [tripleRatchetProgAt, CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name, BitVec.ofNat_eq_ofNat] at hdealloc houter hloop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (tripleRatchetExterns C ctl abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
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
  -- Prologue (+0x000 -> +0x010 = 16)
  refine DropGlueFacts.seq_clean (mid := entry + 16#64)
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
    refine DropGlueFacts.align_pre
      (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21,
            Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    -- Outer fields (+0x010 -> +0x054 = 84)
    refine DropGlueFacts.seq_clean (mid := entry + 84#64)
      (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A 104 8 (messageKeyAt A)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      -- Loop over message_keys (+0x054 -> +0x0c4 = 196)
      refine DropGlueFacts.seq_clean (mid := entry + 196#64)
        (P_mid :=
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104))
               ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
                   memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                     ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
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
                     memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                       ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                  (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
            ac_rfl
          rw [hpre_eq]
          refine SepWP.mono
            (hloop s0 (s0.sp - 48#64) g.mkPtr (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
              (hd :: tl) g.mkPtr _ _
              (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
              ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩
              hx19_2 rfl rfl rfl) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          apply Entails.of_eq
          ac_rfl
      · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A (s0.readReg64
            (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_cap0_weaken (s0.readReg64
              (Reg.gpr 0#5)) g.mkCap g.mkPtr A.pool s0.sp _ _ _ _ _ _) ?_
          wp_done
        · wp_steps
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weaken (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ _ s0.sp _ _ _ _ _ _) ?_
          wp_call hdealloc (g.mkPtr, g.mkCap.toNat * 104, 8)
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
          wp_done

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok_trap hA).mono_outcome
    x R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hpre
  simp only [dropChainSpec, dropProtoChainSpec]
  exact sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A x.gc x.a))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok hA).mono_outcome
    x R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hpre
  simp only [dropChainSpec, dropProtoChainSpec]
  exact sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A x.gc x.a))

end CryptoVerification.LibsignalTripleRatchet.Getters
